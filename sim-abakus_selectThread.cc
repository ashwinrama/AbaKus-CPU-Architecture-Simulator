/* sim-abakus.c - Microarchitecture Implementation */

/* AbaKus Modular Simulator: Aswin Ramachandran and Louis G. Johnson, Oklahoma State University, 2007 */
/* The architecture functional design is described in this file.  Each stage is 
 * distinguished through port interfaces that is used to exchange data between
 * the pipeline stages.
 * The back-end design i.e. the functional execution and ISA description  of the simulations
 * reuses modules from  SimpleScalar(TM) Tool Suite
 * Copyright (C) 1994-2003 by Todd M. Austin, Ph.D. and SimpleScalar, LLC.
 *  
 */

#include<iostream>
#include <list>
#include <algorithm>
#include <vector>
#include <stdlib.h>
#include "sim-init.h"
#include "sim-ExtPrint.h"
#include "bpred.h"
//#include "sc_datatypes.h"
#ifndef DATATYPE
#define DATATYPE 
#include "sc_datatypes.h"
#endif
using namespace std;

list <unsigned int>  activeList, activeValidList, threadBusyList, newThreadList;
list<unsigned int>::iterator temphdPtr;
//const unsigned int THREAD_LEVEL = 4;
const unsigned int CONF_MAX = 16; //Maximum Confidence Estimate of a Thread
const unsigned int MAX_THREADS = 16; //Maximum Confidence Estimate of a Thread

//static list<int> activeThreads1;
struct ReorderBuffer {

    bool busy;
    bool completed; 
    bool misspeculated; //0: Correct; 1: Wrong 
    bool followBr;
    bool issued;
    bool finished;
    bool inOrder;
    bool exception;  //Exception Instruction
    bool lD;  // Indicates its a load instruction; Issued only after the store instruction
    bool alu, br, mult, readLO, readHI;  // Set on an alu instruction or on a branch instruction

    unsigned int sw_reoID; // Stores the Store Buffer ID for a Store Instruction
    unsigned int ld_reoID; // Stores the Store Buffer ID for a Store Instruction
    unsigned int inst_a;
    unsigned int inst_b;
   // unsigned long long br_cycle;
    struct bpred_update_t dir_update;     /* bpred direction update info */

    bool wakeUp; // Set When Ready to be moved into the ReadyQ.
    unsigned int regs_PC;
    unsigned int thrdID : THREAD_LEVEL;
    unsigned int thrdBitPtr;
    bool thrdIDValid;
    unsigned int pred_PC;
    unsigned int ld_pred_addr;
    unsigned int stack_recover_idx;
    unsigned int regs_NPC;
    unsigned int regs_TPC;

    unsigned int rd_old;
    unsigned int rd_new;
    unsigned int rd;
    unsigned int rs;
    unsigned int rt;
} reoBuffer [ REORDER_WIDTH ];

ReorderBuffer* reoBufferPtr = NULL;

struct ThrdW {
   unsigned int BITS : (THREAD_LEVEL);// Thread Width: 2^(Thread_Bits - 1) 
   unsigned int hdPtr; //First Position of the BITS
   unsigned int tailPtr; // Indicates the Last Position of the BITS
   unsigned int cmpPtr; // Indicates the position of the last completed branch
}thrdBits;

//------ISSUE TYPE Queues-------
struct Func_ISSUE_Q {
        //Func_Other issQ [REORDER_WIDTH]; // Size of the ISSUE Queue kept at Inf.
        unsigned int issQ [REORDER_WIDTH]; // Size of the ISSUE Queue kept at Inf.
        bool valid [REORDER_WIDTH];
        bool discard [ REORDER_WIDTH ];
        unsigned int thrdID[REORDER_WIDTH];
        unsigned int regsPC[REORDER_WIDTH];
        unsigned int rd_new[REORDER_WIDTH];
        signed int hdPtr;
        signed int tailPtr;
} alu_insn, mul_insn, ls_insn, br_insn, ot_insn; // Functional Types of ISSUE Queue

Func_ISSUE_Q* issue_ptr = NULL;

//------ALU FU Definition-----------
struct Func_ALU_Q {
        Func_General aluQ [ALU_LAT];
        signed int hdPtr;
        signed int tailPtr;
} alu_unit[ ALU_WIDTH];
Func_General* alu_ptr = NULL;

//------Load FU Definition-----------
struct Func_LD_Q {
        Func_General ldQ [LD_LAT];
        signed int hdPtr;
        signed int tailPtr;
} load_unit[ LD_WIDTH ];
Func_General* ld_ptr = NULL;

//------Branch FU Definition-----------
struct Func_BR_Q {
        Func_General brQ [BR_LAT];
        signed int hdPtr;
        signed int tailPtr;
} branch_unit[BR_WIDTH];
Func_General* br_ptr = NULL;

//------Mulitply FU Definition-----------
struct Func_MUL_Q {
        Func_General mulQ [MUL_LAT];
        signed int hdPtr;
        signed int tailPtr;
} mul_unit [MUL_WIDTH];
Func_General* mul_ptr = NULL;

//--------Other Definition----------
struct Func_OT_Q {
        Func_General otQ [OT_LAT];
        signed int hdPtr;
        signed int tailPtr;
} other_unit[ OT_WIDTH];
Func_General* other_ptr = NULL;
//-------Active Thread Queue-------
/*struct activeThread_Q {
        unsigned int thrdID[THREAD_WIDTH];
        signed int hdPtr;
        signed int tailPtr;
} activeThreads;
*/
bool threadUpdate = 1;
unsigned thrdActive = 0;
//branch_unit.tailPtr = BR_LAT;                                                                                                                                                                                                               
//--------------------------------
struct WRBackBus {
    unsigned int reoID;
    bool spec;
    unsigned int rd_new;
    signed int rt_data;
    signed int rs_data;
    unsigned inst_a, inst_b;
    unsigned regsPC;
} wb_bus[ WB_WIDTH ];


//------Load Address Prediction Buffer-----------
const unsigned int  MEM_BUF_SIZE = 256;
struct MemAddrBuffer {
      bool valid;
      unsigned int mem_addr;
      unsigned int mem_PC;
} memPred_buffer[ MEM_BUF_SIZE  ];

int mem_pred_hdPtr = 0; // Hd Ptr Unfinished Store Buffer
int mem_pred_tPtr = 0; // tail Ptr Unfinished Store Buffer

//------Unfinished SW Buffer-----------
/*struct UnfinishedSWBuffer {
      bool valid;
      unsigned int sw_addr;
      unsigned int reoID;   //Reorder Buffer ID
} unfini_sw_buffer[ REORDER_WIDTH ];

int unfini_sw_hdPtr = 0; // Hd Ptr Unfinished Store Buffer
int unfini_sw_tPtr = 0; // tail Ptr Unfinished Store Buffer
*/
//------Store Buffer-----------
struct StoreBuffer {
      bool valid;
      bool sw_dataValid;
      bool is_sw;  // Is a store word instruction ?
      unsigned long long sw_uniqueID; // ID of the store buffer from which data was forwarded (Exculsive right to set mem violation bit)
      unsigned int sw_addr;
      unsigned int pred_sw_addr;
      unsigned int reoID;   //Reorder Buffer ID
      unsigned int thrdID;   // Thread Buffer ID
      unsigned int thrdBitPtr;   // Thread Buffer ID
      signed int sw_data;
} sw_buffer[ REORDER_WIDTH ];

int sw_hdPtr = 0; // Hd Ptr Store Buffer
int sw_tPtr = 0; // tail Ptr Store Buffer
//------Load Finish Buffer-----------
struct LdFinishBuffer {
      bool mem_violation; 
      bool mem_recover; 
      bool match_exists; //Reorder Buffer ID of the fwded store instruction
      unsigned int sw_pc; //mem violated sw pc
      unsigned long long sw_uniqueID; // ID of the store buffer from which data was forwarded (Exculsive right to set mem violation bit)
      bool valid;
      bool ld_fwd;
      bool is_lw;
      bool is_lh;
      bool is_lb;
      bool is_signed;
      unsigned int ld_addr;
      signed int ld_data;
      unsigned int reoID; //Reorder Buffer ID
      unsigned int thrdID; //Thread ID
//      signed int ld_data;
} ld_buffer[ REORDER_WIDTH ];

int ld_hdPtr = 0; // Hd Ptr Store Buffer
int ld_tPtr = 0; // tail Ptr Store Buffer

// Thread PC List
struct Func_PC_Q {
        bool busy[ THREAD_WIDTH ]; //To indicate whether it is free or not 
        bool valid[ THREAD_WIDTH ]; //To indicate whether to fetch or not (set after br. is resolved)
        bool continueFetch[ THREAD_WIDTH ]; //To indicate whether to fetch or not (set after br. is resolved)
        bool completeBit;
        unsigned int thrdPC [ THREAD_WIDTH ];
        unsigned int thrdID [ THREAD_WIDTH ] ;
        unsigned int thrdParentID [ THREAD_WIDTH ] ; // Used only while Thread Wraps Around
        unsigned int thrdParentLevel [ THREAD_WIDTH ] ; // Used only while Thread Wraps Around
        unsigned int thrdSiblingID [ THREAD_WIDTH ] ; // Used only while Thread Wraps Around
        unsigned int bitPtr [ THREAD_WIDTH ]; // Indicates the Thread Level
        unsigned int fetchCount [ THREAD_WIDTH ]; // No. of insns fetched from this thread in a cycle
        signed int threadCount [ THREAD_WIDTH ]; // Total no. of insns dispatched from this thread.
        float pathConfidence [ THREAD_WIDTH ];
        float normConfidence [ THREAD_WIDTH ];
} thrdPC_Q;

struct Func_PC_Entry {
        unsigned int thrdID; // Indicates the Thread Level
        unsigned int normConfidence;
} thrdEntry;
vector<Func_PC_Entry> priorityList;
vector<Func_PC_Entry>:: iterator itPrty;

struct sortByNorm
{
    bool operator()(const Func_PC_Entry& e1, const Func_PC_Entry& e2)
    { return e2.normConfidence < e1.normConfidence; }
};
/*  Complete MASK */
unsigned int cmpMASK = 0;
/* Parent ThrdID; Parent ThrdLevel*/
/* Even & Odd Counters */
//unsigned int evenThrdCnt = 2;
//unsigned int oddThrdCnt = 3;


unsigned int hPriorityQ [ REORDER_WIDTH ];
unsigned int lPriorityQ [ REORDER_WIDTH ];
int hPQ_hdPtr = 0;
int lPQ_hdPtr = 0;
int hPQ_tailPtr = 0;
int lPQ_tailPtr = 0;

struct IssueReadyQueue {
    unsigned int slotID [ REORDER_WIDTH ];   // Issue Read Queue maintains the list of Slot Ids Ready to be Issued.
    unsigned int thrdID [ REORDER_WIDTH ];   // Issue Read Queue maintains the list of Slot Ids Ready to be Issued.
    bool ldFLAG, excep;
    unsigned int swID;
    unsigned int hdPtr;
    unsigned int tailPtr;
    bool valid [ REORDER_WIDTH ];
    bool discard [ REORDER_WIDTH ];
} issReadyQ;

struct WakeUpTable {
    unsigned int slotID[ REORDER_WIDTH] ;   // Issue Read Queue maintains the list of Slot Ids Ready to be Issued.
    unsigned int regs_PC[ REORDER_WIDTH] ;   // Issue Read Queue maintains the list of Slot Ids Ready to be Issued.
    unsigned int rd_new[ REORDER_WIDTH] ;   // Issue Read Queue maintains the list of Slot Ids Ready to be Issued.
    unsigned int thrdID [ REORDER_WIDTH] ;   // Issue Read Queue maintains the list of Slot Ids Ready to be Issued.
    unsigned int slotLength; // No. of Dependent IW Slot ID
    bool valid;  // To indicate that the entry is valid
} wakeUpTbl[ REORDER_WIDTH ]; 
                                                                                                                                                                                                               
WakeUpTable* wakeUpPtr = NULL;
 extern simulationDataStruct simDataA, simDataB, *cur_data_ptr, *next_data_ptr; //Fetch 
 extern unsigned long long cycle_count;
 bool regs_busyBits[ MD_NUM_IREGS + MD_XREGS ];

//----------simulation statistics/counters and variables--------
 unsigned long long max_exe_insn = 6000000000UL; //Max. Instr. to execute

 bool max_prn_insn_1B = 0; //Max. Instr. to execute
 bool max_prn_insn_2B = 0; //Max. Instr. to execute
 bool max_prn_insn_3B = 0; //Max. Instr. to execute
 bool max_prn_insn_4B = 0; //Max. Instr. to execute
 bool max_prn_insn_5B = 0; //Max. Instr. to execute
 bool max_prn_insn_6B = 0; //Max. Instr. to execute
                                                                                                                                                                 
 const unsigned long long max_exe_insn_1B = 10000000UL; //Max. Instr. to execute
 const unsigned long long max_exe_insn_2B = 20000000UL; //Max. Instr. to execute
 const unsigned long long max_exe_insn_3B = 30000000UL; //Max. Instr. to execute
 const unsigned long long max_exe_insn_4B = 40000000UL; //Max. Instr. to execute
 const unsigned long long max_exe_insn_5B = 50000000UL; //Max. Instr. to execute
 const unsigned long long max_exe_insn_6B = 80432321UL; //Max. Instr. to execute

 unsigned long long sw_uniqueID = 0UL; //SW Unique ID
 unsigned long long brDirJmp = 0;
 unsigned long long brInDirJmp = 0;
 unsigned long long brDirCall = 0;
 unsigned long long brCondJmp = 0;
 unsigned long long brUnCondInDirJmp = 0;
 unsigned long long mispredictBrCntr = 0;
 unsigned long long thrdLevelBusyCntr = 0;
 unsigned long long thrdMaxLevelCntr = 0;
 unsigned long long newLevelBusyCntr = 0;

 unsigned long long ldFwdCntr = 0;
 unsigned long long ldRecvrCntr = 0;
 unsigned long long ldReplaceCntr = 0;
 unsigned long long brMisPredCntr = 0;
 unsigned long long brRecvrCntr = 0;

 unsigned long long sb_mem_recvr = 0;
 unsigned long long lb_mem_recvr = 0;
 unsigned long long lw_mis_recvr = 0;

 unsigned long long reoStallCntr = 0;
 unsigned long long issQStallCntr = 0;
 unsigned long long aluStallCntr = 0;
 unsigned long long brStallCntr = 0;
 unsigned long long ldStallCntr = 0;
 unsigned long long mulStallCntr = 0;
 unsigned long long otStallCntr = 0;

 unsigned long long aluWBStallCntr = 0;
 unsigned long long mulWBStallCntr = 0;
 unsigned long long brWBStallCntr = 0;
 unsigned long long ldWBStallCntr = 0;
 unsigned long long otWBStallCntr = 0;

 unsigned long long aluFUStallCntr = 0;
 unsigned long long mulFUStallCntr = 0;
 unsigned long long brFUStallCntr = 0;
 unsigned long long ldFUStallCntr = 0;
 unsigned long long otFUStallCntr = 0;

 unsigned long long confidenceCntr[CONF_MAX] ;
 unsigned long long threadCntr[THREAD_WIDTH] ;
 unsigned long long threadDiscard[10000] ;
 unsigned long long sim_br_cycle[1000] ;

 unsigned int alu_WbCntr = 0;  // No. of Alu that access the Write Back Bus
 unsigned int mul_WbCntr = 0;  // No. of Alu that access the Write Back Bus
 unsigned int  ot_WbCntr = 0; // No .of other func. units that access the write back bus
 unsigned int tailCntr = 0;
 long long excepCntr = 0;
// unsigned int j, k;
 unsigned int unResolvedCntr = 0; 
 unsigned int mulIssueCntr = 0; 
 unsigned int aluIssCntr = 0; 
 unsigned int brIssCntr = 0; 
 unsigned int ldIssCntr = 0; 
 unsigned int otherIssCntr = 0; 
 unsigned int  resetPtr;
 signed int i,j,k;  //Iteration variables
//--------Round Robin Issue and Write-Back Pointers------------------
 unsigned int alu_rr_ptr = 0; // Round Robin ALU Issue Pointer
 unsigned int mul_rr_ptr = 0; // Round Robin ALU Issue Pointer
 unsigned int br_rr_ptr = 0; // Round Robin ALU Issue Pointer
 unsigned int ld_rr_ptr = 0; // Round Robin ALU Issue Pointer
 unsigned int ot_rr_ptr = 0; // Round Robin ALU Issue Pointer
 unsigned int oper1_Slot, oper2_Slot;
 unsigned int mul_width, alu_width, br_width, ld_width, other_width;
 unsigned int alu_cntr = 0;
 unsigned int mul_cntr = 0;
 unsigned int  ot_cntr = 0;
 unsigned int  fu_cntr = 0;

 unsigned int   alu_IssFu = 0; // round robin issue
 unsigned int   mul_IssFu = 0;
 unsigned int    ot_IssFu = 0;

 unsigned int wbPtr = 0; // Round Robin Pointer
 unsigned int alu_wb_ptr = 0;  //Alu Round Robin Poiner
 unsigned int mul_wb_ptr = 0;  //mul Round Robin Poiner
 unsigned int ot_wb_ptr = 0;  //Other Round Robin Poiner
 unsigned int headPtr = 0;  //ReOrder Buffer head Pointer
 unsigned int tailPtr = 0;  //ReOrder Buffer tail Pointer
 unsigned int ready = 0; // WakeupTbl Indexing
 unsigned int issID, wdTimer1 = 0; //Issue  watch dot timer ( can be disabled)
// static int issuePtr = 0;
 unsigned int wdTimer = 0; //complete watch dog timer
 unsigned finiID = 0;
 int prevFreeReg;
 //unsigned int prevWB; //finish stage
 unsigned int freeCnt, issCnt; // Dispatch
 unsigned int maxThrdLevel = 0;
//------Fetch Variables----------------
  //-bool readyCheck = 0;
  bool firstSpawn = 0;
  bool mulCheck = 0;
  bool inOrder;
  bool excep;
  bool lD;
  bool alu;
  bool mult;
  bool readLO, readHI;
  bool condBr;
  bool br;
  bool fetchBlock;
  bool stall=FALSE;
  unsigned int fetchPC, fetchNPC;
  md_inst_t inst;
//-------Decode variables--------------
   bool rs_allocate,rt_allocate, rd_allocate;   
   int freeRegs[S_WIDTH];
   int num = 0;
//-------Misc Variables-------
   int curPtr = 0; 
   int cmpFetchPC = 0, cmpFetchNPC = 0;
   int excepMSK = 0;
   bool end_simulation = 0;
   bool unknownTarget = 0;
   bool fu_stall = 0;  // finish stage 
   bool reoStallEnable = 0;  // Dispatch stage 
   unsigned int regs_R2 = 0;
//---------------------------------------------------------------
//Rename Register Table to Simulate the Hardware Associative Memory of Register Cache
/* struct RRegFile {
    unsigned int ptr[MD_NUM_IREGS + 1];  // Rename Register Pointer File & LO, HI Register
    unsigned int bitPtr[MD_NUM_IREGS + 1];  // Rename Register Pointer File & LO, HI Register
    bool valid[MD_NUM_IREGS + 1];
 } rRegPtr[THREAD_LEVEL + 1][THREAD_WIDTH]; //Default Level +1
*/
 struct RRegFile1 {
    unsigned int ptr[THREAD_LEVEL + 1][MD_NUM_IREGS + 1];  // Rename Register Pointer File & LO, HI Register
    unsigned int bitPtr[THREAD_LEVEL + 1][MD_NUM_IREGS + 1];  // Rename Register Pointer File & LO, HI Register
    bool valid[THREAD_LEVEL + 1][MD_NUM_IREGS + 1];
    unsigned int thrdID;  // Rename Register Pointer File & LO, HI Register
 } rRegPtr1; //Default Level +1

 list<RRegFile1> rRegVector;
 list<RRegFile1>::iterator reg_ii; 

//unsigned int regCacheSize = 0; // MAX. Limit of Reg Cache = REORDER_WIDTH
//-------------------------------------------------------------
/*struct thrdRRegFile {
    unsigned int thrdID;
    unsigned int ptr;  // Rename Register Pointer File & LO, HI Register
    bool valid;
 } thrdRegPtr [REORDER_WIDTH];
*/
  unsigned int aRegPtr[MD_NUM_IREGS + 1]; // Architected Register Pointer File & LO, HI Register

//-------------------------------------------------------------
  #define VALID(N)		(regs_cp.valid_R[N])
  #define BUSY(N)		        (regs_cp.busy_R[N])
  #define DEBUG		(1)
/*
  reorder_busy* REOBUSY = &next_data_ptr->reoBusyPORTS;
  reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;
  reg_RR_bus* OUTPUT_RF = &next_data_ptr->regfilePORTS;
  reg_bus* OUTPUT_ARP = &next_data_ptr->arpPORTS;
  reg_RRP_bus* OUTPUT_RRP = &next_data_ptr->rrpPORTS;
 */ 
//-----------GENERAL Purpose Functions for Debugging---------------//
void print_regs ()
/*Prints the ARF, ARP and RRP contents*/
{
   for (int i=0; (unsigned) i<(MD_NUM_IREGS + 1); i++)
  {
    fprintf(stderr,"ARP[%d] = %d\n", i, aRegPtr[i]);
  }

/*for (int k = 0; (unsigned) k < (THREAD_LEVEL+1); k++)
{ 
  for (int j = 0; (unsigned) j < THREAD_WIDTH; j++)
  {
    for (int i=0; (unsigned) i<(MD_NUM_IREGS + 1); i++)
    {
     fprintf(stderr," RRP[%d][%d] = %d \t Valid = %d bitPtr = %d \n",k, j ,rRegPtr[k][j].ptr[i], rRegPtr[k][j].valid[i], rRegPtr[k][j].bitPtr[i]);
    }
  }
}
*/
   for (int i=0; (unsigned) i<(MD_NUM_IREGS + MD_XREGS); i++)
  {
  //  fprintf(stderr,"ARP[%d] = %d\t RRP = %d \t Valid = %d \t", i, aRegPtr[i],rRegPtr.ptr[i], rRegPtr.valid[i]);
    //fprintf(stderr,"ARF[%d] = %d \t ARF2[%d] = %d \t Valid = %d  Busy = %d Slot = %d \n", i, regs_cp.regs_R[i],i, regs_cp.regs_R2[i], regs_cp.valid_R[i] ,regs_busyBits[i], regs_cp.instWindowSlot[i]   );
    fprintf(stderr,"ARF[%d] = %d \t ARF2[%d] = %d \t Valid = %d  %d \n", i, regs_cp.regs_R[i],i, regs_cp.regs_R2[i], regs_cp.valid_R[i], regs_busyBits[i] );
  }
}

inline void  print_regval()
{
   for (int i=0; (unsigned) i<(MD_NUM_IREGS); i++)
   {
     fprintf( stderr,"Reg[%d] = %d; Reg_cp = %d\n", i, GPR(i), regs_cp.regs_R[ aRegPtr[i] ] );
   }
}

void regCheck()
{
  //Check all the registers with the internal register file
   for ( int chk = 0; chk < 32; chk++ )
   {
         if ( GPR( chk ) != regs_cp.regs_R[ aRegPtr[chk] ] ) 
           {
               fprintf(stderr," GPR(%d) = %d != %d\n", chk, GPR(chk), regs_cp.regs_R[ aRegPtr[chk] ]);
               print_regs();
               print_regval();exit(0);
               fprintf(stderr, "Registers not equal\n");
           }
   }
   //print_regs();
}

void print_reorder()
{
   fprintf(stderr,"----ReOrder---\n");
   for (int i =0; (unsigned)i < REORDER_WIDTH; i++)
   {
      fprintf(stderr,"busy[%d]=%d thrdID = %d inorder=%d ld= %d alu = %d br = %d  mult = %d LO = %d HI = %d iss = %d, fini = %d, cmplt = %d  spec= %d  excep = %d RS = %d  RT = %d RD = %d Rd_new = %d Rd_old = %d PC = %d,  NPC = %d PredPC = %d wakeUp = %d bitPtr = %d hdPtr = %d followBr = %d thrdValid = %d\n", i,  reoBuffer[i].busy, reoBuffer[i].thrdID, reoBuffer[i].inOrder, reoBuffer[i].lD, reoBuffer[i].alu, reoBuffer[i].br, reoBuffer[i].mult, reoBuffer[i].readLO, reoBuffer[i].readHI, reoBuffer[i].issued, reoBuffer[i].finished, reoBuffer[i].completed, reoBuffer[i].misspeculated, reoBuffer[i].exception, reoBuffer[i].rs, reoBuffer[i].rt,\
         reoBuffer[i].rd, reoBuffer[i].rd_new, reoBuffer[i].rd_old, reoBuffer[i].regs_PC, reoBuffer[i].regs_NPC, reoBuffer[i].pred_PC, reoBuffer[i].wakeUp, reoBuffer[i].thrdBitPtr, thrdBits.hdPtr, reoBuffer[i].followBr, reoBuffer[i].thrdIDValid);
   }

   fprintf(stderr, "-------------------------");
}
   
//--------------End of the General Purpose Functions-------------//

//-------Initialize the Architected Register Pointers------------//
void initialize_ptrs(void)
{
  thrdBits.hdPtr = THREAD_WIDTH/2;
  thrdBits.cmpPtr = 1;
  thrdBits.tailPtr = 0;
  //thrdPC_Q.levelIndex = 0; 

  for (int i=0; i< CONF_MAX; i++)
   confidenceCntr[i] = 0;

 for (unsigned k=0; k< THREAD_WIDTH; k++)
 {
  thrdPC_Q.busy[k] = 0; 
  thrdPC_Q.valid[k] = 0; 
  thrdPC_Q.continueFetch[k] = 0; 
  thrdPC_Q.pathConfidence[k] = 0;
  thrdPC_Q.normConfidence[k] = 0;
 }
  curPtr = 0; 

   regs_cp.regs_R[29] = GPR(29); //Initialize the Register
   regs_cp.valid_R[29] = 1;
   regs_cp.valid_R[0] = 1;

  for (unsigned int j=0; j< (MD_NUM_IREGS+1) ; j++) // Lo & Hi Register
   {
     aRegPtr[j] = j;
     regs_busyBits[j] = 1;
     next_data_ptr->busyPORTS.rd_busy[j] = 1;
     cur_data_ptr->busyPORTS.wr_busy[j] = 1;
     next_data_ptr->busyPORTS.wr_busy[j] = 1;
     regs_cp.valid_R[j] = 1;
   }

 for (unsigned i=0; i< S_WIDTH; i++)
    {
//-----Set Default Address for the Addr Ports------------- 
     //cur_data_ptr->busyPORTS.wr_busy[i] = 1;
     next_data_ptr->busyPORTS.wr_addr[i] = 0;
     cur_data_ptr->busyPORTS.wr_addr[i] = 0;

    // next_data_ptr->busyPORTS.wr_addr[i] = 0;
     //cur_data_ptr->busyPORTS.wr_addr[i] = 0;
     cur_data_ptr->inst_fd.thrdIDValid[i] = 0;
     next_data_ptr->inst_fd.thrdIDValid[i] = 0;

     cur_data_ptr->inst_fd.thrdBitPtr[i] = 0;
     next_data_ptr->inst_fd.thrdBitPtr[i] = 0;
    // cur_data_ptr->busyPORTS.wr_busy_cp[i] = 1;
    }

  for (unsigned i=0; i< COMPLETE_WIDTH; i++)
    {
     cur_data_ptr->arpPORTS.wr_addr_cp[i] = 0;
     cur_data_ptr->arpPORTS.wr_addr_cp[i] = 0;
     next_data_ptr->arpPORTS.wr_addr_cp[i] = 0;
     next_data_ptr->arpPORTS.wr_addr_cp[i] = 0;
     cur_data_ptr->busyPORTS.wr_addr_cp[i] = 0;
     cur_data_ptr->busyPORTS.wr_addr_cp[i] = 0;
     next_data_ptr->busyPORTS.wr_addr_cp[i] = 0;
     next_data_ptr->busyPORTS.wr_addr_cp[i] = 0;
    }
     //fprintf(stderr,"Fetch Begin");
/* for (int k=0; (unsigned) k< (THREAD_LEVEL + 1); k++)  // Lo & Hi Register
 {
  //for (unsigned int j=0; (unsigned) j< (THREAD_WIDTH); j++)  // Lo & Hi Register
  {
   for (int m=0; (unsigned) m< (MD_NUM_IREGS + 1); m++)  // Lo & Hi Register
    {
     rRegPtr[k][0].ptr[m] = m;  
     rRegPtr[k][0].valid[m] = 0;
     rRegPtr[k][0].bitPtr[m] = 0;
    }
  }
 }
*/
 for (int k=0; (unsigned) k< (THREAD_LEVEL + 1); k++)  // Lo & Hi Register
 {
   for (int m=0; (unsigned) m< (MD_NUM_IREGS + 1); m++)  // Lo & Hi Register
    {
     rRegPtr1.ptr[k][m] = m;  
     rRegPtr1.valid[k][m] = 0;
     rRegPtr1.bitPtr[k][m] = 0;
    }
 }
 rRegPtr1.thrdID = 0;
 rRegVector.push_back(rRegPtr1);
 // rBuffer[i].entryBusy = 0;
//******Functional Unit Pointers***********
  for (unsigned i = 0; (unsigned) i < ALU_WIDTH; i++ )
  {
    alu_unit[i].tailPtr = ALU_LAT - 1;                                         
    alu_unit[i].hdPtr = 0;   
  }

  for (unsigned i = 0;(unsigned)  i < MUL_WIDTH; i++ )
  {
    mul_unit[i].tailPtr = MUL_LAT - 1;                                                                                                                                                                       mul_unit[i].hdPtr = 0;   
  }

  for (unsigned i=0;(unsigned)  i < BR_WIDTH; i++) 
  {
    branch_unit[i].tailPtr = BR_LAT - 1;    
    branch_unit[i].hdPtr = 0;
  }
 
  for (unsigned i=0; (unsigned) i < LD_WIDTH; i++)
  {
    load_unit[i].tailPtr = LD_LAT - 1; 
    load_unit[i].hdPtr = 0;                                                                                                                                                                                   }

  for (unsigned  i = 0; (unsigned) i < OT_WIDTH; i++ )
  {
     other_unit[i].tailPtr = OT_LAT - 1; 
     other_unit[i].hdPtr = 0;  
  }

//******Issue Pointers********
  alu_insn.hdPtr = 0;
  alu_insn.tailPtr = 0;

  mul_insn.hdPtr = 0;
  mul_insn.tailPtr = 0;

  br_insn.hdPtr = 0;
  br_insn.tailPtr = 0;

  ls_insn.hdPtr = 0;
  ls_insn.tailPtr = 0;

  ot_insn.hdPtr = 0;
  ot_insn.tailPtr = 0;

  issReadyQ.hdPtr = 0;
  issReadyQ.tailPtr = 0;
  // print_regval();
  // print_regs();
}
  /* reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;
   reorder_busy* REOBUSY = &next_data_ptr->reoBusyPORTS;
   reg_RR_bus* OUTPUT_RF = &next_data_ptr->regfilePORTS;
   reg_bus* OUTPUT_ARP = &next_data_ptr->arpPORTS;
   reg_RRP_bus* OUTPUT_RRP = &next_data_ptr->rrpPORTS;
 */
bool regVectorSearch ( unsigned int searchThrdID )
{
     //-------------- Vector Area------------
       bool vectorFound = 0;
       for (reg_ii =rRegVector.begin(); reg_ii != rRegVector.end(); reg_ii++)
       {
       //   fprintf(stderr," reg_ii->thrdID = %d == %d\n", reg_ii->thrdID, searchThrdID); 
         if ((reg_ii->thrdID) == searchThrdID) //Add Vectors
         {
             vectorFound = 1;
             break;
         }
       }//End of for (Vector)
    if (vectorFound)
      return 1;
    else
      return 0;
}
           //--------------End of Vector Area------------

//****Register File UPDATE Module***********
void regs_Update()
{

  bool discardThrd = 0;
 //----INPUT PORT MAPS-------------
   inst_finish* INPUT_FINI = &cur_data_ptr->inst_fn;
   inst_complete* CMPLT_STALL= &cur_data_ptr->inst_cp;
   inst_rstation* RSTATION_STALL = &cur_data_ptr->inst_rs;

   reg_RR_bus* INPUT_RF = &cur_data_ptr->regfilePORTS;
   reg_bus* INPUT_ARP = &cur_data_ptr->arpPORTS;
   reg_RRP_bus* INPUT_RRP = &cur_data_ptr->rrpPORTS;
   reg_busy* INPUT_BUSY = &cur_data_ptr->busyPORTS;
   //--------Update the complete Bit---------------
  //  fprintf(stderr," complete Update = %d \n",thrdPC_Q.completeBit = CMPLT_STALL->completeBit; // completeBit indicates ThreadSpeculation Mode
    thrdPC_Q.completeBit = CMPLT_STALL->completeBit; // completeBit indicates ThreadSpeculation Mode
//-------------Register Update Writes First---------------------------------------//
//-----Writes the current register value into the storage elements (register file/arp/rrp)----//
    if (INPUT_RF->wr_enableFini )
    {
     for ( i=0; i < S_WIDTH; i++)
      {
        if ( INPUT_RF->wr_addr[i] != 0 )
         {
           regs_cp.regs_R [ INPUT_RF->wr_addr[i] ]= INPUT_RF->wr_data[i];  //Write Data into RegFILE
           //INPUT_RF->wr_addr[i] = 0;
         }
       }// wr_enable fini
    }
    //--------BUSY BITS---------
   // unsigned maskBit = 1; 
  //  maskBit = maskBit << (thrdBits.hdPtr); // Moves 1 for (thrdBits.hdPtr - 1) places
   if ( !RSTATION_STALL->stallUp && !CMPLT_STALL->stallBubble )
   {
    //--------VALID BITS---------
    for ( i=0; i < S_WIDTH; i++)
    {
          if ( INPUT_RF->wr_addrValid[i] != 0 )
           {
             regs_cp.valid_R [ INPUT_RF->wr_addrValid[i] ]= 0;// INPUT_RF->wr_valid[i];  //Write valid bit into RegFILE
           }
     }
   }
 //   discardThrd =  (thrdBits.BITS & maskBit ) ^ (INPUT->thrdID[i] & maskBit); // Flushout the Bad Path
  if ( !RSTATION_STALL->stallUp && !CMPLT_STALL->stallBubble )
   {
    for ( i = 0; i < S_WIDTH ; i++)
     {
         if (INPUT_BUSY->wr_addr[i] != 0 )
         {
            discardThrd = 0;
        /*   if ( thrdPC_Q.completeBit ) 
           {
              discardThrd =  ((thrdBits.BITS  & thrdBits.hdPtr) != (INPUT_RRP->wr_thrdID[i] & (thrdBits.hdPtr))); // Flushout the Bad Path
              //discardThrd =  (thrdBits.BITS & maskBit) ^ (INPUT_RRP->wr_thrdID[i] & maskBit); // Flushout the Bad Path
             // discardThrd =  (thrdBits.BITS & thrdBits.hdPtr) ^ (INPUT_RRP->wr_thrdID[i] & thrdBits.hdPtr); // Flushout the Bad Path
             // discardThrd =  (thrdBits.BITS ^ INPUT_RRP->wr_thrdID[i]); // Flushout the Bad Path
           }*/
           if ( !discardThrd) 
            {
              //if (cycle_count > 3427 )
               //fprintf(stderr," busybit wr_addr = %d \n", INPUT_BUSY->wr_addr[i]);
              regs_busyBits [INPUT_BUSY->wr_addr[i] ]= 1;// INPUT_BUSY->wr_busy[i];  //writing a 1; can replace this statement
            }
         }
        //   fprintf(stderr," Bits = %d, mask = %d rrp_thrdID = %d\n", thrdBits.BITS, maskBit, INPUT_RRP->wr_thrdID[i]);
         //  fprintf(stderr," busyBit addr = %d, discardThrd = %d complete= %d\n", INPUT_BUSY->wr_addr[i], discardThrd, thrdPC_Q.completeBit);
     }
   }
    //----Writes into RRP: Updates the Pointers----//
   // if ( !CMPLT_STALL->stallBubble )
   if ( !RSTATION_STALL->stallUp && !CMPLT_STALL->stallBubble )
    {
       for ( i = 0; i < S_WIDTH ; i++)
       {
        if ( INPUT_RRP->wr_addr[i] != 0  )
        { //Free the assigned registers at Decode
           discardThrd = 0;
          if ( thrdPC_Q.completeBit ) 
          {
              //discardThrd =  ((thrdBits.BITS  & thrdBits.hdPtr) != (INPUT_RRP->wr_thrdID[i] & (thrdBits.hdPtr))); // Flushout the Bad Path
              discardThrd =  !thrdPC_Q.valid[ (INPUT_RRP->wr_thrdID[i])]; // Flushout the Bad Path
              //discardThrd =  (thrdBits.BITS & maskBit) ^ (INPUT_RRP->wr_thrdID[i] & maskBit); // Flushout the Bad Path
              //discardThrd =  (thrdBits.BITS & thrdBits.hdPtr) ^ (INPUT_RRP->wr_thrdID[i] & thrdBits.hdPtr); // Flushout the Bad Path
              //discardThrd =  (thrdBits.BITS ^ INPUT_RRP->wr_thrdID[i]); // Flushout the Bad Path
          }
         if ( !discardThrd) 
          { //Discard Unwanted Thread Streams
          //rRegPtr[INPUT_RRP->wr_bitPtr[i]][INPUT_RRP->wr_thrdID[i]].ptr [ INPUT_RRP->wr_addr[i] ]= INPUT_RRP->wr_data[i]; // Register Pointer
          //rRegPtr[INPUT_RRP->wr_bitPtr[i]][INPUT_RRP->wr_thrdID[i]].valid [ INPUT_RRP->wr_addr[i] ]= 1;// INPUT_RRP->wr_valid[i];
          //rRegPtr[INPUT_RRP->wr_bitPtr[i]][INPUT_RRP->wr_thrdID[i]].bitPtr [ INPUT_RRP->wr_addr[i] ]=  INPUT_RRP->wr_bitPtr[i];

          //-------------- Vector Area------------
        if ( regVectorSearch ( INPUT_RRP->wr_thrdID[i] ) )
           {
                (reg_ii)->ptr [INPUT_RRP->wr_bitPtr[i]][ INPUT_RRP->wr_addr[i] ]= INPUT_RRP->wr_data[i]; // Register Pointer
                (reg_ii)->valid [INPUT_RRP->wr_bitPtr[i]][ INPUT_RRP->wr_addr[i] ]= 1;// INPUT_RRP->wr_valid[i];
                (reg_ii)->bitPtr [INPUT_RRP->wr_bitPtr[i]][ INPUT_RRP->wr_addr[i] ]=  INPUT_RRP->wr_bitPtr[i];
             
           }//End of for (Vector)
          else
           { // Create a new entry
               /* for (unsigned k=0; k <= (THREAD_LEVEL); k++) // Lo & Hi
                {
                 for (unsigned int i=0; i<(MD_NUM_IREGS + 1); i++) // Lo & Hi
                 {
                   rRegPtr1.valid [k][i]= 0;// INPUT_RRP->wr_valid[i];
          //  reg_ii->valid[k][i] = 0;
                  }
                } */
                 rRegPtr1.ptr [INPUT_RRP->wr_bitPtr[i]][ INPUT_RRP->wr_addr[i] ]= INPUT_RRP->wr_data[i]; // Register Pointer
                 rRegPtr1.valid [INPUT_RRP->wr_bitPtr[i]][ INPUT_RRP->wr_addr[i] ]= 1;// INPUT_RRP->wr_valid[i];
                 rRegPtr1.bitPtr [INPUT_RRP->wr_bitPtr[i]][ INPUT_RRP->wr_addr[i] ]=  INPUT_RRP->wr_bitPtr[i];
                 rRegPtr1.thrdID = INPUT_RRP->wr_thrdID[i];
                 //fprintf(stderr," push thrd %d\n", rRegPtr1.thrdID);
                 rRegVector.push_back(rRegPtr1); //Add Vectors
                 rRegPtr1.valid [INPUT_RRP->wr_bitPtr[i]][ INPUT_RRP->wr_addr[i] ]= 0;//Refresh 
                 reg_ii = rRegVector.end(); reg_ii--;
           }

           //--------------End of Vector Area------------
          }//!discard
        } // wr_addr != 0
       }
//                    //if ( rRegPtr[k][(reg_ii)->thrdID].[i] ) 
     }
   /*    for (reg_ii = rRegVector.begin(); reg_ii != rRegVector.end(); reg_ii++)
        {
              for (unsigned int i=0; i<(MD_NUM_IREGS + 1); i++) // Lo & Hi
            fprintf(stderr," valid [0]rs[%d] %d ptr = %d valid %d %d\n", i, (reg_ii)->ptr[0][i], rRegPtr[0][0].ptr[i], (reg_ii)->valid[0][i], rRegPtr[0][0].valid[i]);
        }
  */ 
  //------------FINISH Register Update; Set Data Valid Bit-----------
   if (INPUT_RF->wr_enableFini )
   {
    for ( i = 0; (unsigned) i < WB_WIDTH ; i++)
     {
       if (INPUT_RF->wr_addrValidFini[i] != 0 )
       {
       // fprintf(stderr,"Writing in RegFileFini %d  Valid = %d\t \n", cur_data_ptr->regfilePORTS.wr_addrValidFini[i], cur_data_ptr->regfilePORTS.wr_validFini[i]) ;
        regs_cp.valid_R [ INPUT_RF->wr_addrValidFini[i] ]= INPUT_RF->wr_validFini[i];
       }
     } // for wb_width
    } // if wr_enable

    for ( i = 0; (unsigned) i < WB_WIDTH ; i++)
     {
        if (INPUT_FINI->finishBit[i] != 0 )
        {
           reoBuffer[ INPUT_FINI->finishAddr[i] ].finished = 1; 
        }
     }

   //-----------COMPLETE Register Update; Reset Busy Bits and Write into Architecte Register------------
    if (INPUT_BUSY->wr_enable )
    {
     for ( i = 0; (unsigned) i < COMPLETE_WIDTH ; i++)
      {
         if (INPUT_BUSY->wr_addr_cp[i] != 0 )
         {
           // if ( cycle_count > 3420 )
         //   if ( cycle_count > 9790015 )
          //    fprintf(stderr," CMP wr_addr = %d \n", INPUT_BUSY->wr_addr_cp[i]);
           regs_busyBits [INPUT_BUSY->wr_addr_cp[i] ]= 0;/* INPUT_BUSY->wr_busy_cp[i];*/  //wr_addr[i] is same as i
         }
          
         if (INPUT_ARP->wr_addr_cp[i] != 0 )
          {
           // if (cycle_count > 18676930 )
            //  fprintf(stderr," ARP wr_addr = %d \n", INPUT_ARP->wr_data_cp[i]);
            aRegPtr [ INPUT_ARP->wr_addr_cp[i] ]= INPUT_ARP->wr_data_cp[i];
          }
       }
     }// if wr_enable

}


//-----------incrHdPtr-------------------------
/*inline  void incr_thrdHdptr()
  {
        unsigned int maskBit = 1, checkBit = 0;
        bool incrHd = 1;
       // thrdUpdate = 1; // Indicates that the further completion resumes after a cycle.
       //------Check all the entries for that Bit Position----------
        for ( int i = 0; i < THREAD_WIDTH; i++ )
         {
              maskBit = (maskBit << thrdBits.hdPtr); 
              checkBit = i & maskBit;
              if ( !(checkBit && thrdBits.BITS) )
               {
                 if ( thrdPC_Q.busy[i] ) 
                 {
                    incrHd = 0;  // False, break;
                    break;
                 }
               }
         }

        if (incrHd )
            thrdBits.hdPtr ++;

        if (thrdBits.hdPtr >= THREAD_LEVEL) thrdBits.hdPtr = 0;
  }*/
//------------------FETCH MODULE------------------------------//
 bool followBrPred = 0;
 //followBrPred = 1; // Set to Simply Follow the Br. Prediction without Threading
void
fetch_main()
{
   inst_bus* OUTPUT = &next_data_ptr->inst_fd;
  // reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;

   inst_bus* INPUT = &cur_data_ptr->inst_fd;

   //reg_bus* OUTPUT_ARP = &next_data_ptr->arpPORTS;
   //reg_RRP_bus* OUTPUT_RRP = &next_data_ptr->rrpPORTS;
   inst_dispatch INPUT_STALL = cur_data_ptr->inst_ds;
   inst_dispatch* DECODE_STALL = &cur_data_ptr->inst_ds;
   inst_rstation* RSTATION_STALL = &cur_data_ptr->inst_rs;
   inst_complete* CMPLT_STALL= &cur_data_ptr->inst_cp;

  if (inst_exe)//Fetch Initialization only on first call
  {
     fetchPC = regs.regs_PC;
     cmpFetchPC = fetchPC;
     regs.regs_NPC = regs.regs_PC + sizeof(md_inst_t);
     fetchNPC = regs.regs_NPC;
     cmpFetchNPC = fetchNPC;
     inst_exe = FALSE;
     //activeThreads.hdPtr = 0;
     //activeThreads.tailPtr = 0;
     //----Initialize Threads--------
    if (!followBrPred) {
      thrdPC_Q.thrdPC[0] = fetchPC; 
      thrdPC_Q.thrdID[0] = 0; 
      thrdPC_Q.busy[0] = 1; 
      thrdPC_Q.valid[0] = 1; 
      activeList.push_back(0);
      activeValidList.push_back(0);
      threadBusyList.push_back(0);
      temphdPtr = activeList.begin();
      thrdPC_Q.continueFetch[0] = 1; 
      thrdPC_Q.normConfidence[0] = 1; 
     }
   }

   //Flush All Inputs
   for (int i=0; i < S_WIDTH; i++)
    {
          OUTPUT->inst_a[i] =  0; //cur_data_ptr->inst_fd.rd[i];// out_dep1;// Current Destination operand.
          OUTPUT->inst_b[i] = 0; // cur_data_ptr->inst_fd.rs[i];//in_rs;//Destination operations afer renaming.
          OUTPUT->regs_PC[i] =0; // cur_data_ptr->inst_fd.rd[i];// out_dep1;// Current Destination operand.
          OUTPUT->rs[i] = 0; //cur_data_ptr->inst_fd.rs[i];//in_rs;//Destination operations afer renaming.
          OUTPUT->rt[i] = 0; //cur_data_ptr->inst_fd.rt[i];//Destination operations afer renaming.
    }
  if ( CMPLT_STALL->stallBubble ) //--------UPDATE the PC-------------
   {
    // fprintf(stderr,"PC Updated = %d", CMPLT_STALL->regs_PC );
//     regs.regs_NPC = regs.regs_PC + sizeof(md_inst_t);
     fetchNPC =CMPLT_STALL->regs_PC + sizeof(md_inst_t);
     fetchPC = CMPLT_STALL->regs_PC;
    if (!followBrPred) {
     //----Initialize Threads--------
     curPtr = 0;
     thrdBits.hdPtr =THREAD_WIDTH/2;
     thrdBits.tailPtr = 0;
     thrdPC_Q.thrdPC[0] = fetchPC; 
     thrdPC_Q.thrdID[0] = 0; 
     thrdPC_Q.busy[0] = 1; 
     thrdPC_Q.valid[0] = 1; 
     activeList.push_back(0);
     activeValidList.push_back(0);
     threadBusyList.push_back(0);
     temphdPtr = activeList.begin();
     thrdPC_Q.continueFetch[0] = 1; 
     thrdPC_Q.normConfidence[0] = 1; 
     //activeThreads.hdPtr = 0;
     //activeThreads.tailPtr = 0;
     }
    // exit(0);
   }
      regs.regs_R[MD_REG_ZERO] = 0;
      regs_cp.regs_R[MD_REG_ZERO] = 0;
//----------------------------------------------------------
  //  fprintf(stderr,"\n -----------------Fetch-----------------------------");

   if( RSTATION_STALL->stallUp || DECODE_STALL->stallUp /*|| (INPUT_STALL->stallUp && !INPUT_BUBBLE->stallBubble)  || INPUT_BUBBLE->stallUp*/ )
      //if ( INPUT_STALL->stallUp  )
   {// STALL Fetch; Repeat Previous Data
   //  fprintf ( stderr," \n Fetch Stall");
     for (int i=0; i < S_WIDTH; i++)
     {
      OUTPUT->inst_a[i] = INPUT->inst_a[i];
      OUTPUT->inst_b[i] = INPUT->inst_b[i];
      OUTPUT->regs_PC[i] = INPUT->regs_PC[i];
      OUTPUT->thrdID[i] = INPUT->thrdID[i];
      OUTPUT->thrdIDValid[i] = INPUT->thrdIDValid[i];
      OUTPUT->thrdBitPtr[i] = INPUT->thrdBitPtr[i]; // Thread Bit Ptr 
      OUTPUT->followBr[i] = INPUT->followBr[i];
      OUTPUT->pred_PC[i] = INPUT->pred_PC[i];
      OUTPUT->ld_pred_addr[i] = INPUT->ld_pred_addr[i];
      OUTPUT->stack_recover_idx[i] = INPUT->stack_recover_idx[i];
      //next_data_ptr->inst_fd.inst_b[i] = cur_data_ptr->inst_fd.inst_b[i];
      //next_data_ptr->inst_fd.regs_PC[i] = cur_data_ptr->inst_fd.regs_PC[i];
      OUTPUT->inOrder[i] = cur_data_ptr->inst_fd.inOrder[i];//inOrder;//Destination operations afer renaming.
      OUTPUT->exception[i] = cur_data_ptr->inst_fd.exception[i];// Syscall Instruction.
      OUTPUT->lD[i] = cur_data_ptr->inst_fd.lD[i];//Destination operations afer renaming.
      OUTPUT->alu[i] = cur_data_ptr->inst_fd.alu[i];//Destination operations afer renaming.
      OUTPUT->mult[i] = cur_data_ptr->inst_fd.mult[i];//Destination operations afer renaming.
      OUTPUT->readLO[i] = cur_data_ptr->inst_fd.readLO[i];//Destination operations afer renaming.
      OUTPUT->readHI[i] = cur_data_ptr->inst_fd.readHI[i];//Destination operations afer renaming.
      OUTPUT->br[i] = cur_data_ptr->inst_fd.br[i];//Destination operations afer renaming.
     //OUTPUT_ARP->rs_addr[i] = cur_data_ptr->arpPORTS.rs_addr[i];

     //OUTPUT_RRP->rt_addr[i] = cur_data_ptr->rrpPORTS.rt_addr[i];
     //OUTPUT_ARP->rt_addr[i] = cur_data_ptr->arpPORTS.rt_addr[i];

     //OUTPUT_RRP->rd_addr[i] = cur_data_ptr->rrpPORTS.rd_addr[i];
     //OUTPUT_ARP->rd_addr[i] = cur_data_ptr->arpPORTS.rd_addr[i];
       OUTPUT->rd[i] = INPUT->rd[i];// out_dep1;// Current Destination operand.
       OUTPUT->rs[i] = INPUT->rs[i];//in_rs;//Destination operations afer renaming.
       OUTPUT->rt[i] = INPUT->rt[i];//Destination operations afer renaming.
   /*
     next_data_ptr->inst_fd.inst_a[i] = 0;
     next_data_ptr->inst_fd.inst_b[i] = 0;
     next_data_ptr->inst_fd.regs_PC[i] =0;*/
    // new_ptr_fd->inst_b[i] = cur_ptr_fd->inst_b[i];
    // new_ptr_fd->regs_PC[i] = cur_ptr_fd->regs_PC[i];  //regs.regs_PC;
    }
     if ( CMPLT_STALL->stallBubble )
       {
        // issue_bubbles( &next_data_ptr->inst_fd );
         //fprintf(stderr,"PC RE Updated = %d  PC = %d NPC = %d", CMPLT_STALL->regs_PC, fetchPC, fetchNPC );

        for (int i=0; i < S_WIDTH; i++)
        {
          OUTPUT->inst_a[i] =  0; //cur_data_ptr->inst_fd.rd[i];// out_dep1;// Current Destination operand.
          OUTPUT->inst_b[i] = 0; // cur_data_ptr->inst_fd.rs[i];//in_rs;//Destination operations afer renaming.
          OUTPUT->regs_PC[i] =0; // cur_data_ptr->inst_fd.rd[i];// out_dep1;// Current Destination operand.
          OUTPUT->rs[i] = 0; //cur_data_ptr->inst_fd.rs[i];//in_rs;//Destination operations afer renaming.
          OUTPUT->rt[i] = 0; //cur_data_ptr->inst_fd.rt[i];//Destination operations afer renaming.
         // OUTPUT_RRP->rs_addr[i] = 0; //cur_data_ptr->rrpPORTS.rs_addr[i];
         // OUTPUT_ARP->rs_addr[i] = 0; //cur_data_ptr->arpPORTS.rs_addr[i];

          //OUTPUT_RRP->rt_addr[i] = 0;  //cur_data_ptr->rrpPORTS.rt_addr[i];
         // OUTPUT_ARP->rt_addr[i] = 0;  //cur_data_ptr->arpPORTS.rt_addr[i];

         // OUTPUT_RRP->rd_addr[i] = 0; //cur_data_ptr->rrpPORTS.rd_addr[i];
         // OUTPUT_ARP->rd_addr[i] = 0; //cur_data_ptr->arpPORTS.rd_addr[i];
        }
       }
   }
 else
  {
    /* Out-of-Order Fetch from a Perfect Memory */
  //  signed int temphdPtr = 0;
    bool newThread = 0;
    newThreadList.clear();
    //if ( threadUpdate )
    {
      //thrdActive = thrd_Active();
      thrdActive = activeList.size();
      threadUpdate = 0;
    /*  if( cycle_count > 9127500) 
      {
        fprintf(stderr," total = %d \n", activeList.size() );
        list<unsigned int>::iterator  it; 
        for (it = activeList.begin(); it != activeList.end(); it++)
           fprintf(stderr," thrdID = %d \n", *it );
      }
     */
    }
    if ( thrdActive )  // The Complete Logic resets valid bits.
     {   
        threadCntr[thrdActive]++ ; // No. of Active Threads
        // incr_thrdHdptr();

        // if ( !thrdPC_Q.valid[curPtr] )
         { // Find a valid pointer
            // normalizePathConfidence(); // some paths may have been invalidated;
            // check_completeBit();
             //curPtr = thrd_NextPtr(); 
             if ( activeList.size() > 1)
             {
                thrd_PriorityPtr(); // Add Thrds to Prioirty List
                /*if ( itPrty != priorityList.end())
                {
                   curPtr = itPrty->thrdID;
                   itPrty++;
                   //curPtr = *temphdPtr;
                   //temphdPtr++;
                }
                else*/
                {//Return to the beginning
                   itPrty = priorityList.begin();
                   curPtr = itPrty->thrdID;
                   itPrty++;
                }
          
             }
             else
             {
                temphdPtr = activeList.begin();
                curPtr = *temphdPtr;
               // if( cycle_count > 9127500) 
                // fprintf(stderr," start CurPtr = %d PC = %d total = %d \n",curPtr, thrdPC_Q.thrdPC[curPtr], activeList.size() );
        //        temphdPtr++;
             }
            //if( cycle_count > 8931550) 
             //   fprintf(stderr,"Fetch thrdID = %d\n", curPtr);
           // fprintf(stderr," start CurPtr = %d PC = %d total = %d \n",curPtr, thrdPC_Q.thrdPC[curPtr], activeList.size() );
        //   fprintf(stderr," CurPtr = %d PC = %d total = %d \n",curPtr, thrdPC_Q.thrdPC[curPtr], activeList.size() );
             /*if ( activeList.size() > 1 && temphdPtr != activeList.end())
             {
                 curPtr = *temphdPtr;
                 temphdPtr++; //To avoid the same ID assignment
             }
             else
             {
                 temphdPtr = activeList.begin();
                 curPtr = *temphdPtr;
              }*/
             //curPtr = thrd_PriorityPtr(); 
           // if (cycle_count > 9504900)
          //    fprintf(stderr," newCurPtr = %d Active = %d PC = %d \n",curPtr, thrd_Active(), thrdPC_Q.thrdPC[curPtr] );

             if ( curPtr == THREAD_WIDTH )
              {
                for (unsigned int i = 0; i < THREAD_WIDTH; i++)
                {
                   if ( thrdPC_Q.busy[i] && thrdPC_Q.valid[i] )
                   {
                       fprintf(stderr," i = %d, busy %d valid = %d",i, thrdPC_Q.busy[i], thrdPC_Q.valid[i]);
                   }
                }
                 fprintf(stderr,"\ncycle = %d Dude, No Valid Threads!",cycle_count);
                 exit(-1);
              }
             fetchPC = thrdPC_Q.thrdPC[curPtr];
            // fprintf(stderr,"Thrd  active PC[%d] = %d\n", curPtr, fetchPC);
       //      fetchNPC =  fetchPC + sizeof(md_inst_t);
        }
     }

    /********End of thread reset*************/
    // fprintf(stderr," cycle + %u \n", cycle_count);
    for (int i=0; i < S_WIDTH; i++)
    {
    //  if ( unknownTarget ) break; // Stop Fetch for a Taken Br whose Addr is not known
       MD_FETCH_INST(inst, mem, fetchPC);
       fetchNPC =  fetchPC + sizeof(md_inst_t);
    //     if (cycle_count > 13200)
       MD_SET_OPCODE(op, inst);
       inOrder = 0;
       excep = 0;
       lD = 0;
       br = 0;
       condBr = 0;
       alu = 0;
       mult = 0;
       readLO = 0;
       readHI = 0;
   //    MD_SET_OPCODE(op, inst);
       switch (op)
        {
         #define DEFINST(OP,MSK,NAME,OPFORM,RES,FLAGS,O1,O2,I1,I2,I3)           \
         case OP:                                                       \
          out_dep1 = O1; out_dep2 = O2; in_rs = I1 ; in_rt=I2; \
          if ( MSK == 0x02 ) out_dep1 = 31; \
          if ( (0x30 <= MSK && MSK <= 0x34 ) ) inOrder = 1; \
          if ( (0x20 <= MSK && MSK <= 0x28 ) )  lD = 1; \
          if ( (0xa2 == MSK) ) alu = 1; \
          if ( (MSK == 0x2c) || (MSK == 0x2d) ) excep = 1; \
          if ( (0x40 <= MSK && MSK <= 0x45 ) )  alu = 1; \
          if ( (0x01 <= MSK && MSK <= 0x0a ) ) { br = 1; \
                 if ( 0x05 <= MSK && MSK <= 0x0a ) condBr = 1; }\
          if ( (0x46 <= MSK && MSK <= 0x4d) ) { mult = 1;\
                if ( MSK == 0x4c ) readLO = 1;\
                if ( MSK == 0x4a ) readHI = 1;   } \
          if ( (0x0b == MSK || MSK == 0x0c ) ) excep = 1; \
          if ( (0x35 <= MSK && MSK <= 0x3a) )  excep = 1; \
          if ( (0x29 <= MSK && MSK <= 0x2b) )  excep = 1; \
          if ( (0xc0 <= MSK && MSK <= 0xd2 ) )  excep = 1; \
          if ( (0x70 <= MSK && MSK <= 0x97 ) )  excep = 1; \
          if ( (0xa0 <= MSK && MSK <= 0xa1) )  excep = 1; \
          if ( (0xa3 <= MSK && MSK <= 0xa8 ) )  excep = 1; \
         break;
        #define DECLARE_FAULT(FAULT)                                            \
          { /*fault = (FAULT);*/ break; }
        #include "machine_oo.def"
         /*default:
      fprintf(stderr,"\nInvalid code execution: NOP" );*/
        //  panic("attempted to execute a bogus opcode");
       }

    //   if (cycle_count > 18703000 )
       /*if ( cycle_count > 4000 ) \
       {
         fprintf(stderr," ID = %d Fetch PC = %d\t alu = %d ld = %d \n", curPtr, fetchPC, alu, lD);
         md_print_insn( inst, fetchPC, stderr);
       }*/
     // ******BRANCH PREDICTION*******
     int fe_pred_PC = 0, target_addr = 0, fe_stack_recover_idx = 0;
     unsigned int thrdTotal = 0; // Total No. of Threads
     unsigned int allocPtr = 0;
     unsigned int confEstimate; 
     bool confDir=0;
     unsigned int fe_pred_PC_br = 0;
     bool  changePath = 0,  br_taken = 0;
     struct bpred_update_t pdir_update;     /* bpred direction update info */
     OUTPUT->thrdBitPtr[i] = 0; // Thread Bit Ptr 
     OUTPUT->followBr[i] = 0;  // Indicate if in the thread mode, it follows Br Pred and not eager execution.
     OUTPUT->dir_update[i].pdir1 = NULL;
     OUTPUT->dir_update[i].pdir2 = NULL;
     OUTPUT->dir_update[i].pmeta = NULL;
    //Set Thrd Bit Ptr
     if (thrdActive)
         OUTPUT->thrdBitPtr[i] = thrdPC_Q.bitPtr[curPtr];  // Thread Bit Ptr 

   //  fprintf (stderr, " PC Stream thrdID %u \n", OUTPUT->thrdBitPtr[i] ); 
    if (br)
    {
          fe_pred_PC =  
              bpred_lookup(pred,
                            /* branch address */fetchPC,
                           /* target address */target_addr,
                           /* opcode */op,
                           /* call? */MD_IS_CALL(op),
                           /* return? */MD_IS_RETURN(op),
                           /* updt */&OUTPUT->dir_update[i],
                           /*thrdID*/ curPtr,
                           /* RSB index */&fe_stack_recover_idx);
        //if (cycle_count > 1900)
      //     md_print_insn( inst, fetchPC, stderr);
         //  fprintf (stderr, "Predict %u \n", fe_pred_PC ); 
       // }
    //   if (confEstimate)
     //   fprintf (stderr, "BrPC = %u Conf. Estimate %d \n", fetchPC, confEstimate);

       if ( fe_pred_PC > 1 )
         {
          br_taken = 1;
          fetchNPC = fe_pred_PC; // Predicted PC; Change the Next PC for (JAL, JR, J Instructions)
          fe_pred_PC_br = fe_pred_PC;
         }
       else
         {
           OUTPUT->followBr[i] = 1; // J & Jmps with no hits have to recover
         }
      if (condBr && followBrPred)
      { // For Stats
       confEstimate =  confpred_lookup ( confpred, fetchPC, 0, op ) ;
       confidenceCntr[ confEstimate ]++;
      }
    }
        
   /**********************************************************************************/
     const unsigned UNRESOLVED = 0 ;

       if ( fe_pred_PC > 1 )
          fe_pred_PC_br = fe_pred_PC;
       else
          fe_pred_PC_br = fetchNPC;

     if  ( condBr && !followBrPred && unResolvedCntr < UNRESOLVED  )
      {
          //      md_print_insn( inst, fetchPC, stderr);
          //fetchNPC = fe_pred_PC; // Predicted PC; Change the Next PC for (JAL, JR, J Instructions)
          OUTPUT->followBr[i] = 1;
          unResolvedCntr++;
      //   followBrPred = 1;
      }

      //if ( fetchPC == 4244904 )
       //{ fprintf(stderr, " NPC %d pred = %d\t", fetchNPC, fe_pred_PC);  }

   /***********************************************************************************/ 
     /* valid address returned from branch predictor? */
     if (/*fe_pred_PC > 1 && */condBr && !followBrPred && unResolvedCntr >= UNRESOLVED )
      {
         // OUTPUT->followBr[i] = 0; // J & Jmps with no hits have to recover
         // fe_pred_PC = fetchPC + sizeof(md_inst_t);
          fetchNPC = fetchPC + sizeof(md_inst_t); //  Change the Next PC for (conditional Br Instructions)
        /*---BTB LOOKUP---*/
         //fprintf(stderr," fe_pred_PC = %d pred = %d\n", fetchPC, pred);
         fe_pred_PC = btb_lookup ( pred, fetchPC );
       //  if (cycle_count > 11037 ) {
       // if (cycle_count > 9654800){
        // fprintf(stderr," LookUP PC %d Pred %d UnRes = %d followBr = %d\n", fetchPC, fe_pred_PC, unResolvedCntr, OUTPUT->followBr[i]);
         //md_print_insn( inst, fetchPC, stderr);
         //fprintf(stderr," fe_pred_PC = %d\n", fetchPC);
         //}
        /*--------Confidence Estimation---------*/
         if ( condBr && !followBrPred)
         {
          //Predict the Direction
         //fprintf(stderr," fe_pred_PC = %d pred = %d\n", fetchPC, pred->dirpred.twolev);
	   //confDir = *(bpred_dir_lookup (pred->dirpred.twolev, fetchPC)) >= 2 ? 1:0;
           confDir = br_taken;
        // fprintf(stderr," fe_pred_PC = %d\n", fetchPC);
           // Confidence of this prediction
          confEstimate =  confpred_lookup ( confpred, fetchPC, 0, op ) ;
           confidenceCntr[ confEstimate ]++;
         //fprintf(stderr," confEstimate = %d\n", confEstimate);

	   //dir_update_ptr->pdir1 =
         }
     
       if ( fe_pred_PC > 1000 )
       { 
         unsigned nxtThrdID = 0, compBit = 1;
         bool thrdLevelFree = 1;
         bool thrdLevelEmpty = 1;
         bool resetLevel = 0;

         if ( firstSpawn == 0 )
         { /* Upon First Thread Spawn; Reset all thread PCs */
                curPtr = 0;
                thrdPC_Q.thrdPC[0] = 0; 
                thrdPC_Q.thrdID[0] = 0; 
                thrdPC_Q.bitPtr[0] = 0;// thrdBits.tailPtr; //Br. Level to Resolve
                //fprintf(stderr," Initial = %d\n", thrdBits.tailPtr);
                //exit(0);
       //         thrdPC_Q.busy[0] = 0; 
        //        thrdPC_Q.valid[0] = 0; 
                //thrdPC_Q.continueFetch[0] = 0; 
                thrdPC_Q.thrdParentID[0] = 0; // Record the Parent thrd ID during Wrap Around
                thrdPC_Q.thrdParentLevel[0] = 0; // Record the Parent thrd ID during Wrap Around
                thrdPC_Q.pathConfidence[0] = 0; 
                thrdPC_Q.normConfidence[0] = 0; 
                firstSpawn = 1;
         }

         OUTPUT->thrdBitPtr[i] = thrdPC_Q.bitPtr[curPtr];  // Thread Bit Ptr 
     //      fprintf (stderr, " PC Stream thrdbitptr %d \n", OUTPUT->thrdBitPtr[i] ); 
        unsigned int tempBitPtr = thrdPC_Q.bitPtr[curPtr];
        unsigned int levelIndex = 1;// thrdBits.tailPtr;
        unsigned int temptailPtr = 0;
        unsigned int topLevel = 0;

        temptailPtr = thrdBits.tailPtr;
        if (temptailPtr != 0)
        {
         for (unsigned i = 0; i < THREAD_LEVEL; i++)
         {
           temptailPtr = temptailPtr >> 1; 
           topLevel ++;
           if ( temptailPtr == 0 )
           {
             break;
           }
         }
        }//end if
        //else
         // temptailPtr = 1;
       //   fprintf(stderr," entered %d \n", topLevel);

     //     if (cycle_count > 136)
      //       fprintf(stderr,"Thread BitsPtr = %d curPtr %d btbPC %d\n", tempBitPtr, thrdPC_Q.bitPtr[curPtr], fe_pred_PC);

         if (tempBitPtr == topLevel)
             resetLevel = 1;

         tempBitPtr ++;
         if ( tempBitPtr > THREAD_LEVEL )
         {
             tempBitPtr = 1;
          }

         //Take the curThrdID and compliment the 'tempBitPtr' position and find if it is free          
            compBit = compBit << (tempBitPtr - 1);  
            nxtThrdID = curPtr ^ compBit; // Invert the tempBitPtr bit          

         if ( resetLevel )
         { // Check if the level is free
             //thrdLevelFree = isThrdLevelFree(tempBitPtr);
             levelIndex = levelIndex << (tempBitPtr -1 );
             if ( levelIndex > THREAD_WIDTH/2 && thrdBits.hdPtr >= 1 ) //hdPtr indicates the Branch at this level is yet to be resolved.
             {
                levelIndex = 1;
             }
          //   thrdLevelFree = (levelIndex != thrdBits.hdPtr );
             if ( (levelIndex == thrdBits.hdPtr ))
             {
               thrdLevelFree = 0;
               thrdLevelBusyCntr ++;
                 //fprintf(stderr,"cycle %d Cannot  PC %d ID = %d newLevel= %d ThrdPar %d ->  newID %d par_[%d] = %d Level %d\n", cycle_count, fetchPC, curPtr, tempBitPtr, thrdPC_Q.thrdParentID[nxtThrdID], nxtThrdID, curPtr, thrdPC_Q.thrdParentID[curPtr], levelIndex);
               //fprintf(stderr,"cycle %d Thrd Check PC = %d free = %d BitsPtr = %d curID %d curPtr %d index = %d hdPtr = %d tailPtr = %d\n",cycle_count, fetchPC, thrdLevelFree, tempBitPtr,  curPtr, thrdPC_Q.bitPtr[curPtr], levelIndex, thrdBits.hdPtr, thrdBits.tailPtr);
             }
          }
      //   if( cycle_count > 9127500) 
      //       fprintf(stderr," FreeLevel check cur %d nxt %d valid %d busy %d count = %d\n", curPtr, nxtThrdID, thrdPC_Q.valid[nxtThrdID], thrdPC_Q.busy[nxtThrdID], thrdPC_Q.threadCount[nxtThrdID]);
         
         if ( thrdLevelFree && /*!isThrdLevelBusy( tempBitPtr ) && thrd_Active() <= THREAD_WIDTH &&*/  condBr  && !thrdPC_Q.busy[nxtThrdID] )
         {
           if (resetLevel) 
              thrdBits.tailPtr = levelIndex;
   //         fprintf(stderr,"Create\n");
             //hrdPC_Q.levelIndex = tempBitPtr; // Indicates the next free level
          //  if (cycle_count > 11037)
           //    fprintf(stderr," New thrd BitsPtr = %d\n", thrdBits.tailPtr);
            //if (thrdBits.tailPtr > THREAD_LEVEL  ) thrdBits.tailPtr = 1; 
           //  if  (maxThrdLevel < (thrdPC_Q.bitPtr[curPtr] ) )
            //     maxThrdLevel = thrdPC_Q.bitPtr[curPtr];  // Set Max. Thrd Level
             float curPathConf = thrdPC_Q.pathConfidence[curPtr]; 
             OUTPUT->followBr[i] = 0; // J & Jmps with no hits have to recover
             newThread = 1; 
             thrdTotal = activeList.size();
             if ( thrdTotal == 0 ) //First Branch to be resolved
             {
             //   unsigned int thrdPtr = allocateThrdID();
               curPtr = 0;
              // allocPtr = thrd_AllocPtr();
               if ( allocPtr == THREAD_WIDTH )  fatal ("\n No Thread ID to Allocate ");
             //   thrdPC_Q.thrdPC[0] = fetchNPC; 
              //  thrdPC_Q.thrdID[0] = 0; 
                //thrdPC_Q.bitPtr[0] =  0;// thrdBits.tailPtr; //Br. Level to Resolve
                //fprintf(stderr," Total thrd BitsPtr = %d\n", thrdBits.tailPtr);
               // thrdPC_Q.busy[0] = 1; 
                //thrdPC_Q.valid[0] = 1; 
                //thrdPC_Q.continueFetch[0] = 1; 
                //fprintf( stderr, "cycle = %d  tailPC[%d] = %d\n",cycle_count, fetchNPC,allocPtr);
                 //exit(0);
                //fprintf( stderr, " conf Estimate %d =  %1.2f", confEstimate, /*static_cast<float>/(static_cast<float>(confEstimate)/CONF_MAX));

             //   if (confDir) //Predicted Direction and the Conf. Estimate must be correlated.
                   thrdPC_Q.pathConfidence[0] = 0.3;//1 - (static_cast<float>(confEstimate)/(CONF_MAX)); 
              //  else
               //    thrdPC_Q.pathConfidence[0] = 0.3;//(static_cast<float>(confEstimate)/(CONF_MAX)); 
              //  fprintf(stderr," Thrd[%d] %f = %1.3f\n", curPtr, static_cast<float>(confEstimate)/CONF_MAX, thrdPC_Q.pathConfidence[curPtr]);
          //      md_print_insn( inst, fetchPC, stderr);
               // fprintf( stderr, "cycle = %d  tailPC[%d] = %d\n",cycle_count, fetchNPC,allocPtr);
              }
            //*********New Thread Initializations*********

            //------Set Thread Parenthood----------------
                thrdPC_Q.thrdParentID[nxtThrdID] = curPtr; // Record the Parent thrd ID during Wrap Around
                thrdPC_Q.thrdParentLevel[nxtThrdID] = thrdPC_Q.bitPtr[curPtr]; // Record the Parent thrd ID during Wrap Around
                thrdPC_Q.thrdSiblingID [nxtThrdID] = curPtr ; // Used only while Thread Wraps Around
                thrdPC_Q.thrdSiblingID [curPtr] = nxtThrdID ; // Used only while Thread Wraps Around

           //     if (cycle_count > 800 )
         // if (cycle_count > 9358480)
                // fprintf(stderr,"cycle %d Creating New PC %d ID = %d newLevel= %d ThrdPar %d ->  newID %d par_[%d] = %d\n", cycle_count, fetchPC, curPtr, tempBitPtr, thrdPC_Q.thrdParentID[nxtThrdID], nxtThrdID, curPtr, thrdPC_Q.thrdParentID[curPtr]);
             //---------Change the Br. Level---------------------------------------------------------
                thrdPC_Q.bitPtr[curPtr] += 1; //Change the Br. Level of the Br. Instruction 

                if ( thrdPC_Q.bitPtr[curPtr] > THREAD_LEVEL )
                {
                 //   thrdPC_Q.thrdParentID[curPtr] = curPtr;
                    thrdPC_Q.bitPtr[curPtr] = 1;
                }
                //----Calculate the Cumulative Confidence-------
                if ( thrdTotal != 0 ) //First Branch to be resolved
                {
               //   if (confDir)
                    thrdPC_Q.pathConfidence[curPtr] = (curPathConf == 0 ? 1: curPathConf) * 0.3;  //Not Taken
                 // else
                //    thrdPC_Q.pathConfidence[curPtr] = (curPathConf == 0 ? 1: curPathConf) / ((static_cast<float>(confEstimate)/(CONF_MAX))); 
                }
              //  int thrds = 1;
               // for ( int i = 1; i < (thrdPC_Q.bitPtr[curPtr]); i++ )
                //    thrds *= 2;   // Raise by power 2 
                 //Active Queues
                  newThreadList.push_back(nxtThrdID);
//                 fprintf(stderr," cycle %d push  = %d PC = %d \n", cycle_count, nxtThrdID, thrdPC_Q.thrdPC[nxtThrdID] );

                //allocPtr = curPtr + thrds;
                if ( nxtThrdID & compBit )
                  allocPtr = nxtThrdID;
                else
                { // Not taken path
                  //if (cycle_count > 735)
		//	fprintf(stderr,"Change Path [%d]= %d curID[%d]=%d cycle = %d\n", nxtThrdID, fetchNPC, curPtr, fe_pred_PC, cycle_count );
                   changePath = 1;
                   thrdPC_Q.thrdPC[nxtThrdID] = fetchNPC; 
                   thrdPC_Q.bitPtr[nxtThrdID] = thrdPC_Q.bitPtr[curPtr]; //Br. Level to Resolve
                   thrdPC_Q.thrdID[nxtThrdID] = nxtThrdID; 
                   //----Calculate the Cumulative Confidence-------
                 //  if (confDir)
                  //   thrdPC_Q.pathConfidence[nxtThrdID] = /*(curPathConf == 0 ? 1: curPathConf) */ (1 - (static_cast<float>(confEstimate)/(CONF_MAX))); 
                   //else
                    // thrdPC_Q.pathConfidence[nxtThrdID] = /*(curPathConf == 0 ? 1: curPathConf) */ ((static_cast<float>(confEstimate)/(CONF_MAX))); 
                //   if (confDir)
                   thrdPC_Q.pathConfidence[nxtThrdID] = 0.3 * (curPathConf == 0 ? 1: curPathConf); 
                 //  else
                  //   thrdPC_Q.pathConfidence[nxtThrdID] = 0.3 * ((static_cast<float>(confEstimate)/(CONF_MAX))); 
           
              //  if  (nxtThrdID == 10)
               //    fprintf(stderr,"Not Taken Thrd[%d] = %1.3f \n", nxtThrdID, (thrdPC_Q.pathConfidence[nxtThrdID]) );

                   thrdPC_Q.busy[nxtThrdID] = 1; 
                   thrdPC_Q.valid[nxtThrdID] = 1; 
               //    if( cycle_count > 9127500) 
               //        fprintf(stderr," change path check %d valid %d count = %d\n", nxtThrdID, thrdPC_Q.valid[nxtThrdID], thrdPC_Q.threadCount[nxtThrdID]);
                   thrdPC_Q.continueFetch[nxtThrdID] = 1; 
                   allocPtr = curPtr;
                }

        //	fprintf(stderr,"Busy Path [%d]= %d curID[%d]=%d cycle = %d\n", allocPtr, fe_pred_PC, curPtr, fetchNPC, cycle_count );
                thrdPC_Q.bitPtr[allocPtr] = thrdPC_Q.bitPtr[curPtr]; //Br. Level to Resolve
                thrdPC_Q.thrdPC[ allocPtr ] = fe_pred_PC; 
                thrdPC_Q.thrdID[allocPtr] = allocPtr; 

                //----Calculate the Cumulative Confidence-------
                /*if (confDir)
                   thrdPC_Q.pathConfidence[allocPtr] = /*(curPathConf == 0 ? 1: curPathConf) / (static_cast<float>(confEstimate)/(CONF_MAX)); 
                else
                   thrdPC_Q.pathConfidence[allocPtr] = /*(curPathConf == 0 ? 1: curPathConf) / (1- (static_cast<float>(confEstimate)/(CONF_MAX))); 
                */
                 thrdPC_Q.pathConfidence[allocPtr] = 0.7 * (curPathConf == 0 ? 1: curPathConf);  // Taken Path
                //fprintf(stderr,"Taken Thrd[%d] conf %d = %f cur %f\n", allocPtr, confEstimate, thrdPC_Q.pathConfidence[allocPtr], thrdPC_Q.pathConfidence[curPtr]);
                // exit(0);
            //    fprintf(stderr,"thrd BitsPtr = %d\n", thrdPC_Q.bitPtr[curPtr]);
            //   if  (allocPtr == 10)
             //      fprintf(stderr,"alloc Taken Thrd[%d] = %1.3f \n", allocPtr, (thrdPC_Q.pathConfidence[allocPtr]) );
                thrdPC_Q.busy[allocPtr] = 1; 
                thrdPC_Q.valid[allocPtr] = 1; 
             //  if( cycle_count > 9127500) 
             //       fprintf(stderr," cur check %d valid %d count = %d\n", allocPtr, thrdPC_Q.valid[allocPtr], thrdPC_Q.threadCount[allocPtr]);
                thrdPC_Q.continueFetch[allocPtr] = 1; 
           // if ( thrds < thrd_Total() ) 
            //    thrdBits.tailPtr++;
            //fprintf(stderr,"thrd %d Bits = %d\n",thrdTotal, thrdBits.tailPtr);
               //fprintf( stderr, "cycle = %d Total UnResolved thrds = %d cur = %d PC = %d tailPC[%d] = %d \n",cycle_count, thrd_Total(), curPtr, allocPtr, fetchPC, fe_pred_PC);
            
        }
        /* no predicted taken target, attempt not taken target */
         //fetchNPC = fe_pred_PC;
       // if ( condBr ) // Follow 2 streams for (conditional Branches)
        //  fe_pred_PC = fetchPC + sizeof(md_inst_t); // Do not use the Pred PC to alter the current Fetch Stream
        else
        { /* Follow Branch Predictor -  */
          //fetchNPC = fe_pred_PC; // Predicted PC; Change the Next PC for (JAL, JR, J Instructions)
          if ( thrdLevelFree && thrdPC_Q.busy[nxtThrdID] )
          {
            newLevelBusyCntr ++;
           // fprintf(stderr," cycle %d Next ThrdID %d valid = %d bitptr =%d count = %d cur %d\n", cycle_count, nxtThrdID, thrdPC_Q.valid[nxtThrdID], thrdPC_Q.bitPtr[nxtThrdID], thrdPC_Q.threadCount[nxtThrdID], curPtr);
           if ( thrdPC_Q.busy[nxtThrdID] && thrdPC_Q.threadCount[nxtThrdID] == 0)
            {
              print_reorder();
               exit(0);
             }
          }

          OUTPUT->followBr[i] = 1;
          fetchNPC = fe_pred_PC_br;
          fe_pred_PC = fe_pred_PC_br; 
          //fetchNPC =  fetchPC + sizeof(md_inst_t);
          //fe_pred_PC = fetchNPC;// fe_pred_PC_br; 
         // fprintf( stderr, " Follow Br Pred cond= %d PC = %d level= %d curPtr = %d\n", condBr, fetchPC,  (thrdPC_Q.bitPtr[curPtr] ), curPtr );
        }
      } // End of fe_pred_PC > 0
      else
       {
          OUTPUT->followBr[i] = 1;
          fetchNPC = fe_pred_PC_br;
          fe_pred_PC = fe_pred_PC_br; 
          //fprintf( stderr, "No BTB Match Follow Br Pred cond= %d PC = %d level= %d curPtr = %d\n", condBr, fetchPC,  (thrdPC_Q.bitPtr[curPtr] ), curPtr );
       }
        // if (cycle_count > 11037 ) {
          // md_print_insn( inst, fetchPC, stderr);
           //fprintf(stderr," fe_pred_PC = %d\n", fetchPC);
         //  fprintf(stderr," Final CondBr PC %d Pred %d UnRes = %d followBr = %d\n", fetchPC, fe_pred_PC, unResolvedCntr, OUTPUT->followBr[i]);
        // }
     } // condBr
     else
      {
          OUTPUT->followBr[i] = 1;
          fetchNPC = fe_pred_PC_br;
          fe_pred_PC = fe_pred_PC_br; 
          //fprintf( stderr, "No BTB Match Follow Br Pred cond= %d PC = %d level= %d curPtr = %d\n", condBr, fetchPC,  (thrdPC_Q.bitPtr[curPtr] ), curPtr );
      }
      if ( fetchNPC == 0 ) { fprintf(stderr, " NULL NPC %d", fe_pred_PC_br); exit(-1); }


      /*if (cycle_count > 850 && condBr ) {
           fprintf(stderr," fetch_PC = %d\n", fetchPC);
           md_print_insn( inst, fetchPC, stderr); 
           fprintf(stderr," Ultimate CondBr PC %d Pred %d UnRes = %d followBr = %d\n", fetchPC, fe_pred_PC, unResolvedCntr, OUTPUT->followBr[i]);
       }*/
      /*************Old SuperScalar Mode***************/
      if ( followBrPred )
        OUTPUT->followBr[i] = 0;  // Indicate if in the thread mode, it follows Br Pred and not eager execution.
     /**********************************************/
     
   

     if ( fe_pred_PC == 0 ) // No valid Pred PC
      {    
          fe_pred_PC = fetchPC + sizeof(md_inst_t);
      }

      //--------Predict SW and Load Destination Address
      OUTPUT->ld_pred_addr[i] =0;// 0xFFFFFFFF;
      if ( lD || inOrder )
      {
            OUTPUT->ld_pred_addr[i] =  ldpred_lookup ( ldpred, fetchPC, 0, op ) ;
      }

      if ( mult )
       {  // Set Lo and Hi Registers
          if ( in_rs == 65 ) in_rs = 32; // LO
          if ( in_rt == 65 ) in_rs = 32;

          if ( in_rs == 64 ) in_rs = 32; // HI
          if ( in_rt == 64 ) in_rs = 32;

          if ( out_dep1 == 65 ) out_dep1 = 32;  // Output LO
          if ( out_dep2 == 65 ) out_dep2 = 32;

          if ( out_dep1 == 64 ) out_dep1 = 32;  // Output HI
          if ( out_dep2 == 64 ) out_dep2 = 32;
       }

       OUTPUT->rd[i] =  out_dep1;// Current Destination operand.
       OUTPUT->rs[i] = in_rs;//Destination operations afer renaming.
       OUTPUT->rt[i] = in_rt;//Destination operations afer renaming.
       OUTPUT->inOrder[i] = inOrder;//Destination operations afer renaming.
       OUTPUT->exception[i] = excep;//Destination operations afer renaming.
       OUTPUT->lD[i] = lD;//Destination operations afer renaming.
       OUTPUT->alu[i] = alu;//Destination operations afer renaming.
       OUTPUT->mult[i] = mult;//Destination operations afer renaming.
       OUTPUT->readLO[i] = readLO;//Destination operations afer renaming.
       OUTPUT->readHI[i] = readHI;//Destination operations afer renaming.
       OUTPUT->br[i] = br;//Destination operations afer renaming.
  //------Read RFs: Set the Address---------------------------//
       OUTPUT->inst_a[i] = inst.a;
       OUTPUT->inst_b[i] = inst.b;
       OUTPUT->regs_PC[i] = fetchPC;  //regs.regs_PC;
      // OUTPUT->thrdID[i] = curPtr;  // Thread ID
       OUTPUT->pred_PC[i] = fe_pred_PC;  //regs.regs_PC;
       OUTPUT->stack_recover_idx[i] = fe_stack_recover_idx;  //regs.regs_PC;
       //if (br)
       //fprintf(stderr," stack_recover %d\n", OUTPUT->stack_recover_idx[i]);
     //  OUTPUT->dir_update[i] = pdir_update;  //regs.regs_PC;
 //    if ( cycle_count > 9000 )
  //     fprintf( stderr, " i = %d fetchPC = %d fetchNPC = %d thrdNPC = %d BitPtr = %d follow = %d thrdID = %d\n",i, fetchPC, fetchNPC, thrdPC_Q.thrdPC[curPtr], OUTPUT->thrdBitPtr[i], OUTPUT->followBr[i], curPtr);

   //        fprintf (stderr, " PC Stream thrdbitptr %d \n", OUTPUT->thrdBitPtr[i] ); 
      thrdTotal = activeList.size(); //Max. is Fixed Normally

      if ( thrdTotal > MAX_THREADS )
         thrdTotal = MAX_THREADS;
     //    thrdTotal = thrd_Active();
       //fprintf(stderr," No. of Active Threads %d\n", thrdTotal); 
       if ( thrdTotal  ) //atleast 2 thread are active
       {
        //  fprintf( stderr," Thread Active \n");
          //exit(0);
          if ( i == S_WIDTH - 1 && !changePath )
             thrdPC_Q.thrdPC[curPtr] = fetchNPC; // Save the NPC for subsequent cycles 

          if (changePath)
          {
             fetchNPC = thrdPC_Q.thrdPC[curPtr];  // Save the NPC for subsequent cycles 
          }
          
        //   OUTPUT->thrdBitPtr[i] = thrdPC_Q.bitPtr[curPtr];  // Thread Bit Ptr 
           OUTPUT->thrdID[i] = curPtr;  // Thread ID
           OUTPUT->thrdIDValid[i] = 1;  // Thread ID Valid
        //  fprintf( stderr,"\n Active Fetch ID = %d PC = %d bitPtr = %d", curPtr, fetchPC, thrdPC_Q.bitPtr[curPtr]);
           thrdPC_Q.fetchCount[curPtr]++; //No. of fetched instructions / cycle 
           thrdPC_Q.threadCount[curPtr]++; // No. of instructions from this thread in the pipeline
          // if (curPtr == 10)
       //    fprintf(stderr," %d thrd Count[%d], thrdTotal=%d %d\n",cycle_count, curPtr,thrdTotal, thrdPC_Q.threadCount[curPtr]);
          //**********Fetch Allocation Policy********************************/
           // For 50-50 Allocation uncomment the following line
         // unsigned int pathWidth = S_WIDTH/(thrdTotal == 0 ? 1: thrdTotal);

          unsigned int pathWidth = 0;
          if ( thrdTotal > (S_WIDTH - 1) || thrdTotal == 0 )
            pathWidth = 1;
          else
            pathWidth = S_WIDTH/(thrdTotal);
          
        /* To allocate the Fetch Width Proportional to the Confidence Estimate */
/*           unsigned int pathWidth = 0;
           //fprintf( stderr," cycle = %u curPtr %d ID %d\n", cycle_count, curPtr, thrdPC_Q.thrdID[curPtr]);

           if ( thrdPC_Q.normConfidence[curPtr] <= (1/static_cast<float>(S_WIDTH)) )
           {
              pathWidth = 1;  //Minimum Width of 1 instruction
           }
           else
           {
              pathWidth = static_cast<unsigned int>(thrdPC_Q.normConfidence[curPtr] * S_WIDTH);
           }
           //fprintf( stderr," cycle = %u Confidence[%d] = %1.3f pathwidth %d of %d %f\n", cycle_count, thrdPC_Q.thrdID[curPtr], thrdPC_Q.pathConfidence[curPtr], thrdPC_Q.fetchCount[curPtr], pathWidth, (1/static_cast<float>(S_WIDTH)));
 */          
         if ( thrdPC_Q.fetchCount[curPtr] >= pathWidth )
           {
              //newThread = 0;
                 thrdPC_Q.thrdPC[curPtr] = fetchNPC; // NPC for subsequent cycles 
          //      fprintf(stderr,"  nxtPC %d curPtr = %d count = %d \n", thrdPC_Q.thrdPC[curPtr], curPtr, thrdPC_Q.fetchCount[curPtr] );
                 thrdPC_Q.fetchCount[curPtr] = 0; // reset fetch counter
            /* if (newThread)
             {
                 for ( list<unsigned int>::iterator it = newThreadList.begin(); it != newThreadList.end(); it++)
                 {
                   activeList.push_back(*it); 
                   activeValidList.push_back(*it);
                   threadBusyList.push_back(*it);
        //    fprintf(stderr,"add thrdID = %d\n", *it);
                 }
                 newThreadList.clear();
                 newThread = 0;                
               curPtr = thrd_PriorityPtr();
                //fprintf(stderr,"new thrdID = %d\n", curPtr);
             }*/
        //    fprintf(stderr,"add thrdID1 = %d\n", priorityList.size());

             if ( priorityList.size() > 1)
             {
            //fprintf(stderr,"add thrdID = \n");
                if ( itPrty != priorityList.end())
                {
                   curPtr = itPrty->thrdID;
                   itPrty++;
                }
                else
                {//Return to the beginning
                   itPrty = priorityList.begin();
                   curPtr = itPrty->thrdID;
                   //fprintf( stderr,"\n begin Fetch ID = %d PC = %d ", *temphdPtr, thrdPC_Q.thrdPC[*temphdPtr]);
                   itPrty++;
                }
             }
             else
             {
                temphdPtr = activeList.begin();
                curPtr = *temphdPtr;
                //fprintf( stderr,"\n begin Fetch ID = %d PC = %d ", *temphdPtr, thrdPC_Q.thrdPC[*temphdPtr]);
        //        temphdPtr++;
             }
            //else
              // continue with the same thread

           if ( curPtr == THREAD_WIDTH ) fatal("\n Dude, Switch, No Valid Threads!");

                fetchNPC = thrdPC_Q.thrdPC[curPtr]; // Next PC of Next ThrdPC

          //   fprintf( stderr,"\n Switch Fetch ID = %d PC = %d count = %d ", curPtr, thrdPC_Q.thrdPC[curPtr], thrdPC_Q.threadCount[curPtr]);
          } // End of thread switch

//         if( cycle_count > 8931550) 
 //           fprintf( stderr,"\ncur Fetch ID = %d PC = %d count = %d ", curPtr, thrdPC_Q.thrdPC[curPtr], thrdPC_Q.threadCount[curPtr]);
         
       } // if thrdTotal
       else
       { // No Active Threads
          curPtr = 0;
          OUTPUT->thrdID[i] = 0;  // Thread ID
          OUTPUT->thrdIDValid[i] = 0;  // Thread ID
       }
      // if ( followBrPred )
          // OUTPUT->thrdIDValid[i] = 1;  // Thread ID Valid
    //   fprintf( stderr, "ID[%d] = %d \n", curPtr, thrdPC_Q.thrdID[ curPtr ]);
     //---This code is outside as a result of Thread ID Table
      fetchPC = fetchNPC;
      if ( fetchPC == 0 ) { fprintf(stderr," cycle %d Null PC ", cycle_count);exit(-1); }
       fetchNPC += sizeof(md_inst_t);

       fe_stack_recover_idx = 0;
       fe_pred_PC = 0; //Clear pred_PC
 //  fprintf(stderr,"--------Fetch Stage Completed-------%d \n", OUTPUT->thrdIDValid[i]);
   } // for loog S_WIDTH
   if ( newThread ) 
     { 
       //---------NORMALIZE the Confidence Estimates-----------
     // fprintf(stderr,"--------New Thread-------%d \n", OUTPUT->thrdIDValid[i]);
         for ( list<unsigned int>::iterator it = newThreadList.begin(); it != newThreadList.end(); it++)
         {
            activeList.push_back(*it); 
            activeValidList.push_back(*it);
            threadBusyList.push_back(*it);
        //    fprintf(stderr,"add thrdID = %d\n", *it);
          }
     }
//   fprintf(stderr,"--------Fetch Stage Completed-------%d \n", OUTPUT->thrdIDValid[i]);

  } // if Not Stalled
 //  fprintf ( stderr, " Cycle Cnt %d\n", cycle_count );
   //fprintf(stderr,"-----Fetch Stalled-------\n");
} // End of Fetch

unsigned thrd_PriorityPtr()
 {
   float maxConf = 0, checkConf = 0;
   unsigned int maxThrd = THREAD_WIDTH;
   unsigned thrdMask = 1;
   unsigned int numValid = 0;
   float confSum = 0;  //Confidence Sum
  // if( cycle_count > 9127520) 
   //    fprintf(stderr,"priority \n");

   list<unsigned int>::iterator  it; 
   vector<Func_PC_Entry>::iterator  it_entry; 
   priorityList.clear(); //Refresh Prioirty List each cycle

   for (it = activeList.begin(); it != activeList.end(); it++)
//   for ( int i = 0; i < THREAD_WIDTH; i++)
    {
       if ( thrdPC_Q.busy[*it] && thrdPC_Q.valid[*it] && thrdPC_Q.continueFetch[*it] )
       {

      //  if (cycle_count > 10406740)
        // Find the confidence sum /
        //if ( thrdPC_Q.busy[*it] && thrdPC_Q.valid[*it] && thrdPC_Q.continueFetch[*it] ) 
         {
            numValid ++;
            confSum += thrdPC_Q.pathConfidence[*it];
  //         fprintf(stderr,"path  %1.3f total = %1.3f\n", *it, thrdPC_Q.pathConfidence[*it], confSum);
         }
      //  if (cycle_count > 10406740)
       //    fprintf(stderr," %d valid = %d busy = %d \n", i, thrdPC_Q.busy[i]);
       }
    }
   //}// end of Thread Width
    //   if( cycle_count > 9127520) 
     //      fprintf(stderr,"confsum  %1.3f \n",  confSum);

      if (confSum)
      {
        for (it = activeList.begin(); it != activeList.end(); it++)
        {
          if ( thrdPC_Q.busy[*it] && thrdPC_Q.valid[*it] && thrdPC_Q.continueFetch[*it] ) 
          {
            thrdPC_Q.normConfidence[*it] = static_cast<float>(thrdPC_Q.pathConfidence[*it])/confSum;
            thrdEntry.thrdID = *it;
            thrdEntry.normConfidence = static_cast<unsigned int>(thrdPC_Q.normConfidence[*it]*100);
            priorityList.push_back(thrdEntry); // Add IDs to the priority List
          //  (priorityList.end()-1)->thrdID = *it;
           // (priorityList.end()-1)->normConfidence = static_cast<unsigned int>(thrdPC_Q.normConfidence[*it]*100);
      //     if( cycle_count > 9127520) 
       //      fprintf(stderr," add Entry %d  %d\n", thrdEntry.thrdID, thrdEntry.normConfidence);
          }
         }
      }
      else if (confSum == 0 /*&& numValid == 1*/)
      { //Find and Set Confidence to 1
        for (it = activeList.begin(); it != activeList.end(); it++)
         {
            thrdPC_Q.normConfidence[*it] = 1;
            thrdEntry.thrdID = *it;
            thrdEntry.normConfidence = static_cast<unsigned int>(thrdPC_Q.normConfidence[*it]*100);
            priorityList.push_back(thrdEntry); // Add IDs to the priority List
           /* if ( thrdPC_Q.busy[*it] && thrdPC_Q.valid[*it] && thrdPC_Q.continueFetch[*it] ) 
            {
                thrdPC_Q.normConfidence[*it] = 1;
                thrdEntry.thrdID = *it;
                thrdEntry.normConfidence = thrdPC_Q.normConfidence[*it];
                priorityList.push_back(thrdEntry); // Add IDs to the priority List
            }*/
          } // end for
      } // else if
   
    /*  for (it_entry = priorityList.begin(); it_entry != priorityList.end(); it_entry++)
       {
           fprintf(stderr," Before Priority id  %d  %d\n", it_entry->thrdID, it_entry->normConfidence);
       }
     */
//   for (it = priorityList.begin(); it != priorityList.end(); it++)
    {
      //     fprintf(stderr,"norm  \n");
       sort( priorityList.begin(), priorityList.end(), sortByNorm());
       //    fprintf(stderr,"norm2   \n");
 /*   if( cycle_count > 9127520) 
    {
      for (it_entry = priorityList.begin(); it_entry != priorityList.end(); it_entry++)
       {
           fprintf(stderr,"Priority id  %d  %d\n", it_entry->thrdID, it_entry->normConfidence);
       }
    }
  */   
      //  itPrty = priorityList.begin();
    /*    if  ( thrdPC_Q.normConfidence[*it] >= maxConf)
       // if  ( thrdPC_Q.pathConfidence[*it] >= maxConf)
        {
            maxThrd = *it;
            maxConf = thrdPC_Q.normConfidence[*it];
        //    maxConf = thrdPC_Q.pathConfidence[*it];
        }
     */
    }
      return maxThrd;
 }

/* unsigned int thrd_Total()
 {
   unsigned int cnt = 0;
   for ( int i = 0; i < THREAD_WIDTH; i++)
    {
       if ( thrdPC_Q.busy[i] ) 
       {
         //fprintf(stderr," Thrdbusy %d\n", i);
         cnt++;
        }
    }
   return cnt;
 }*/

/*unsigned thrd_NextPtr()
 {
   static unsigned int thrdPtr = 0;
   unsigned int nxtPtr = 0, numValid = 0;
   float confSum = 0;  //Confidence Sum
   thrdPC_Q.completeBit = 0;
   bool hit = 0;

   for ( int i = 0; i < THREAD_WIDTH; i++)
   {
     find the next valid thrd pointer*/
 //   if ( !hit )
   // {
  //    if ( thrdPtr == THREAD_WIDTH ) thrdPtr = 0;
  //    fprintf( stderr," cycle %d ThrdPTR = %d, busy = %d, valid = %d \n", cycle_count,thrdPtr, thrdPC_Q.busy[thrdPtr], thrdPC_Q.valid[thrdPtr]);
    //  if ( thrdPC_Q.busy[thrdPtr] == 1 && thrdPC_Q.valid[thrdPtr]== 1 && thrdPC_Q.continueFetch[thrdPtr] == 1  )
     // {
      //    thrdPC_Q.completeBit = 1;
       //   nxtPtr = thrdPtr; // Store for the start location of the next thrd_Ptr() call.
        //  thrdPtr ++;
         // hit = 1; 
          
          //break; 
     // }
      //thrdPtr ++ ; // Store for the start location of the next thrd_Ptr() call.
    //}// if (1hit)

    /* Find the confidence sum */
  /*   if ( thrdPC_Q.busy[i] && thrdPC_Q.valid[i] && thrdPC_Q.continueFetch[i] ) 
      {
          numValid ++;
          confSum += thrdPC_Q.pathConfidence[i];
      }
   */
   //}// end of Thread Width

/*      if (confSum)
      {
        for ( int i = 0; i < THREAD_WIDTH; i++)
        {
          if ( thrdPC_Q.busy[i] && thrdPC_Q.valid[i] && thrdPC_Q.continueFetch[i] ) 
          {
            thrdPC_Q.normConfidence[i] = static_cast<float>(thrdPC_Q.pathConfidence[i])/confSum;
          }
         }
      }
      else if (confSum == 0 && numValid == 1)
      { //Find and Set Confidence to 1
         for ( int i = 0; i < THREAD_WIDTH; i++)
         {
            if ( thrdPC_Q.busy[i] && thrdPC_Q.valid[i] && thrdPC_Q.continueFetch[i] ) 
            {
                thrdPC_Q.normConfidence[i] = 1;
             }
          } // end for
      } // else if
   */
     //  if (hit) 
     //    return nxtPtr;
   //    else
  //       return THREAD_WIDTH; // No THREAD ID is Valid
 //}

/* 
 unsigned int thrd_Active()
 {
   unsigned int cnt = 0;
   unsigned int thrdPtr = 0;
   activeThreads.tailPtr = 0;
      fprintf(stderr," Active valid  \n");
  // list <int> activeThreads;
   thrdPtr =  activeThreads.thrdID[activeThreads.hdPtr];
   activeThreads.hdPtr = 0;
   for (unsigned int i = 0; i < THREAD_WIDTH; i++)
    {
       if (thrdPtr == THREAD_WIDTH) thrdPtr = 0;
      // if ( thrdPC_Q.valid[i] && thrdPC_Q.continueFetch[i] ) 
       if ( thrdPC_Q.valid[thrdPtr] && thrdPC_Q.continueFetch[thrdPtr] ) 
       {
          activeThreads.thrdID[activeThreads.tailPtr] = thrdPtr;
          activeThreads.tailPtr ++;
      //  if (cycle_count > 133)
         //  fprintf(stderr," Active valid = %d busy = %d \n", i, thrdPC_Q.busy[i]);
          cnt++;
       }
       thrdPtr++;
    }
   if ( cnt == 0 && !followBrPred) { fprintf(stderr," Active = 0 \n"); 
      for (unsigned int i = 0; i < THREAD_WIDTH; i++)
      {
        if ( thrdPC_Q.valid[i] && thrdPC_Q.continueFetch[i] ) 
          fprintf (stderr,"cycle %d id %d busy %d valid %d contin %d\n", cycle_count, i, thrdPC_Q.busy[i], thrdPC_Q.valid[i], thrdPC_Q.continueFetch[i] ); 
      }

     exit(0);}
   return cnt;
 }
*/
void check_completeBit()
  {
     thrdPC_Q.completeBit = 0;
      for ( int i =0; i < THREAD_WIDTH; i++ )
      {
         if ( thrdPC_Q.busy[i] ) 
         {
            if ( !thrdPC_Q.valid[i] )
               thrdPC_Q.completeBit = 1;
         }
       }
  }
 //------------------------ End of Fetch Support Functions------------------------------------------------------
 inline void issue_bubbles( inst_dispatch* OUTPUT )
 {
     
       //if (  OUTPUT->regs_PC[i] != 0)//Instr. Addr.
       {
         for ( i=0; i < S_WIDTH; i++)
         {
         OUTPUT->inst_a[i] = 0;//inst_a & inst_b are parts of same opcode.
         OUTPUT->inst_b[i] = 0;
         OUTPUT->regs_PC[i] = 0;//Instr. Addr.
         OUTPUT->thrdID[i] = 0;  // Thread ID
         OUTPUT->thrdBitPtr[i] = 0;  // Thread ID
         OUTPUT->thrdIDValid[i] = 0;  // Thread ID
         OUTPUT->followBr[i] = 0;  // Thread ID
         OUTPUT->pred_PC[i] = 0;   //regs.regs_PC;
         OUTPUT->ld_pred_addr[i] = 0;   //regs.regs_PC;
         OUTPUT->stack_recover_idx[i] = 0;  //regs.regs_PC;
         //OUTPUT->dir_update[i] = null_dir_update;  //regs.regs_PC;
          OUTPUT->dir_update[i].pdir1 = NULL;
          OUTPUT->dir_update[i].pdir2 = NULL;
          OUTPUT->dir_update[i].pmeta = NULL;
         OUTPUT->inOrder[i] = 0;//inOrder;//Destination operations afer renaming.
         OUTPUT->exception[i] = 0;//inOrder;//Destination operations afer renaming.
         OUTPUT->lD[i] = 0;//Destination operations afer renaming.
         OUTPUT->br[i] = 0;//Destination operations afer renaming.
         OUTPUT->alu[i] = 0;//Destination operations afer renaming.
         OUTPUT->mult[i] = 0;//Destination operations afer renaming.
         OUTPUT->readLO[i] = 0;//Destination operations afer renaming.
         OUTPUT->readHI[i] = 0;//Destination operations afer renaming.

         OUTPUT->rd[i] = 0;// Current Destination operand. 
         OUTPUT->rd_old[i] = 0;//Destination operand before renaming.
         OUTPUT->rd_new[i] = 0;//Destination operand afer renaming.
         OUTPUT->rs[i] = 0;//Destination operations afer renaming.
         OUTPUT->rt[i] = 0;//Destination operations afer renaming.
         //OUTPUT->freePtr[i] = 0;
         }
       }
        //print_regs();
}

//******************DECODE MODULE *********************************
void decode_main(/*fetchInput, dispatchOutput*/ )
{
//------------Outputs-----------------------------
   inst_dispatch* OUTPUT = &next_data_ptr->inst_ds; 
   inst_dispatch* prevOUT = &cur_data_ptr->inst_ds;  //Used for Stall Up

   reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;
   reg_RR_bus* OUTPUT_RF = &next_data_ptr->regfilePORTS;
   //reg_bus* OUTPUT_ARP = &next_data_ptr->arpPORTS;
   reg_RRP_bus* OUTPUT_RRP = &next_data_ptr->rrpPORTS;

   reg_busy* prevBUSY = &cur_data_ptr->busyPORTS;
   reg_RR_bus* prevRF = &cur_data_ptr->regfilePORTS;
   //reg_bus* prevARP = &cur_data_ptr->arpPORTS;
   reg_RRP_bus* prevRRP = &cur_data_ptr->rrpPORTS;
   //-----------Inputs-------------------------------
   inst_bus* INPUT =   &cur_data_ptr->inst_fd;  //Alias
   //inst_dispatch* DISPATCH_STALL = &cur_data_ptr->inst_ds;
   inst_rstation* RSTATION_STALL = &cur_data_ptr->inst_rs;
   inst_complete* CMPLT_STALL= &cur_data_ptr->inst_cp;

   for ( i=0; i < S_WIDTH; i++)
   {
       //  OUTPUT_BUSY->wr_addr[ i ] = 0; 
      //---------Clear the Ouputs----------------
         OUTPUT->rd[i] = 0;// Current Destination operand. 
         OUTPUT->rd_old[i] = 0;//Destination operand before renaming.
         OUTPUT->rd_new[i] = 0;//Destination operand afer renaming.
         OUTPUT->rs[i] = 0;//Destination operations afer renaming.
         OUTPUT->rt[i] = 0;//Destination operations afer renaming.
       //  OUTPUT_RF->rs_addr[i] = 0;  //SET Read Ports of RF 
        // OUTPUT_RF->rt_addr[i] = 0;
         OUTPUT_RF->wr_valid[i] = 0; //Invalidate the new entry
         OUTPUT_RF->wr_addrValid[i] = 0;
         OUTPUT_BUSY->wr_addr[ i ] = 0;
         OUTPUT_RRP->wr_valid[i] = 0;                     //Set the new Pointer to be valid                                                      
         OUTPUT_RRP->wr_data[i] = 0;     //New Pointer                                                                                  
         OUTPUT_RRP->wr_bitPtr[i] = 0;     //New Pointer                                                                                  
         OUTPUT_RRP->wr_addr[i] = 0;            //Destination Addr.                                                                                                                                                            
         OUTPUT_RRP->wr_thrdID[i] = 0;            //Destination Addr.                                                                                                                                                            
   }
  if ( !(RSTATION_STALL->stallUp) ) {
  //------------------Priority Encoder To find Free Registers---------------------------------
   OUTPUT->stallUp = 0;
  
   for ( i=1; (unsigned )i <= (MD_NUM_IREGS + MD_XREGS); i++)
    {
     if ( regs_busyBits [i]/* next_data_ptr->busyPORTS.rd_busy[i] */ == 0 ) //BUSY(i)== 0 )//UNCLOCKED  Check is ith register is free 
      {
           freeRegs[num] = 0;
        // fprintf(stderr,"READ BUSY =%d\n",BUSY(i));
        // if (num < S_WIDTH)
        //{
            freeRegs[num] = i;
        //next_data_ptr->busyPORTS.wr_addr[num] = i;
        //SET_BUSY( i, 1 ); //Register Number to set busy.
	    //fprintf(stderr,"\nFree Pointer %d ", i );
            num ++;
            if (num == S_WIDTH) break;//Break the for loop if 4 free registers are found
        //}
      }
    }
//-------------------------------------------------------------------------
    if ( num < S_WIDTH )//If 4 Free Pointers were not found. 
    {
         OUTPUT->stallUp = 1;// SET STALL
         issue_bubbles( &next_data_ptr->inst_ds );  
     //---ISSUE BUBBLES----
       for (i=0; i < S_WIDTH; i++)
        {
        /* OUTPUT->inst_a[i] = 0;//inst_a & inst_b are parts of same opcode.
         OUTPUT->inst_b[i] = 0;
         OUTPUT->regs_PC[i] = 0;//Instr. Addr.
         OUTPUT->inOrder[i] = 0;//inOrder;//Destination operations afer renaming.
         OUTPUT->lD[i] = 0;//Destination operations afer renaming.

         OUTPUT->rd[i] = 0;// Current Destination operand. 
         OUTPUT->rd_old[i] = 0;//Destination operand before renaming.
         OUTPUT->rd_new[i] = 0;//Destination operand afer renaming.
         OUTPUT->rs[i] = 0;//Destination operations afer renaming.
         OUTPUT->rt[i] = 0;//Destination operations afer renaming.
         next_data_ptr->regfilePORTS.rs_addr[i] = 0;  //SET Read Ports of RF 
         next_data_ptr->regfilePORTS.rt_addr[i] = 0;
         next_data_ptr->rrpPORTS.wr_valid[i] = 0;                     //Set the new Pointer to be valid                                                                     
         next_data_ptr->rrpPORTS.wr_data[i] = 0;     //New Pointer                                                                                  
         next_data_ptr->rrpPORTS.wr_addr[i] = 0;            //Destination Addr.                                                                                                                                                            
         */
         //OUTPUT_RF->rs_addr[i] = 0;  //SET Read Ports of RF 
         //OUTPUT_RF->rt_addr[i] = 0;
         OUTPUT_RF->wr_addrValid[i] = 0; 
         OUTPUT_BUSY->wr_addr[ i ] = 0; 

         OUTPUT_RRP->wr_valid[i] = 0;                     //Set the new Pointer to be valid                                                                     
         OUTPUT_RRP->wr_data[i] = 0;     //New Pointer                                                                                  
         OUTPUT_RRP->wr_bitPtr[i] = 0;     //New Pointer                                                                                  
         OUTPUT_RRP->wr_addr[i] = 0;            //Destination Addr.                                                                                                                                                            
         //OUTPUT->freePtr[i] = 0;
        }
        print_regs();
        print_reorder();
        fprintf(stderr,"Decode Stalled");
        exit(-1);
     }
    else if ( CMPLT_STALL->stallBubble == 1 )
    {
       //---ISSUE BUBBLES----
       //if (  OUTPUT->regs_PC[i] != 0)//Instr. Addr.
       {
      //  fprintf(stderr," FLUSHOUT\n");
        issue_bubbles( &next_data_ptr->inst_ds );  
        for ( i=0; i < S_WIDTH; i++)
        {
        /* OUTPUT->inst_a[i] = 0;//inst_a & inst_b are parts of same opcode.
         OUTPUT->inst_b[i] = 0;
         OUTPUT->regs_PC[i] = 0;//Instr. Addr.
         OUTPUT->inOrder[i] = 0;//inOrder;//Destination operations afer renaming.
         OUTPUT->lD[i] = 0;//Destination operations afer renaming.

         OUTPUT->rd[i] = 0;// Current Destination operand. 
         OUTPUT->rd_old[i] = 0;//Destination operand before renaming.
         /UTPUT->rd_new[i] = 0;//Destination operand afer renaming.
         OUTPUT->rs[i] = 0;//Destination operations afer renaming.
         OUTPUT->rt[i] = 0;//Destination operations afer renaming.*/
         //OUTPUT_RF->rs_addr[i] = 0;  //SET Read Ports of RF 
         //OUTPUT_RF->rt_addr[i] = 0;
           OUTPUT_RF->wr_valid[i] = 0; //Invalidate the new entry
           OUTPUT_RF->wr_addrValid[i] = 0;
           OUTPUT_BUSY->wr_addr[ i ] = 0;

           OUTPUT_RRP->wr_thrdID[i] = 0;                     //Set the new Pointer to be valid                                                                     
           OUTPUT_RRP->wr_valid[i] = 0;                     //Set the new Pointer to be valid                                                                     
           OUTPUT_RRP->wr_data[i] = 0;     //New Pointer                                                                                  
           OUTPUT_RRP->wr_bitPtr[i] = 0;     //New Pointer                                                                                  
           OUTPUT_RRP->wr_addr[i] = 0;            //Destination Addr.                                                                                                                                                            
         //OUTPUT->freePtr[i] = 0;
         }
        } // if regs_PC !=0
      // issue_bubbles( &next_data_ptr->inst_ds );  
       //fprintf(stderr," Issue Bubbles\n");
    }
   else
    {
     for (  i = 0; i < S_WIDTH; i++)
     {
        //fprintf(stderr," Out Pred PC = %d cycle = %d valid = %d\n", OUTPUT->pred_PC[i], cycle_count, INPUT->thrdIDValid[i]);

         OUTPUT->inst_a[i] = INPUT->inst_a[i];//inst_a & inst_b are parts of same opcode.
         OUTPUT->inst_b[i] = INPUT->inst_b[i];
         OUTPUT->regs_PC[i] = INPUT->regs_PC[i];//Instr. Addr.
         OUTPUT->thrdID[i] = INPUT->thrdID[i];  // Thread ID
         OUTPUT->thrdBitPtr[i] = INPUT->thrdBitPtr[i];  // Thread ID
         OUTPUT->thrdIDValid[i] = INPUT->thrdIDValid[i];  // Thread ID
         OUTPUT->pred_PC[i] = INPUT->pred_PC[i];  //regs.regs_PC;
         OUTPUT->ld_pred_addr[i] = INPUT->ld_pred_addr[i];   //regs.regs_PC;
         OUTPUT->stack_recover_idx[i] = INPUT->stack_recover_idx[i];  //regs.regs_PC;
         OUTPUT->dir_update[i] = INPUT->dir_update[i];  //regs.regs_PC;
       //  fprintf(stderr,"Decode Pred_PC = %d\n", OUTPUT->pred_PC[i]);
         OUTPUT->inOrder[i] = INPUT->inOrder[i];//Destination operations afer renaming.
         OUTPUT->exception[i] = INPUT->exception[i];//Destination operations afer renaming.
         OUTPUT->lD[i] = INPUT->lD[i];//Destination operations afer renaming.
         OUTPUT->alu[i] = INPUT->alu[i];//Destination operations afer renaming.
         OUTPUT->mult[i] = INPUT->mult[i];//Destination operations afer renaming.
         OUTPUT->readLO[i] = INPUT->readLO[i];//Destination operations afer renaming.
         OUTPUT->readHI[i] = INPUT->readHI[i];//Destination operations afer renaming.
         OUTPUT->br[i] = INPUT->br[i];//Destination operations afer renaming.
         OUTPUT->followBr[i] = INPUT->followBr[i];  //Reset the MASK
          //      if (cycle_count > 9000 )
    // fprintf(stderr," Decode PC = %d Bit Ptr = %d followBr = %d cycle = %d\n", OUTPUT->regs_PC[i], OUTPUT->thrdBitPtr[i], OUTPUT->followBr[i], cycle_count);

         inst.a= INPUT->inst_a[i];
         inst.b= INPUT->inst_b[i];
      /*   next_data_ptr->regfilePORTS.rs_addr[i] = 0;  //SET Read Ports of RF 
         next_data_ptr->regfilePORTS.rt_addr[i] = 0;
         next_data_ptr->regfilePORTS.wr_addrValid[i] = 0;// freeRegs[i];
         next_data_ptr->rrpPORTS.wr_valid[i] = 0;                     //Set the new Pointer to be valid                                                                     
         next_data_ptr->rrpPORTS.wr_data[i] = 0;     //New Pointer                                                                                  
         next_data_ptr->rrpPORTS.wr_addr[i] = 0; */           //Destination Addr.                                                                                                                                	//--------------------Allocation----------------------------------//
       if ( inst.a > 0 )
       {
         rs_allocate = 0; 
         rt_allocate = 0; 
         rd_allocate = 0; 
	//--------------Override Logic-----------------------//
        if ( i > 0 )
        {	
            for (int j = i-1; j >= 0; j-- )
	     {
                //fprintf ( stderr, " j = %d Rd = %d prev_rd=%d \n",j, INPUT->rd[i], INPUT->rd[j] );
//              if ( INPUT->thrdID[i] == INPUT->thrdID[j] )
              if ( threadMatch( INPUT->thrdBitPtr[j], INPUT->thrdID[j],INPUT->thrdBitPtr[i], INPUT->thrdID[i] ) )
              {
		if ( rs_allocate == 0 && INPUT->rs[i] == INPUT->rd[j] && (INPUT->rs[i] > 0 && INPUT->rs[i] < 34) )
		{
                    rs_allocate = 1; 
		    OUTPUT->rs[i] = freeRegs[j];
                //  if (cycle_count > 7200 )
                 //   fprintf ( stderr, "PC = %d Override RS = %d \n", INPUT->regs_PC[i], freeRegs[j] );
		}

		if ( rt_allocate == 0 && INPUT->rt[i] == INPUT->rd[j] && (INPUT->rt[i] > 0 && INPUT->rt[i] < 34) )
		{
                    rt_allocate = 1; 
		    OUTPUT->rt[i] = freeRegs[j];
       //             fprintf ( stderr, " Override Rt = %d \n", freeRegs[j] );
		}

		if ( rd_allocate == 0 &&  INPUT->rd[i] == INPUT->rd[j] && (INPUT->rd[i] > 0 && INPUT->rd[i] < 34) )
		{
                    rd_allocate = 1; 
		    OUTPUT->rd_old[i] = freeRegs[j];
                   // temp_rd_old = freeRegs[j];
       //         fprintf ( stderr, " Override Rd = %d \n", OUTPUT->rd_old[i] );
	 	}
               }

	     } // End of For Loop
	} // End of if (override Logic)

       signed int thrdRenameID = 0;
       signed int curThrdID = 0, prevThrdID = 0, siblingThrdID = 0;
       signed int thrdLevel = 0;
       unsigned int thrdMask =  1;
       unsigned int levelCnt = 0;
       bool regMapped = 0;// False
       //-----------Finding Top UnResolved Level------------
    /*    unsigned int topLevel = 0; // top level unresolved branch level
        unsigned int tempHdPtr = 0;
        if ( thrdBits.hdPtr !=0 )
        {
          tempHdPtr = thrdBits.hdPtr;
          for (unsigned i = 0; i < THREAD_LEVEL; i++)
          {
            tempHdPtr = tempHdPtr >> 1; 
            topLevel ++;
            if ( tempHdPtr == 0 )
            {
            //  if ( topLevel >= THREAD_LEVEL ) topLevel = 1;
              break;
            }
          }
       //   fprintf(stderr," entered %d \n", topLevel);
        }
        else
           topLevel = 1;
   */
   //    if ( topLevel == THREAD_LEVEL ) topLevel = 1;
       //--------------------------------------------------
       if ( !rs_allocate ) 
	{
         if ( 0 < INPUT->rs[i] && INPUT->rs[i] < 34) //Valid
         {
           if ( INPUT->thrdIDValid[i] == 1 && INPUT->thrdBitPtr[i] > 0)
           {// if thrd.Valid
           //First search all the levels with the same thrdID
              regMapped = 0;
              thrdMask = 1;
              thrdLevel = INPUT->thrdBitPtr[i]; //Start from Current Level
              curThrdID = INPUT->thrdID[i]; //Start from Current ThrdID 
       //     fprintf(stderr," Main PC = %d thrdLevel = %d, ID = %d valid = %d\n", INPUT->regs_PC[i], thrdLevel, curThrdID, INPUT->thrdIDValid[i] );
            
            /*  while ( levelCnt < THREAD_LEVEL  ) 
              { // Checks for same ThrdID
               // Check if the Renamed Register is Valid 
                  if ( rRegPtr[thrdLevel][curThrdID].valid[ INPUT->rs[i] ] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 ) 
                  {//-------Read from the RRP--------------------
                     OUTPUT->rs[ i ] = rRegPtr[thrdLevel][curThrdID].ptr[ INPUT->rs[i] ]; //READ_RRP_RS(i); //      
                     if (cycle_count > 700)
                        fprintf(stderr," Main PC = %d thrdLevel = %d, ID = %d\n", INPUT->regs_PC[i], thrdLevel, curThrdID);
                    //   if (cycle_count > 18703000 )
                     //    fprintf(stderr," Rs Hit %d %d ID = %d PC = %d\n", OUTPUT->rs[i], curThrdID, INPUT->thrdID[i], INPUT->regs_PC[i]);
                     regMapped = 1;
                     break; // break while
                   }
             
                   if ( !regMapped ) 
                   {
                      thrdLevel = thrdLevel - 1; // Move above 1 thrdLevel
                      if (thrdLevel <= 0) thrdLevel = THREAD_LEVEL; // Move above 1 thrdLevel
                      levelCnt++;
                   }
               } // end of while(thrdLevel)
              */
                if ( !regMapped   )
                { // Change the ThrdID
                   levelCnt = 0;
                   thrdLevel = INPUT->thrdBitPtr[i]; //Start from Current Level
                   curThrdID = INPUT->thrdID[i]; //Start from Current ThrdID 
                   while ( levelCnt < THREAD_LEVEL  && regMapped == 0) 
                   { // Checks for same ThrdID
                    // if ( curThrdID == INPUT->thrdID[i] )
                    // fprintf(stderr,"AREG PC = %d thrdLevel = %d, ID = %d\n", INPUT->regs_PC[i], thrdLevel, curThrdID);
                  //   if (cycle_count > 6750)
                   //       fprintf(stderr," RS PC = %d  thrd ID = %d lvl = %d hdPtr = %d\n", INPUT->regs_PC[i], curThrdID, thrdLevel, thrdBits.hdPtr);
                if ( regVectorSearch (curThrdID) )
                {
                      if ( (reg_ii)->valid[thrdLevel][INPUT->rs[i]] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 ) 
                      {//-------Read from the RRP--------------------
                         OUTPUT->rs[ i ] = (reg_ii)->ptr[thrdLevel][INPUT->rs[i]]; //READ_RRP_RS(i); //      
                      //   if (cycle_count > 18703000 )
                      //   if ( cycle_count > 17575000 )
                       //    fprintf(stderr," Rs Hit 2 %d lvl = %d cur= %d ID = %d PC = %d\n", OUTPUT->rs[i], thrdLevel, curThrdID, INPUT->thrdID[i], INPUT->regs_PC[i]);
                         regMapped = 1;
                         break; // break while
                      }
                  }
           /*  else
             { // Check if the Renamed Register is Busy
               if ( regs_busyBits[rRegPtr[thrdLevel][curThrdID].ptr[ INPUT->rs[i] ]] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 ) 
               {//-------Read from the RRP--------------------
                   OUTPUT->rs[ i ] = rRegPtr[thrdLevel][curThrdID].ptr[ INPUT->rs[i] ]; //READ_RRP_RS(i); //      
                   regMapped = 1;
                   break; // break while
               }
             }*/
                     if ( !regMapped ) 
                     {
                     //   if (thrdLevel == thrdBits.hdPtr) break; // TopLevel
	                thrdMask = 1;
       	                thrdMask = ( thrdMask <<  (thrdLevel - 1)); // Since Level Count is Sub. earlier siblingThrdID = ( thrdMask ^  curThrdID ); // 2^(thrdLevel+1)/2 
                        siblingThrdID = ( thrdMask ^  curThrdID ); // 2^(thrdLevel+1)/2 
                        if ( (thrdPC_Q.thrdParentLevel[curThrdID] == thrdPC_Q.thrdParentLevel[siblingThrdID]) ) break;
                //   	if (cycle_count > 700)
                 //     	fprintf(stderr," PC = %d thrd Mask = %d curID = %d sib = %d par = %d\n", INPUT->regs_PC[i], thrdMask, curThrdID, siblingThrdID, thrdPC_Q.thrdParentID[curThrdID]);
                  	thrdLevel = thrdLevel - 1; // Move above 1 thrdLevel
                  	if (thrdLevel <= 0) 
                  	{
                        //  if (curThrdID == 0)
                         //    if ( thrdPC_Q.thrdParentLevel[0] == 0 ) break;

                    	   thrdLevel = THREAD_LEVEL; // Move above 1 thrdLevel

                           //if ( (thrdPC_Q.thrdParentLevel[curThrdID] == 0) && (thrdPC_Q.thrdParentLevel[siblingThrdID] == 0) )
                           if ( (thrdPC_Q.thrdParentLevel[curThrdID] == thrdPC_Q.thrdParentLevel[siblingThrdID]) )
                           { break; }
                  	}

                   	if (thrdPC_Q.thrdParentID[ curThrdID ] == siblingThrdID && thrdPC_Q.thrdParentLevel[curThrdID] == thrdLevel ) 
                   	{
                      //if ( thrdPC_Q.thrdIDValid[ siblingThrdID ] )
                         curThrdID = siblingThrdID;
                   	}
               // if (cycle_count > 700)
                //          fprintf(stderr," RT PC = %d  thrd ID = %d lvl = %d top = %d hdPtr = %d\n", INPUT->regs_PC[i], curThrdID, thrdLevel, topLevel, thrdBits.hdPtr);
                //curThrdID = ( thrdMask  >> (THREAD_LEVEL - thrdLevel)) & curThrdID; // 2^(thrdLevel+1)/2 

//                       if (cycle_count > 700)
 //                         fprintf(stderr,"PC = %d  thrd ID = %d lvl = %d top = %d hdPtr = %d\n", INPUT->regs_PC[i], curThrdID, thrdLevel, topLevel, thrdBits.hdPtr);

                       levelCnt++;

                     } //!regMapped
                   } // end of while(thrdLevel)

                } //!regMapped
              }// if thrd.Valid

              if (!regMapped)
              {//--------Read from the Parent ThrdID Register----------
                if ( regVectorSearch (0) )
                {
                   if ( (reg_ii)->valid[0][INPUT->rs[i]] ==  1 )
                     OUTPUT->rs[ i ] = (reg_ii)->ptr[0][INPUT->rs[i]]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                   else
                     OUTPUT->rs[ i ] = aRegPtr[ INPUT->rs[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                }
                else
                     OUTPUT->rs[ i ] = aRegPtr[ INPUT->rs[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
            /*   if ( rRegPtr[0][0].valid[ INPUT->rs[i] ] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 ) 
                  OUTPUT->rs[ i ] = rRegPtr[0][0].ptr[ INPUT->rs[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                else
                  OUTPUT->rs[ i ] = aRegPtr[ INPUT->rs[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
              */
                 // if (cycle_count > 6750)
                  // fprintf(stderr," Rs hit Areg %d %d ID = %d PC = %d\n", OUTPUT->rs[i], curThrdID, INPUT->thrdID[i], INPUT->regs_PC[i]);
             //--------------------------------------------
              } //End of !regMapped 

          } // End of if Input < 34
	} // End of !rs_allocate
        
       if ( !rt_allocate ) 
	{
         if ( 0 < INPUT->rt[i] && INPUT->rt[i] < 34) //Valid
          {
            regMapped = 0;
           if ( INPUT->thrdIDValid[i] == 1 && INPUT->thrdBitPtr[i] > 0)
           {
            levelCnt = 0;
            thrdMask = 1;
            thrdLevel = INPUT->thrdBitPtr[i]; //Start from Current Level
            curThrdID = INPUT->thrdID[i]; //Start from Current ThrdID
          /* while ( levelCnt < THREAD_LEVEL ) 
           { // Checks for same ThrdID
             //if ( curThrdID == INPUT->thrdID[i] )
             {// Check if the Renamed Register is Valid 
                if ( rRegPtr[thrdLevel][curThrdID].valid[ INPUT->rt[i] ] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 )
                {//-------Read from the RRP--------------------
                     if (cycle_count > 700)
                        fprintf(stderr," Main Rt PC = %d thrdLevel = %d, ID = %d\n", INPUT->regs_PC[i], thrdLevel, curThrdID);
                    OUTPUT->rt[ i ] = rRegPtr[thrdLevel][curThrdID].ptr[ INPUT->rt[i] ]; //READ_RRP_RS(i); //      
                    //fprintf(stderr,"rt[%d] hit = %d lvl= %d ID = %d\n", INPUT->rt[i], OUTPUT->rt[i], thrdLevel, curThrdID);
                    regMapped = 1;
                    break; // break while
                 }
              }

             if ( !regMapped ) 
             {
                thrdLevel = thrdLevel - 1; // Move above 1 thrdLevel
                if (thrdLevel <= 0) thrdLevel = THREAD_LEVEL; // Move above 1 thrdLevel
                levelCnt++;
             }
           } // end of while(thrdLevel)
            */
         if ( !regMapped )
          {
            levelCnt = 0;
            thrdLevel = INPUT->thrdBitPtr[i]; //Start from Current Level
            curThrdID = INPUT->thrdID[i]; //Start from Current ThrdID

           while ( levelCnt < THREAD_LEVEL && regMapped == 0) 
           { // Checks for same ThrdID
             //if ( curThrdID == INPUT->thrdID[i] )
              // Check if the Renamed Register is Valid 
                 //   if (cycle_count > 9355144)
                  //        fprintf(stderr," RT PC = %d  thrd ID = %d lvl = %d  hdPtr = %d\n", INPUT->regs_PC[i], curThrdID, thrdLevel, thrdBits.hdPtr);
     //           fprintf(stderr,"RT PC = %d thrdLevel = %d, ID = %d\n", INPUT->regs_PC[i], thrdLevel, curThrdID);
                if ( regVectorSearch (curThrdID) )
                {
                 if ( (reg_ii)->valid[thrdLevel][INPUT->rt[i]] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 )
                 {//-------Read from the RRP--------------------
                    OUTPUT->rt[ i ] = (reg_ii)->ptr[thrdLevel][INPUT->rt[i]]; //READ_RRP_RS(i); //      
                    regMapped = 1;
                //if (cycle_count > 9329883)
                 //  fprintf(stderr," RT[%d] = %d\n", INPUT->rt[i], rRegPtr[thrdLevel][curThrdID].ptr[ INPUT->rt[i] ]);
                    break; // break while
                  }
                }

             if ( !regMapped ) 
             {
                //curThrdID = ( thrdMask  >> (THREAD_LEVEL - thrdLevel)) & curThrdID; // 2^(thrdLevel+1)/2 
                //   if (thrdLevel == thrdBits.hdPtr) break; // TopLevel
                   thrdMask = 1;
                   thrdMask = ( thrdMask <<  (thrdLevel - 1)); // Since Level Count is Sub. earlier 
                   siblingThrdID = ( thrdMask ^  curThrdID ); // 2^(thrdLevel+1)/2 

                   // if (cycle_count > 9355144)
                    //  fprintf (stderr," curPar[%d] %d sibPar[%d] %d\n",curThrdID, thrdPC_Q.thrdParentLevel[curThrdID], siblingThrdID, thrdPC_Q.thrdParentLevel[siblingThrdID] );

                   if ( (thrdPC_Q.thrdParentLevel[curThrdID] == thrdPC_Q.thrdParentLevel[siblingThrdID]) ) break;
                 //  if (cycle_count > 700)
                  //    fprintf(stderr," PC = %d thrd Mask = %d curID = %d sib = %d par = %d\n", INPUT->regs_PC[i], thrdMask, curThrdID, siblingThrdID, thrdPC_Q.thrdParentID[curThrdID]);
                  thrdLevel = thrdLevel - 1; // Move above 1 thrdLevel
                  if (thrdLevel <= 0) 
                  {
                 //   if ( curThrdID == 0 )
                  //     if ( thrdPC_Q.thrdParentLevel[0] == 0 ) break;
                    thrdLevel = THREAD_LEVEL; // Move above 1 thrdLevel
                    //if ( thrdPC_Q.thrdParentLevel[curThrdID] == 0 && thrdPC_Q.thrdParentLevel[siblingThrdID] == 0) break;
                  }

                  if (thrdPC_Q.thrdParentID[ curThrdID ] == siblingThrdID && thrdPC_Q.thrdParentLevel[curThrdID] == thrdLevel ) 
                   {
                      //if ( thrdPC_Q.thrdIDValid[ siblingThrdID ] )
                         curThrdID = siblingThrdID;
                   }
               // if (cycle_count > 700)
                //          fprintf(stderr," RT PC = %d  thrd ID = %d lvl = %d top = %d hdPtr = %d\n", INPUT->regs_PC[i], curThrdID, thrdLevel, topLevel, thrdBits.hdPtr);

                levelCnt++;
             } //if !regMapped

            } // end of while(thrdLevel)

          }
         } //thrdValid
           if (!regMapped)
           {//--------Read from the Parent ThrdID Register----------
                if ( regVectorSearch (0) )
                {
                   if ( (reg_ii)->valid[0][INPUT->rt[i]] ==  1 )
                     OUTPUT->rt[ i ] = (reg_ii)->ptr[0][INPUT->rt[i]]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                   else
                     OUTPUT->rt[ i ] = aRegPtr[ INPUT->rt[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                }
                else
                     OUTPUT->rt[ i ] = aRegPtr[ INPUT->rt[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
             //--------------------------------------------
                  //if (cycle_count > 6750)
                   //fprintf(stderr," Ptr RT[%d] = %d valid ptr = %d\n", INPUT->rt[i], OUTPUT->rt[i], rRegPtr[0][0].valid[ INPUT->rt[i] ]);
           } //End of !regMapped 

          }
	}
     //--------REGISTER File Reads------------------------------//
         //next_data_ptr->regfilePORTS.rs_addr[i] = OUTPUT->rs[i];  //SET Read Ports of RF 
        // next_data_ptr->regfilePORTS.rt_addr[i] = OUTPUT->rt[i];
        // OUTPUT_RF->rs_addr[i] = OUTPUT->rs[i];  //SET Read Ports of RF 
         //OUTPUT_RF->rt_addr[i] = OUTPUT->rt[i];
    //   fprintf( stderr, " rs_addr = %d, rt_addr = %d ", next_data_ptr->arpPORTS.rt_data[i], next_data_ptr->arpPORTS.rt_data[i]);// OUTPUT->rt[i] );
    //---------------------------------------------------------//

   //-----------------Rename the Destination Register-------------------------
     //fprintf(stderr,"Dest[%d] =%d\n", freeNum, OUTPUT->rd[freeNum]);
      if ( 0 < INPUT->rd[i]  && INPUT->rd[i] < 34 )
       {
      //    fprintf(stderr,"OUTPUT Depend = %d\n", out_dep1);
      //fprintf(stderr,"--------Decode RD \t %d \t %d \t %d \t %d-----", OUTPUT->rd_old[freeNum], rRegPtr.ptr[out_dep1], out_dep1, out_dep2);
      //-----------------------------------------------------------------------
       if ( !rd_allocate ) 
	{
        // if ( 0 < INPUT->rt[i] && INPUT->rt[i] < 34) //Valid
         
          {
            regMapped = 0;
          if ( INPUT->thrdIDValid[i] == 1 && INPUT->thrdBitPtr[i] > 0)
          {
            levelCnt = 0;
            thrdMask = 1;
            thrdLevel = INPUT->thrdBitPtr[i]; //Start from Current Level
            curThrdID = INPUT->thrdID[i]; //Start from Current ThrdID
          /* while ( levelCnt < THREAD_LEVEL ) 
           { // Checks for same ThrdID
             //if ( curThrdID == INPUT->thrdID[i] )
             {// Check if the Renamed Register is Valid 
                if ( rRegPtr[thrdLevel][curThrdID].valid[ INPUT->rd[i] ] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 )
                {//-------Read from the RRP--------------------
                    OUTPUT->rd_old[ i ] = rRegPtr[thrdLevel][curThrdID].ptr[ INPUT->rd[i] ]; //READ_RRP_RS(i); //      
                    //if (cycle_count > 18702970 )
                     // fprintf(stderr," 0 rd_old = %d PC = %d lvl= %d ID = %d\n", OUTPUT->rd_old[i], INPUT->regs_PC[i], thrdLevel, curThrdID);
                    regMapped = 1;
                    break; // break while
                 }
              }

             if ( !regMapped ) 
             {
                thrdLevel = thrdLevel - 1; // Move above 1 thrdLevel
                if (thrdLevel <= 0) thrdLevel = THREAD_LEVEL; // Move above 1 thrdLevel
                levelCnt++;:wq

             }
           } // end of while(thrdLevel)
           */
         if ( !regMapped )
          {
            levelCnt = 0;
            thrdLevel = INPUT->thrdBitPtr[i]; //Start from Current Level
            curThrdID = INPUT->thrdID[i]; //Start from Current ThrdID
           while ( levelCnt < THREAD_LEVEL && regMapped == 0) 
           { // Checks for same ThrdID
             //if ( curThrdID == INPUT->thrdID[i] )
              // Check if the Renamed Register is Valid 
//               if ( cycle_count > 9790015 )
                //  fprintf(stderr,"%d RD PC = %d thrdLevel = %d, ID = %d\n", cycle_count, INPUT->regs_PC[i], thrdLevel, curThrdID);
                if ( regVectorSearch (curThrdID) )
                {
                
                if ( (reg_ii)->valid[thrdLevel][INPUT->rd[i]] == 1 )//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 )
                {//-------Read from the RRP--------------------
                    OUTPUT->rd_old[ i ] = (reg_ii)->ptr[thrdLevel][INPUT->rd[i]]; //READ_RRP_RS(i); //      
                    regMapped = 1;
                    //if (cycle_count > 18702970 )
  //                  if ( cycle_count > 9790015 )
   //                     fprintf(stderr," 1 rd_old = %d PC = %d lvl= %d ID = %d\n", OUTPUT->rd_old[i], INPUT->regs_PC[i], thrdLevel, curThrdID);
                    break; // break while
                 }
               }
             if ( !regMapped ) 
             {
                
                //if (cycle_count > 4240)
                 //   fprintf(stderr," thrd ID = %d lvl = %d top = %d hdPtr = %d\n", curThrdID, thrdLevel, topLevel, thrdBits.hdPtr);
                //curThrdID = ( thrdMask  >> (THREAD_LEVEL - thrdLevel)) & curThrdID; // 2^(thrdLevel+1)/2 
                 //  if (thrdLevel == thrdBits.hdPtr) break; // TopLevel
                   thrdMask = 1;
                   thrdMask = ( thrdMask <<  (thrdLevel - 1)); // Since Level Count is Sub. earlier 
                   siblingThrdID = ( thrdMask ^  curThrdID ); // 2^(thrdLevel+1)/2 

                   if ( (thrdPC_Q.thrdParentLevel[curThrdID] == thrdPC_Q.thrdParentLevel[siblingThrdID]) ) break;
                  // if (cycle_count > 700)
                   //   fprintf(stderr," PC = %d thrd Mask = %d curID = %d sib = %d par = %d\n", INPUT->regs_PC[i], thrdMask, curThrdID, siblingThrdID, thrdPC_Q.thrdParentID[curThrdID]);
                  thrdLevel = thrdLevel - 1; // Move above 1 thrdLevel
                  if (thrdLevel <= 0) 
                  {
                    thrdLevel = THREAD_LEVEL; // Move above 1 thrdLevel
                    //if ( thrdPC_Q.thrdParentLevel[curThrdID] == 0 && thrdPC_Q.thrdParentLevel[siblingThrdID] == 0) break;
                  }
                  if (thrdPC_Q.thrdParentID[ curThrdID ] == siblingThrdID && thrdPC_Q.thrdParentLevel[curThrdID] == thrdLevel ) 
                   {
                      //if ( thrdPC_Q.thrdIDValid[ siblingThrdID ] )
                         curThrdID = siblingThrdID;
                   }
              //  if (cycle_count > 9340100)
               //      fprintf(stderr," RD PC = %d  thrd ID = %d lvl = %d hdPtr = %d\n", INPUT->regs_PC[i], curThrdID, thrdLevel, thrdBits.hdPtr);
                //curThrdID = ( thrdMask  >> (THREAD_LEVEL - thrdLevel)) & curThrdID; // 2^(thrdLevel+1)/2 

                //if (cycle_count > 18702970 )
                //curThrdID = prevThrdID;
                //prevThrdID = curThrdID - 2; // 2^(thrdLevel+1)/2 
                //if (prevThrdID < 0 ) prevThrdID = 0;
                levelCnt++;
             } // !regMapped
            } // end of while(thrdLevel)

           //  if ( regMapped && thrdLevel > INPUT->thrdBitPtr[i] && rRegPtr[0][0].valid[ INPUT->rd[i] ] == 1 )
            // { // thrdLevel > INPUT->thrdLevel is not valid if rRegPtr[0][0] is valid; Hence it overrides;
             //     OUTPUT->rd_old[ i ] = rRegPtr[0][0].ptr[ INPUT->rd[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
             //}
                 //if (cycle_count > 18702970 )
                  //    fprintf(stderr," 2 rd_old = %d PC = %d lvl= %d ID = %d\n", OUTPUT->rd_old[i], INPUT->regs_PC[i], thrdLevel, curThrdID);
          }
        } // !thrdValid
           if (!regMapped)
           {//--------Read from the Parent ThrdID Register----------
                if ( regVectorSearch (0) )
                {
                   if ( (reg_ii)->valid[0][INPUT->rd[i]] ==  1 )
                     OUTPUT->rd_old[ i ] = (reg_ii)->ptr[0][INPUT->rd[i]]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                   else
                     OUTPUT->rd_old[ i ] = aRegPtr[ INPUT->rd[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                }
                else
                     OUTPUT->rd_old[ i ] = aRegPtr[ INPUT->rd[i] ]; //READ_ARP_RS(i); //aRegPtr[ in_rs ];
                  //if ( cycle_count > 9790015 )
                   //   fprintf(stderr," 3 rd_old = %d PC = %d lvl= %d ID = %d\n", OUTPUT->rd_old[i], INPUT->regs_PC[i], thrdLevel, curThrdID);
             //--------------------------------------------
           } //End of !regMapped 

          }
	}
       /* if ( rd_allocate == 0 ) 
	{
          if ( rRegPtr[INPUT->thrdBitPtr[i]][INPUT->thrdID[i]].valid[ INPUT->rd[i] ] )//  CHECK VALID_RRP_RD(i) == 1 ) //rRegPtr.valid[ out_dep1 ] == 1)  //if not cleared after recovery
          {
            OUTPUT->rd_old[i ] = rRegPtr[INPUT->thrdBitPtr[i]][INPUT->thrdID[i]].ptr[ INPUT->rd[i] ];// READ_RRP_RD(i);Pass the OLD Dest. Reg.to complete for the ARP
         //   fprintf(stderr,"--------RRF to \t %d from\t %d-----", freePtr[freeNum], rRegPtr.ptr[out_dep1]);
          }
          else
          {
         // fprintf(stderr,"---ACTUAL POINTER------%d and rename %d\t", aRegPtr[out_dep1], rRegPtr.ptr[out_dep1] );
            OUTPUT->rd_old[ i ] = aRegPtr[ INPUT->rd[i] ];//READ_ARP_RD(i);
         //   fprintf(stderr,"--------RRF to \t %d from\t %d-----", freePtr[freeNum], aRegPtr[out_dep1]);
          }
	}*/
                                                                                                                                                                                             
         OUTPUT->rd[i] = INPUT->rd[i];     //Pass the actual Dest. Reg. to complete for the ARP
         OUTPUT->rd_new[i] = freeRegs[i]; // rRegPtr.ptr[out_dep1];//Pass the Dest. Reg.tocomplete for the ARP

         OUTPUT_RRP->wr_valid[i] = 1;                     //Set the new Pointer to be valid                                                                     
         OUTPUT_RRP->wr_data[i] = freeRegs[i];     //New Pointer                                                                                  
         OUTPUT_RRP->wr_bitPtr[i] = INPUT->thrdBitPtr[i];     //bit Ptr
         OUTPUT_RRP->wr_addr[i] = INPUT->rd[i];           //Destination Addr.
         OUTPUT_RRP->wr_thrdID[i] = INPUT->thrdID[i];           //Destination Addr.                                                                                                                                                            
         //fprintf(stderr," RRP wr_data = %d\n", freeRegs[i]);
         OUTPUT_BUSY->wr_busy[ i ] = 1;
         OUTPUT_BUSY->wr_addr[ i ] = freeRegs[i] ;
    //     if (cycle_count > 3427 )
          // if (cycle_count > 9318646 )
           //fprintf(stderr,"decode busybit thrdID wr_addr[%d] = %d \n", INPUT->thrdID[i], OUTPUT->regs_PC[i], OUTPUT_BUSY->wr_addr[i]);
         

         OUTPUT_RF->wr_valid[i] = 0; //Invalidate the new entry
         OUTPUT_RF->wr_addrValid[i] = freeRegs[i];
         }
        } //End of  NOP Check

   } //End of For Loop
  }                 // next_data_ptr->regfilePORTS.wr_addr[i] = INPUT->freeRegs[i];
   
      //fprintf(stderr,"--------SET BUSY \t %d-----\n", INPUT_STALL->freePtr[freeNum]);
      //fprintf(stderr,"READ BUSY =%d\n",BUSY(i));
                                                                                                                                                                                             
      //fprintf(stderr,"\nBusy Set for %d\n", OUTPUT->freePtr[ freeNum ]);
      //fprintf(stderr,"Dest[%d] =%d\n", freeNum, OUTPUT->rd[freeNum]);

  }
 else
  {//During StallUp
       //fprintf(stderr," Dispatch-Decode StallUp \n");
       for ( i=0; i < S_WIDTH; i++)
        {
         OUTPUT->inst_a[i] = prevOUT->inst_a[i] ;//inst_a & inst_b are parts of same opcode.
         OUTPUT->inst_b[i] =  prevOUT->inst_b[i];
         OUTPUT->regs_PC[i] = prevOUT->regs_PC[i];//Instr. Addr.
        // if (cycle_count > 18702986 )
        //   if (cycle_count > 9318646 )
         //     fprintf(stderr," stall dis PC = %d thrdID = %d\n", prevOUT->regs_PC[i], prevOUT->thrdID[i]);
         OUTPUT->thrdID[i] = prevOUT->thrdID[i];//Instr. Addr.
         OUTPUT->thrdBitPtr[i] = prevOUT->thrdBitPtr[i];  // Thread ID
         OUTPUT->thrdIDValid[i] = prevOUT->thrdIDValid[i];//Instr. Addr.
         OUTPUT->followBr[i] = prevOUT->followBr[i];  //Reset the MASK
         OUTPUT->pred_PC[i] = prevOUT->pred_PC[i];  //regs.regs_PC;
         OUTPUT->ld_pred_addr[i] = prevOUT->ld_pred_addr[i];   //regs.regs_PC;
         OUTPUT->stack_recover_idx[i] = prevOUT->stack_recover_idx[i];  //regs.regs_PC;
         OUTPUT->dir_update[i] = prevOUT->dir_update[i];  //regs.regs_PC;
         OUTPUT->inOrder[i] = prevOUT->inOrder[i];//inOrder;//Destination operations afer renaming.
         OUTPUT->exception[i] = prevOUT->exception[i];//inOrder;//Destination operations afer renaming.
         OUTPUT->lD[i] = prevOUT->lD[i];//Destination operations afer renaming.
         OUTPUT->alu[i] = prevOUT->alu[i];//Destination operations afer renaming.
         OUTPUT->mult[i] = prevOUT->mult[i];//Destination operations afer renaming.
         OUTPUT->readLO[i] = prevOUT->readLO[i];//Destination operations afer renaming.
         OUTPUT->readHI[i] = prevOUT->readHI[i];//Destination operations afer renaming.
         OUTPUT->br[i] = prevOUT->br[i];//Destination operations afer renaming.

         OUTPUT->rd[i] = prevOUT->rd[i];// Current Destination operand. 
         OUTPUT->rd_old[i] = prevOUT->rd_old[i];//Destination operand before renaming.
         OUTPUT->rd_new[i] = prevOUT->rd_new[i];//Destination operand afer renaming.
         OUTPUT->rs[i] = prevOUT->rs[i];//Destination operations afer renaming.
         OUTPUT->rt[i] = prevOUT->rt[i];//Destination operations afer renaming.
        // next_data_ptr->regfilePORTS.rs_addr[i] = cur_data_ptr->regfilePORTS.rs_addr[i];  //SET Read Ports of RF 
        // next_data_ptr->regfilePORTS.rt_addr[i] = cur_data_ptr->regfilePORTS.rt_addr[i];
        // OUTPUT_RF->rs_addr[i] = cur_data_ptr->regfilePORTS.rs_addr[i];  //SET Read Ports of RF 
         //OUTPUT_RF->rt_addr[i] = cur_data_ptr->regfilePORTS.rt_addr[i];
         OUTPUT_RRP->wr_thrdID[i] = prevRRP->wr_thrdID[i];           //Destination Addr.                                                                                                                                                            
         OUTPUT_RRP->wr_valid[i] =  prevRRP->wr_valid[i];// cur_data_ptr->rrpPORTS.wr_valid[i];                     //Set the new Pointer to be valid                                                                     
         OUTPUT_RRP->wr_data[i] =  prevRRP->wr_data[i];// cur_data_ptr->rrpPORTS.wr_data[i];     //New Pointer                                                                                  
         OUTPUT_RRP->wr_bitPtr[i] =  prevRRP->wr_bitPtr[i];// cur_data_ptr->rrpPORTS.wr_bitPtr[i];     //New Pointer                                                                                  
         OUTPUT_RRP->wr_addr[i] =  prevRRP->wr_addr[i];// cur_data_ptr->rrpPORTS.wr_addr[i];            //Destination Addr.                                                                                                                                                            
        // OUTPUT_RF->wr_addr[i] =  prevRF->wr_addr[i]; 
         OUTPUT_RF->wr_addrValid[i] =  prevRF->wr_addrValid[i]; 
      //   OUTPUT_BUSY->wr_busy[ i ] =  prevBUSY->wr_busy[i];
          //fprintf(stderr," prev_wr_addr %d \n", prevBUSY->wr_addr[i]);
         //OUTPUT_BUSY->wr_addr[ i ] = 0; 
         OUTPUT_BUSY->wr_addr[ i ] =  prevBUSY->wr_addr[i];
         //OUTPUT->freePtr[i] = 0;
        }
     if ( CMPLT_STALL->stallBubble == 1 )
     {
       //---ISSUE BUBBLES----
       issue_bubbles( &next_data_ptr->inst_ds );  
       for ( i=0; i < S_WIDTH; i++)
        {
         //OUTPUT_RF->rs_addr[i] = 0;   //SET Read Ports of RF 
        // OUTPUT_RF->rt_addr[i] = 0;
         //OUTPUT_RF->wr_addr[i] = 0; 
         OUTPUT_RF->wr_addrValid[i] = 0; 
         OUTPUT_RRP->wr_thrdID[i] = 0;           //Destination Addr.                                                                                                                                                            
         OUTPUT_RRP->wr_valid[i] = 0;                     //Set the new Pointer to be valid                                                                     
         OUTPUT_RRP->wr_data[i] = 0;     //New Pointer                                                                                  
         OUTPUT_RRP->wr_bitPtr[i] = 0;     //New Pointer                                                                                  
         OUTPUT_RRP->wr_addr[i] = 0;            //Destination Addr.                                                                                                                                                            
         OUTPUT_BUSY->wr_addr[ i ] = 0; 
         //OUTPUT->freePtr[i] = 0;
        }
      // issue_bubbles( &next_data_ptr->inst_ds );  
      // fprintf(stderr," Issue Bubbles\n");
     }
      // issue_bubbles( &next_data_ptr->inst_ds );  
  }

}



//************DISPATCH MODULE*****************************//
void dispatch_main()
{
   bool discardThrd = 0;
   unsigned int maskBit = 1;
  //  inst_dispatch* OUTPUT_STALL = new_ptr_ds;
 // inst_issue* INPUT_STALL_rs = &cur_data_ptr->inst_rs;
  inst_rstation* OUTPUT = &next_data_ptr->inst_rs;
   
 
 // reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;
  //reg_RR_bus* OUTPUT_RF = &next_data_ptr->regfilePORTS;
  inst_dispatch* INPUT = &cur_data_ptr->inst_ds;
  inst_rstation* RSTATION_STALL= &cur_data_ptr->inst_rs;
  //inst_finish* FINISH_STALL = &cur_data_ptr->inst_fn; 
  inst_complete* CMPLT_STALL= &cur_data_ptr->inst_cp;
   reg_RRP_bus* INPUT_RRP = &cur_data_ptr->rrpPORTS;
   reg_busy* INPUT_BUSY = &cur_data_ptr->busyPORTS;

   OUTPUT->stallUp = 0;
 //----------------Free the Assigned Registers---------
   if ( CMPLT_STALL->stallBubble )
    {
       // rRegPtr.ptr[ INPUT->rd[i] ] = INPUT->rd_old[i];//Set the dest.to point to this new register
        //rRegPtr.valid[ INPUT->rd[i] ] = 1;
       for ( i = 0; i < S_WIDTH; i++)
        {
          //if (cycle_count > 18676985 )
           // fprintf(stderr," cmp stall %d\n", INPUT->rd_new[i]);
        regs_busyBits [ INPUT->rd_new[i] ] = 0;
        }
    }
 //----------------------------------------------------
   if ( !RSTATION_STALL->stallUp && !CMPLT_STALL->stallBubble )
   {

       //maskBit =  thrdBits.BITS & (thrdBits.hdPtr); // Moves 1 for (thrdBits.hdPtr - 1) places
       for ( i = 0; i < S_WIDTH; i++)
        {
         if (INPUT->inst_a[i] > 0 ) 
         {
          discardThrd = 0;
        //     fprintf(stderr,"Dis Bits = %d, mask = %d rrp_thrdID = %d completeBit = %d\n", thrdBits.BITS, maskBit, INPUT->thrdID[i], thrdPC_Q.completeBit);
          if ( thrdPC_Q.completeBit ) 
          {
           //  if (cycle_count > 9318646 )
            //       fprintf(stderr," Dispatch bits = %d PC = %d ID = %d  rd_new = %d slot = %d mask = %d, bits.tail = %d bits.hd = %d\n", thrdBits.BITS, INPUT->regs_PC[i], INPUT->thrdID[i], INPUT->rd_new[i],  regs_cp.instWindowSlot[ INPUT->rd_new[i] ], maskBit, INPUT->thrdBitPtr[i], thrdBits.hdPtr ); 
              //discardThrd =  (thrdBits.BITS  & maskBit) ^ ((INPUT->thrdID[i] & maskBit) >> (thrdBits.hdPtr-1)); // Flushout the Bad Path
              //discardThrd =  ((thrdBits.BITS  & thrdBits.hdPtr) != (INPUT->thrdID[i] & (thrdBits.hdPtr))); // Flushout the Bad Path
              discardThrd =  !thrdPC_Q.valid[(INPUT->thrdID[i])];
                  // fprintf(stderr," Discard bits = %d  ID = %d  rd_new = %d slot = %d mask = %d, bits.tail = %d bits.hd = %d\n", thrdBits.BITS, INPUT->thrdID[i], INPUT->rd_new[i],  regs_cp.instWindowSlot[ INPUT->rd_new[i] ], maskBit, thrdBits.tailPtr, thrdBits.hdPtr ); 
              if (discardThrd) 
              {
                   //if (cycle_count > 18676985 )
                    //   fprintf(stderr," discard cmp stall %d\n", INPUT->rd_new[i]);
                   regs_busyBits [ INPUT->rd_new[i] ] = 0;
            // if (cycle_count > 9654800)
            // if (cycle_count > 9318646 )
             //      fprintf(stderr," Discard bits = %d PC = %d ID = %d  rd_new = %d slot = %d mask = %d, bits.tail = %d bits.hd = %d\n", thrdBits.BITS, INPUT->regs_PC[i], INPUT->thrdID[i], INPUT->rd_new[i],  regs_cp.instWindowSlot[ INPUT->rd_new[i] ], maskBit, INPUT->thrdBitPtr[i], thrdBits.hdPtr ); 
                 // thrd_Active();

                //   thrdPC_Q.valid[INPUT->thrdID[i]] = 0;  // Reset Valid Bit of the ThrdID

               //------------ Thread Count Decrement---------
               if ( thrdPC_Q.threadCount[INPUT->thrdID[i]] > 0 )
                {   
                  thrdPC_Q.threadCount[INPUT->thrdID[i]]--;
                // fprintf(stderr,"Disp. thrdID Count %d  ",thrdPC_Q.threadCount[INPUT->thrdID[i]]);

                  if ( thrdPC_Q.threadCount[INPUT->thrdID[i]] == 0 )
                  {
                    //fprintf(stderr,"\n thrdID %d Dispatch FREE ",INPUT->thrdID[i]);
                   /*for (unsigned k=1; k <= (THREAD_LEVEL); k++) // Lo & Hi
                   {
                      for (unsigned int j=0; j<(MD_NUM_IREGS + 1); j++) // Lo & Hi
                      {
                          rRegPtr[k][INPUT->thrdID[i]].valid[j] = 0;
                      }
                   }*/
                     //thrdPC_Q.thrdParentID[INPUT->thrdID[i]] = 0;
                    // thrdPC_Q.thrdParentLevel[INPUT->thrdID[i]] = 0;
                   //  threadBusyList.remove( INPUT->thrdID[i]);
                     thrdPC_Q.busy[INPUT->thrdID[i]] = 0; 
                     thrdPC_Q.bitPtr[INPUT->thrdID[i]] = 0; 
                  //  if( cycle_count > 9127500) 
                   //   fprintf(stderr," Reset discard %d\n", reoBufferPtr->thrdID);
                   }
                 }
               //------------End of Thread Count Decrement---------
              } // Free the rename register
           } // if completeBit

        if ( !discardThrd )
        {
        //   fprintf(stderr," Dispatch PC = %d Pred PC = %d cycle = %d\n", OUTPUT->regs_PC[i], OUTPUT->pred_PC[i], cycle_count);
     //      fprintf(stderr," Entry \n");
     //      rRegPtr[INPUT->thrdBitPtr[i] ][INPUT->thrdID[i]].ptr [ INPUT->rd[i] ]= INPUT->rd_new[i];
      //     rRegPtr[INPUT->thrdBitPtr[i] ][INPUT->thrdID[i]].valid [ INPUT->rd[i] ]=  1; //INPUT->wr_valid[i];
       //    rRegPtr[INPUT->thrdBitPtr[i] ][INPUT->thrdID[i]].bitPtr [ INPUT->rd[i] ]=  INPUT->thrdBitPtr[i];

           reoBufferPtr = &reoBuffer[headPtr];
           regs_cp.instWindowSlot[ INPUT->rd_new[i] ] = headPtr;    // Used during the Issue Check - Dependency

         //------Check if the Reg Data is Valid to allocate the instruction nin the Ready Q------

          if ( INPUT->inOrder[i] )// To skip the loads from issuing ahead of stores 
          {
               issReadyQ.swID = headPtr;
               issReadyQ.ldFLAG = 0;  //Store the most recent Store Slot Id.}
              //***Store Buffer Allocation******
               reoBufferPtr->sw_reoID = sw_tPtr;  // Store Buffer
               sw_buffer[ sw_tPtr ].reoID = headPtr;  //ReoID of Reorder Buffer
               sw_buffer[ sw_tPtr ].thrdID = INPUT->thrdID[i];  //ReoID of Reorder Buffer
               sw_buffer[ sw_tPtr ].thrdBitPtr = INPUT->thrdBitPtr[i];  //ReoID of Reorder Buffer
               sw_buffer[ sw_tPtr ].sw_uniqueID = sw_uniqueID++ ;  //
               sw_buffer[ sw_tPtr ].pred_sw_addr = INPUT->ld_pred_addr[i];  //ReoID of Reorder BufferINPUT->regs_PC[i]; //
               sw_buffer[ sw_tPtr ].valid = 1;  //
               sw_buffer[ sw_tPtr ].sw_dataValid = 0;  //
               sw_buffer[ sw_tPtr ].sw_addr = 0;  //
               sw_tPtr++;  \
               if ((unsigned)sw_tPtr >= REORDER_WIDTH) \
                 sw_tPtr = 0; \
          }
          //********Load Allocation*******
          if ( INPUT->lD[i] )
          { 
              reoBufferPtr->ld_reoID = ld_tPtr;  //
              reoBufferPtr->ld_pred_addr = INPUT->ld_pred_addr[i];  
              reoBufferPtr->thrdID = INPUT->thrdID[i];//Instr. Addr.
              reoBufferPtr->thrdBitPtr = INPUT->thrdBitPtr[i];  // Thread ID

              ld_buffer[ ld_tPtr ].reoID = headPtr;  //
              ld_buffer[ ld_tPtr ].valid = 1;  //
              ld_buffer[ ld_tPtr ].ld_addr = 0;  //
              ld_buffer[ ld_tPtr ].sw_uniqueID = 0;  //
              ld_buffer[ ld_tPtr ].ld_fwd = 0;  //
              ld_buffer[ ld_tPtr ].is_lw = 0;  //
              ld_buffer[ ld_tPtr ].is_lh = 0;  //
              ld_buffer[ ld_tPtr ].is_lb = 0;  //
              ld_buffer[ ld_tPtr ].is_signed = 0;  //
              ld_buffer[ ld_tPtr ].mem_violation = 0;  //
              ld_buffer[ ld_tPtr ].mem_recover = 0;  //
              ld_buffer[ ld_tPtr ].sw_pc = 0;  //
              ld_buffer[  ld_tPtr ].match_exists = 0;
              ld_tPtr++;  \
              if ( (unsigned) ld_tPtr >= REORDER_WIDTH) \
                 ld_tPtr = 0; \
          }

	  if ( INPUT->lD[i] && !ld_bypassLogic()/*issReadyQ.ldFLAG*/ )  // If Load Instr and there exists a previous uncompleted Store
          {
          //      if (cycle_count > 53663300)
           //     fprintf( stderr," Dispatch reo = %d valid %d = %d \n", headPtr, INPUT->rt[i], regs_cp.valid_R[ INPUT->rt[i] ]);
          	reoBufferPtr->wakeUp = regs_cp.valid_R[ INPUT->rt[i] ]; //If Not Valid; Ld has to wait for 2 instr. to finish ( store and a dep. dest reg. slot) // Store the Dependent Slot ID of the Src Operands
               // fprintf(stderr," Ld Reo %d sw reo %d\n", headPtr, issReadyQ.swID);
                wakeUpPtr = &wakeUpTbl[ issReadyQ.swID ];
		wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = headPtr;  // Issue Load upon completing all the stores
		wakeUpPtr->regs_PC[ wakeUpPtr->slotLength ] = INPUT->regs_PC[i];  // Issue Load upon completing all the stores
		wakeUpPtr->rd_new[ wakeUpPtr->slotLength ] = INPUT->rd_new[i];  // Issue Load upon completing all the stores
		wakeUpPtr->thrdID[ wakeUpPtr->slotLength ] = INPUT->thrdID[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->slotLength++;
                wakeUpPtr->valid = 1; 

                //--------Check if Rt is Valid for Loads------------
		if (  (regs_cp.valid_R[ INPUT->rt[i] ]  == 0) ) 
		{
                  wakeUpPtr = &wakeUpTbl[ regs_cp.instWindowSlot[ INPUT->rt[i] ] ];
                  wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = headPtr;  // Issue Load upon completing all the stores
		  wakeUpPtr->regs_PC[ wakeUpPtr->slotLength ] = INPUT->regs_PC[i];  // Issue Load upon completing all the stores
		  wakeUpPtr->rd_new[ wakeUpPtr->slotLength ] = INPUT->rd_new[i];  // Issue Load upon completing all the stores
		  wakeUpPtr->thrdID[ wakeUpPtr->slotLength ] = INPUT->thrdID[i];  // Issue Load upon completing all the stores
		  wakeUpPtr->slotLength ++;
		  wakeUpPtr->valid = 1;
                }
	  }
          else if (  (regs_cp.valid_R[ INPUT->rs[i] ]  == 1) && \
                        (regs_cp.valid_R[ INPUT->rt[i] ] == 1) )//1VALID( INPUT->rt[i] ) )
          {
        //        if (cycle_count > 53663300)
         //       fprintf( stderr," Dispatch reo = %d valid %d = %d \n", headPtr, INPUT->rt[i], regs_cp.valid_R[ INPUT->rt[i] ]);
          	issReadyQ.slotID[ issReadyQ.hdPtr ] = headPtr;  // Store the Inst. Window Slot ID directly in the Ready Q
          	issReadyQ.thrdID[ issReadyQ.hdPtr ] = INPUT->thrdID[i] ;  // Store the Inst. Window Slot ID directly in the Ready Q
                issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                issReadyQ.discard[ issReadyQ.hdPtr ] = 0;
                issReadyQ.hdPtr++; 
                if ( issReadyQ.hdPtr == REORDER_WIDTH )
                      issReadyQ.hdPtr = 0;
                if ( issReadyQ.hdPtr == issReadyQ.tailPtr )
	      	   { OUTPUT->stallUp = 1; issQStallCntr++; }
	  }
          else if (  (regs_cp.valid_R[ INPUT->rs[i] ]  == 0) && \
                        (regs_cp.valid_R[ INPUT->rt[i] ] == 0)  ) //1VALID( INPUT->rt[i] ) )
          {
          	reoBufferPtr->wakeUp = 0;  // Store the Dependent Slot ID of the Src Operands
                wakeUpPtr = &wakeUpTbl[ regs_cp.instWindowSlot[ INPUT->rs[i] ] ];
		wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = headPtr;  // Issue Load upon completing all the stores
		wakeUpPtr->regs_PC[ wakeUpPtr->slotLength ] = INPUT->regs_PC[i];  // Issue Load upon completing all the stores
		wakeUpPtr->rd_new[ wakeUpPtr->slotLength ] = INPUT->rd_new[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->thrdID[ wakeUpPtr->slotLength ] = INPUT->thrdID[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->slotLength++;
                wakeUpPtr->valid = 1; 

                wakeUpPtr = &wakeUpTbl[ regs_cp.instWindowSlot[ INPUT->rt[i] ] ];
		wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = headPtr;  // Issue Load upon completing all the stores
		wakeUpPtr->regs_PC[ wakeUpPtr->slotLength ] = INPUT->regs_PC[i];  // Issue Load upon completing all the stores
		wakeUpPtr->rd_new[ wakeUpPtr->slotLength ] = INPUT->rd_new[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->thrdID[ wakeUpPtr->slotLength ] = INPUT->thrdID[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->slotLength++;
                wakeUpPtr->valid = 1; 

          }
          else if (  (regs_cp.valid_R[ INPUT->rs[i] ]  == 0)  ) 
          {
          	reoBufferPtr->wakeUp = 1;  // Store the Dependent Slot ID of the Src Operands
               /*if ( cycle_count > 46000 && headPtr == 2695)
               {
                 fprintf(stderr," dep reo %d\n",  regs_cp.instWindowSlot[ INPUT->rs[i] ]); 
               }*/
                wakeUpPtr = &wakeUpTbl[ regs_cp.instWindowSlot[ INPUT->rs[i] ] ];
		wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = headPtr;  // Issue Load upon completing all the stores
		wakeUpPtr->regs_PC[ wakeUpPtr->slotLength ] = INPUT->regs_PC[i];  // Issue Load upon completing all the stores
		wakeUpPtr->rd_new[ wakeUpPtr->slotLength ] = INPUT->rd_new[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->thrdID[ wakeUpPtr->slotLength ] = INPUT->thrdID[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->slotLength++;
                wakeUpPtr->valid = 1; 
	  }
          else if (  (regs_cp.valid_R[ INPUT->rt[i] ]  == 0) ) 
          {
          	reoBufferPtr->wakeUp = 1;  // Store the Dependent Slot ID of the Src Operands
                wakeUpPtr = &wakeUpTbl[ regs_cp.instWindowSlot[ INPUT->rt[i] ] ];
              // if ( cycle_count > 990 )
             //    fprintf(stderr," SlotID = %d wPtr = %d %d\n", headPtr, regs_cp.instWindowSlot[ INPUT->rt[i] ], INPUT->rt[i] );
		wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = headPtr;  // Issue Load upon completing all the stores
		wakeUpPtr->regs_PC[ wakeUpPtr->slotLength ] = INPUT->regs_PC[i];  // Issue Load upon completing all the stores
		wakeUpPtr->rd_new[ wakeUpPtr->slotLength ] = INPUT->rd_new[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->thrdID[ wakeUpPtr->slotLength ] = INPUT->thrdID[i];  // Issue Load upon completing all the stores
	        wakeUpPtr->slotLength++;
                wakeUpPtr->valid = 1; 
		//wakeUpTbl[ regs_cp.instWindowSlot[ INPUT->rt[i] ] ].valid[ headPtr ] = 1;
	  }


         //------------------------------------------------------------------------------------

          reoBufferPtr->busy = 1;
          reoBufferPtr->completed = 0;
          reoBufferPtr->finished = 0;
          reoBufferPtr->issued = 0;
          reoBufferPtr->misspeculated = 0;

          reoBufferPtr->rs = INPUT->rs[i];
          reoBufferPtr->rt = INPUT->rt[i];
          
          reoBufferPtr->rd_new = INPUT->rd_new[i];
          reoBufferPtr->rd_old = INPUT->rd_old[i];
          reoBufferPtr->rd = INPUT->rd[i];

          reoBufferPtr->inOrder = INPUT->inOrder[i];//Destination operations afer renaming.
          reoBufferPtr->exception = INPUT->exception[i];//Destination operations afer renaming.
          reoBufferPtr->lD = INPUT->lD[i];//Destination operations afer renaming.
          reoBufferPtr->alu = INPUT->alu[i];//Destination operations afer renaming.
          reoBufferPtr->mult = INPUT->mult[i];//Destination operations afer renaming.
          reoBufferPtr->readLO = INPUT->readLO[i];//Destination operations afer renaming.
          reoBufferPtr->readHI = INPUT->readHI[i];//Destination operations afer renaming.
          reoBufferPtr->br = INPUT->br[i];//Destination operations afer renaming.
 
          reoBufferPtr->regs_PC = INPUT->regs_PC[i];
          reoBufferPtr->thrdID = INPUT->thrdID[i];//Instr. Addr.
          reoBufferPtr->thrdBitPtr = INPUT->thrdBitPtr[i];  // Thread ID
          reoBufferPtr->thrdIDValid = INPUT->thrdIDValid[i];//Instr. Addr.
          reoBufferPtr->followBr = INPUT->followBr[i]; // Mask Bit on/off
          //if ( reoBufferPtr->regs_PC == 4201888 )
          //  fprintf(stderr," Dispatch followBR = %d\n", reoBufferPtr->followBr );
      //    if ( INPUT->thrdIDValid[i] ) 
       //     thrdPC_Q.threadCount[INPUT->thrdID[i]]++; // Increment the thread count
          reoBufferPtr->pred_PC = INPUT->pred_PC[i];  //regs.regs_PC;
          //fprintf(stderr," Dispatch Pred_PC = %d\n", OUTPUT->pred_PC[i] );
          reoBufferPtr->stack_recover_idx = INPUT->stack_recover_idx[i];  //regs.regs_PC;
          reoBufferPtr->dir_update = INPUT->dir_update[i];  //regs.regs_PC;
          reoBufferPtr->regs_NPC = 0; // Calculated at Finish
          reoBufferPtr->inst_a = INPUT->inst_a[i];
          reoBufferPtr->inst_b = INPUT->inst_b[i];

          reoStallEnable = 1;                                                                                                                                                                                                
          if ( ( (headPtr + 1) % REORDER_WIDTH ) != tailPtr )
             headPtr = ( (headPtr + 1) % REORDER_WIDTH );
         else
             headPtr = tailPtr;//Reorder Buffer Full, but will start to load from the tail ptr.
        } // if !discard
       } // if Inst.a > 0

      } // End of For Loop
   }
//----------Check ReOrder Buffer-----------------------
    if ( headPtr != tailPtr  )
    {
     k = headPtr;
     for ( int t = 0; t < S_WIDTH; t++)
     {
       k = ( (k + 1) % REORDER_WIDTH );
      if ((unsigned) k == tailPtr )
       {
	    reoStallCntr++;
            OUTPUT->stallUp = 1;
            break;
       }
      } //end of For loop
    }
    else if ( reoStallEnable ) // Can be the End of the Circular or Beginning
    {  //Stall Up
     /*      fprintf( stderr,"\nCycle count %u", cycle_count);
           reoStallCntr++;
           OUTPUT->stallUp = 1;*/
       freeCnt = 0;
       for ( k=0; (unsigned)k < REORDER_WIDTH; k++)
       {
         if ( reoBuffer[k].busy == 0 )
         {
            freeCnt ++;
            if (freeCnt == S_WIDTH) break;//Break the for loop if 4 free registers are found
         }
       }
       if ( freeCnt < S_WIDTH )  //Less reoBuffers available
        {
	    reoStallCntr++;
            OUTPUT->stallUp = 1;
        }
    }
  
}

//*******ISSUE STAGE*********
void issue_main ()
{   
   inst_issue* OUTPUT = &next_data_ptr->inst_is;
   inst_issue* PREV_OUTPUT = &cur_data_ptr->inst_is;
  // inst_issue* ISS_STALL = &cur_data_ptr->inst_is;
   inst_execute* ISS_STALL = &cur_data_ptr->inst_ex;
   inst_complete* CMPLT_STALL= &cur_data_ptr->inst_cp;


  /* bool alu_fu_available = 0;
   bool mul_fu_available = 0;
   bool br_fu_available = 0;
   bool ld_fu_available = 0;
   bool ot_fu_available = 0;
*/
   issCnt = 0; 
   wdTimer1 = 0;
   otherIssCntr = 0;
   aluIssCntr = 0;
   ldIssCntr = 0;
   brIssCntr = 0;
   mulIssueCntr = 0;
//  inst_rstation* INPUT = &cur_data_ptr->inst_rs;
//-----------ISSUE LOGIC------------------------------------
     //{
      //  if ( issReadyQ.valid[ issRQ ] && cycle_count > 53663300 )
       //     fprintf (stderr,"Cycle = %d  ReoID = %d tPtr = %d hPtr = %d\n", cycle_count, issReadyQ.slotID[ issRQ ], issReadyQ.tailPtr, issReadyQ.hdPtr); 
    // }

    //-------Read from the READY Queue and Issue the ready insns to the respect queues for execution------
    if ( !CMPLT_STALL->stallBubble )
     {
       while ( issCnt < ISSUE_WIDTH && issReadyQ.valid[ issReadyQ.tailPtr ] /*&& issReadyQ.excep == 0 */  )
       {
        //Watch Dog timer
          
          wdTimer1 ++;
      	  issID = issReadyQ.slotID[ issReadyQ.tailPtr ]; //issuePtr;
          reoBufferPtr = &reoBuffer[issID];

          if ( wdTimer1 > (ISSUE_WIDTH + 4) )
          {
            
            fprintf (stderr,"ISSUE EXIT \nCycle = %d timer = %d issCnt = %d ReoID = %d tPtr = %d hPtr = %d\n", cycle_count, wdTimer1, issCnt, issID, issReadyQ.tailPtr,  issReadyQ.hdPtr );
           fprintf (stderr,"Busy = %d not_valid = %d bitPtr = %d thrdID = %d\n",reoBufferPtr->busy, !thrdPC_Q.valid[reoBufferPtr->thrdID], reoBufferPtr->thrdBitPtr, reoBufferPtr->thrdID );
            print_reorder();
 	    print_regs();
            exit(0);
	  }
        /*  if (cycle_count > 1740)
           {fprintf (stderr,"Busy = %d valid = %d bitPtr = %d thrdID = %d PC = %d\n",reoBufferPtr->busy, thrdPC_Q.valid[reoBufferPtr->thrdID], reoBufferPtr->thrdBitPtr, reoBufferPtr->thrdID, reoBufferPtr->regs_PC );
            fprintf (stderr,"Cycle = %d timer = %d issCnt = %d ReoID = %d tPtr = %d hPtr = %d\n", cycle_count, wdTimer1, issCnt, issID, issReadyQ.tailPtr,  issReadyQ.hdPtr );
        }*/

         // i = issuePtr;
       //----------Check if the Instruction causes an Exception; Enforce Precise Exception-------------------------------
          if ( reoBufferPtr->busy == 1 && reoBufferPtr->issued == 0 /*|| reoBufferPtr->misspeculated*/ )
          {    
              issue_ptr = NULL; 
        //                if (cycle_count > 600 )
         //               fprintf( stderr, " issue ID = %d \n", issID );
     /*                   OUTPUT->reoID[issCnt ] = issID;  // Reorder ID
                        OUTPUT->spec[issCnt ] = reoBufferPtr->misspeculated;  // Reorder ID
                        //        fprintf(stderr,"\n reo ISSUE = %d\t", OUTPUT->reoID[issCnt] );
                        OUTPUT->rd[issCnt ] = reoBufferPtr->rd;
                        OUTPUT->rd_new[issCnt ] = reoBufferPtr->rd_new;
                        OUTPUT->rd_old[issCnt ] = reoBufferPtr->rd_old;

                        OUTPUT->inst_a[issCnt ] = reoBufferPtr->inst_a;
                        OUTPUT->inst_b[issCnt ] = reoBufferPtr->inst_b;
                        OUTPUT->regs_PC[issCnt ] = reoBufferPtr->regs_PC;
      */                   // -----------Set Issued------------------------
                        //reoBufferPtr->issued= 1;
                if ( (reoBufferPtr->lD == 1 || reoBufferPtr->inOrder == 1 ) )  // ISSUE for Load or Store Instruction
                   //-----------Load Instructions---------------
                   {
                        issue_ptr = &ls_insn;
                //        ls_insn.issQ[ ls_insn.tailPtr ] = issID;
                 //       ls_insn.tailPtr ++;
                  //      if (ls_insn.tailPtr >= REORDER_WIDTH)
                   //       ls_insn.tailPtr = 0;
                   }
                 else if ( reoBufferPtr->br == 1/* && !FINISH_STALL->alu_StallUp */)
                  { //---------Branch Instructions--------------
                        issue_ptr = &br_insn;
            //            br_insn.issQ[ br_insn.tailPtr ] = issID;
             //           br_insn.tailPtr ++;
              //          if (br_insn.tailPtr >= REORDER_WIDTH)
               //           br_insn.tailPtr = 0;
                  }
                 else if ( reoBufferPtr->alu == 1/* && !FINISH_STALL->alu_StallUp */)
                  {// ALU type instructions 
                        issue_ptr = &alu_insn;
        //                alu_insn.issQ[ alu_insn.tailPtr ] = issID;
         //               alu_insn.tailPtr ++;
          //              if (alu_insn.tailPtr >= REORDER_WIDTH)
           //               alu_insn.tailPtr = 0;
                  } //---End of Alu Instruction Check
                 else if ( reoBufferPtr->mult == 1/* && !FINISH_STALL->mul_StallUp*/ && !(reoBufferPtr->readLO | reoBufferPtr->readHI) )
                  {
                        issue_ptr = &mul_insn;
                     //  Multiply or Divide instructions; MFLO & MFHI are placed in the other function queue. 
    //                    mul_insn.issQ[ mul_insn.tailPtr ] = issID;
     //                   mul_insn.tailPtr ++;
      //                  if (mul_insn.tailPtr >= REORDER_WIDTH)
       //                   mul_insn.tailPtr = 0;
                  } //---End of mul/div Instruction Check
                 else 
                  {
                        issue_ptr = &ot_insn;
                     // All other instructions 
//                        ot_insn.issQ[ ot_insn.tailPtr ] = issID;
 //                       ot_insn.tailPtr ++;
  //                      if (ot_insn.tailPtr >= REORDER_WIDTH)
   //                       ot_insn.tailPtr = 0;
                  }//-------End of Order Check Issue--------------------
                issue_ptr->issQ[ issue_ptr->tailPtr ] = issID;
                issue_ptr->thrdID[ issue_ptr->tailPtr ] = reoBufferPtr->thrdID;
                issue_ptr->regsPC[ issue_ptr->tailPtr ] = reoBufferPtr->regs_PC;
                issue_ptr->rd_new[ issue_ptr->tailPtr ] = reoBufferPtr->rd_new;
                issue_ptr->valid[ issue_ptr->tailPtr ] = 1;
                issue_ptr->discard[ issue_ptr->tailPtr ] = 0;
        //        if (cycle_count > 2240 )
         //          fprintf ( stderr, " issID = %d tailPtr = %d \n", issID, issue_ptr->tailPtr);

                issue_ptr->tailPtr ++;

                if (issue_ptr->tailPtr >= REORDER_WIDTH)
                   issue_ptr->tailPtr = 0;

         	issReadyQ.valid[ issReadyQ.tailPtr ] = 0;
                issReadyQ.tailPtr++;
                if (  (unsigned) issReadyQ.tailPtr == REORDER_WIDTH )
	          issReadyQ.tailPtr = 0;
                issCnt ++;
        } // if Busy and Not Issued;
        else if ( reoBufferPtr->busy == 0/* && !thrdPC_Q.valid[reoBufferPtr->thrdID]*/ && reoBufferPtr->thrdBitPtr > 0/*|| reoBufferPtr->misspeculated*/ )
          {
         	issReadyQ.valid[ issReadyQ.tailPtr ] = 0;
                issReadyQ.tailPtr++;
                if (  (unsigned) issReadyQ.tailPtr == REORDER_WIDTH )
	          issReadyQ.tailPtr = 0;
                issCnt ++;
          }
    //    else if ( reoBufferPtr->busy == 1 /*&& reoBufferPtr->issued == 1 */ && !thrdPC_Q.valid[reoBufferPtr->thrdID] && reoBufferPtr->thrdBitPtr > 0/*|| reoBufferPtr->misspeculated*/ )
        else if ( issReadyQ.discard )
          { /* Must have overlapped before the recovery of the old thread */
             //   if (cycle_count > 54420261 )
              //    fprintf(stderr," Discard Reo %d\n", issID);
         	issReadyQ.valid[ issReadyQ.tailPtr ] = 0;
                issReadyQ.tailPtr++;
                if (  (unsigned) issReadyQ.tailPtr == REORDER_WIDTH )
	          issReadyQ.tailPtr = 0;
                issCnt ++;
          }

     } //------End of while Loop -------------------

  issCnt = 0;
  issue_ptr = NULL; 
  static int issue_rr_ptr = 0; // Round Robin Issue Pointer
  int issueQEmpty = 0; 
  bool issEmpty[5];
  issEmpty[0] = 0;
  issEmpty[1] = 0;
  issEmpty[2] = 0;
  issEmpty[3] = 0;
  issEmpty[4] = 0;

    // fprintf(stderr, " cycle = %d \n", cycle_count);

//  while ( issCnt < ISSUE_WIDTH )
 // {
  //  if ( ISS_STALL->stallUp[issCnt] )
   //  {/* Assign the previous output as there is a stall in this bus */ 
    //   fprintf(stderr," ReIssue Bus = %d nextReoID = %d ReoID = %d at cycle = %u\n", issCnt, OUTPUT->reoID[issCnt], PREV_OUTPUT->reoID[issCnt], cycle_count);
//       OUTPUT->reoID[issCnt ] = PREV_OUTPUT->reoID[issCnt ];  // Reorder ID
  //     OUTPUT->spec[issCnt ] = PREV_OUTPUT->spec[issCnt ];  // 
   //    OUTPUT->rd[issCnt ] = PREV_OUTPUT->rd[issCnt ];
    //   OUTPUT->rd_new[issCnt ] = PREV_OUTPUT->rd_new[issCnt ];
     //  OUTPUT->rd_old[issCnt ] = PREV_OUTPUT->rd_old[issCnt ];
      // OUTPUT->inst_a[issCnt ] = PREV_OUTPUT->inst_a[issCnt ];
      // OUTPUT->inst_b[issCnt ] = PREV_OUTPUT->inst_b[issCnt ];
       //OUTPUT->regs_PC[issCnt ] = PREV_OUTPUT->regs_PC[issCnt ];
     //}
    //issCnt++;
  // }
 // -------SET NEXT ISSUE OUTPUTS-------
    for ( i = 0;  (unsigned) i < ISSUE_WIDTH; i++)
       {
      //   if ( ISS_STALL->stallUp[i] )
     //      fprintf( stderr,"cycle = %u Iss stall = %d \n", cycle_count, ISS_STALL->stallUp[i] );
             //next_data_ptr->regfilePORTS.rs_addr[ i ] = 0; //SET Read Ports of RF 
             // next_data_ptr->regfilePORTS.rt_addr[i ] = 0; 
        if ( !ISS_STALL->stallUp[i] &&  OUTPUT->regs_PC[i] != 0 )
         {
              OUTPUT->reoID[i ] = 0;  // Reorder ID
              OUTPUT->rd[i ] = 0;
              OUTPUT->rs[i ] = 0;
              OUTPUT->rt[i ] = 0;

              OUTPUT->rd_new[i] = 0; 
              OUTPUT->rd_old[i] = 0;
              OUTPUT->spec[i] = 0;

              OUTPUT->inst_a[i] = 0;
              OUTPUT->inst_b[i] = 0;
              OUTPUT->regs_PC[i] = 0;
              OUTPUT->thrdID[i ] = 0;
         }
         else if ( ISS_STALL->stallUp[i] && OUTPUT->regs_PC[i] == 0 )
         {
    //     fprintf(stderr," COpy Bus = %d nextReoID = %d ReoID = %d at cycle = %u\n", issCnt, OUTPUT->reoID[issCnt], PREV_OUTPUT->reoID[issCnt], cycle_count);
           if ( reoBuffer[PREV_OUTPUT->reoID[i]].busy && reoBuffer[PREV_OUTPUT->reoID[i]].regs_PC == PREV_OUTPUT->regs_PC[i] && reoBuffer[PREV_OUTPUT->reoID[i]].rd_new == PREV_OUTPUT->rd_new[i] )
           {
              OUTPUT->regs_PC[i ] = PREV_OUTPUT->regs_PC[i];
              OUTPUT->reoID[i ] = PREV_OUTPUT->reoID[i];  // Reorder ID
              OUTPUT->spec[i ] = PREV_OUTPUT->spec[i];  // 
              OUTPUT->rd[i ] = PREV_OUTPUT->rd[i];
              OUTPUT->rd_new[i] = PREV_OUTPUT->rd_new[i];
              OUTPUT->rd_old[i] = PREV_OUTPUT->rd_old[i];
              OUTPUT->inst_a[i] = PREV_OUTPUT->inst_a[i];
              OUTPUT->inst_b[i] = PREV_OUTPUT->inst_b[i];
              OUTPUT->thrdID[i ] = PREV_OUTPUT->thrdID[i];
           }
         } // else if
      } // end of for
 
    // for ( int issRQ = 0; issRQ < REORDER_WIDTH; issRQ++)
  issCnt = 0;
  while ( issCnt < ISSUE_WIDTH )
  { 
     //fprintf(stderr, " Iss stall = %d PC = %d \n", ISS_STALL->stallUp[issCnt], OUTPUT->regs_PC[issCnt] );
   if ( !ISS_STALL->stallUp[issCnt] &&  OUTPUT->regs_PC[issCnt] == 0 ) // Don't Set New OUTPUTS
   {
    // fprintf(stderr, " Iss stall = %d \n", ISS_STALL->stallUp[issCnt]);ke

    //Assign the FU type Pointers 
     switch ( issue_rr_ptr )
     {
       case 0:
         issue_ptr = &alu_insn; 
         break;
       case 1:
         issue_ptr = &mul_insn; 
         break;
       case 2:
         issue_ptr = &ls_insn; 
         break;
       case 3:
         issue_ptr = &br_insn; 
         break;
       case 4:
         issue_ptr = &ot_insn; 
        break;
       default:
         fprintf ( stderr, " No such Instruction Issue Handler Defined %d \n", issue_rr_ptr); 
        break;
      } // end of switch (issue_rr_ptr)

     //if (cycle_count > 2240 )
      // fprintf ( stderr, " outside isscnt = %d, type = %d hdPtr = %d valid = %d reoID = %d  \n",  issCnt, issue_rr_ptr, issue_ptr->hdPtr,
       //                                                                              issue_ptr->valid[issue_ptr->hdPtr], issue_ptr->issQ[issue_ptr->hdPtr]);

     if ( issue_ptr->hdPtr != issue_ptr->tailPtr && issue_ptr->valid[issue_ptr->hdPtr] && !issue_ptr->discard[issue_ptr->hdPtr] )
     {
       reoBufferPtr = &reoBuffer[ issue_ptr->issQ[issue_ptr->hdPtr] ];
       issue_ptr->valid[issue_ptr->hdPtr] = 0; // Invalidate

      // if (cycle_count > 53663300 )
   //    fprintf ( stderr, " isscnt = %d, type = %d reoID %d \n",  issCnt, issue_rr_ptr, OUTPUT->reoID[issCnt]); 
     if ( reoBufferPtr->thrdID == issue_ptr->thrdID[issue_ptr->hdPtr] && reoBufferPtr->regs_PC == issue_ptr->regsPC[issue_ptr->hdPtr] &&  reoBufferPtr->rd_new == issue_ptr->rd_new[issue_ptr->hdPtr] )
     { 
      //if (cycle_count > 1750 )
       //  fprintf ( stderr, " isscnt = %d, type = %d reoID %d \n",  issCnt, issue_rr_ptr, OUTPUT->reoID[issCnt]);
       OUTPUT->reoID[issCnt ] = issue_ptr->issQ[issue_ptr->hdPtr];  // Reorder ID
       OUTPUT->spec[issCnt ] = reoBufferPtr->misspeculated;  // 
       OUTPUT->rd[issCnt ] = reoBufferPtr->rd;
       OUTPUT->rd_new[issCnt ] = reoBufferPtr->rd_new;
       OUTPUT->rd_old[issCnt ] = reoBufferPtr->rd_old;
       OUTPUT->inst_a[issCnt ] = reoBufferPtr->inst_a;
       OUTPUT->inst_b[issCnt ] = reoBufferPtr->inst_b;
       OUTPUT->regs_PC[issCnt ] = reoBufferPtr->regs_PC;
       OUTPUT->thrdID[issCnt ] = reoBufferPtr->thrdID;
      }
       issue_ptr->hdPtr ++;
       if ( issue_ptr->hdPtr >= REORDER_WIDTH )
         issue_ptr->hdPtr = 0;

        issCnt++;
       if ( issCnt == ISSUE_WIDTH ) break;
     }
     else
     {
       issEmpty[ issue_rr_ptr ] = 1;
     }
     issue_rr_ptr++;
     if (issue_rr_ptr == 5 ) issue_rr_ptr = 0; // Reset Round Robin Issue Pointer 
   }
  else
    {
       issCnt++;
       if ( issCnt == ISSUE_WIDTH ) break;
    } // If issue_bus has a stall

//   fprintf( stderr," cal. empty 0 = %d 1 = %d 2 = %d 3 = %d 4 = %d \n",issEmpty[0], issEmpty[1], issEmpty[2], issEmpty[3], issEmpty[4]);
    if ( (issEmpty[0] && issEmpty[1] && issEmpty[2] && issEmpty[3] && issEmpty[4]) == 1 ) {issue_rr_ptr = 0; break;} // Reset Round Robin Issue Pointer

   } // End of while
  }
 else //if cmp->stallBubble True
  {
    //--------Bubbles--------------------
     for ( int i = 0; i < ISSUE_WIDTH; i++)
     {
       OUTPUT->reoID[i] = 0;  // Reorder ID
       OUTPUT->spec[i] = 0;
       OUTPUT->rd[i] = 0;
       OUTPUT->rd_new[i] = 0;
       OUTPUT->rd_old[i] = 0;
       OUTPUT->inst_a[i] = 0;
       OUTPUT->inst_b[i] = 0;
       OUTPUT->regs_PC[i] = 0;
       OUTPUT->thrdID[i ] = 0;
     }
  } // end of cmp->stallBubble

                //-----No available slots----------
        
       //----------Check if the Instruction causes an Exception; Enforce Precise Exception-------------------------------
        /*  if ( (unsigned)  mulIssueCntr == MUL_WIDTH ||  (unsigned) ldIssCntr == LD_WIDTH ||  (unsigned) brIssCntr == BR_WIDTH ||  (unsigned) aluIssCntr == ALU_WIDTH ||  (unsigned) otherIssCntr == OT_WIDTH )
          {
          //    	fprintf(stderr,"\nMUL ISSUED = %d\t", mulIssueCntr);
	       if ( (unsigned) mulIssueCntr == MUL_WIDTH ) mulStallCntr++;
	       if ( (unsigned) aluIssCntr == ALU_WIDTH ) aluStallCntr++;
	       if ( (unsigned) brIssCntr == BR_WIDTH ) brStallCntr++;
	       if ( (unsigned) ldIssCntr == LD_WIDTH ) ldStallCntr++;
	       if ( (unsigned) otherIssCntr == OT_WIDTH ) otStallCntr++;
                break;   //Stall further issues
          }*/

  /* else
   { // Copy the previous outputs to current outputs.
      for ( i=0; i < ISSUE_WIDTH; i++)
       {
           OUTPUT->reoID[i] = RSTATION_STALL->reoID[i];  // Reorder ID
           OUTPUT->spec[i] = RSTATION_STALL->spec[ i ];  // Reorder ID
                //  fprintf(stderr,"\n reo ISSUE = %d\t", OUTPUT->reoID[issCnt] );
           OUTPUT->rd[i] = RSTATION_STALL->rd[ i ];
           OUTPUT->rd_new[i] = RSTATION_STALL->rd_new[ i ];
           OUTPUT->rd_old[i] = RSTATION_STALL->rd_old[ i ];

           OUTPUT->inst_a[i] = RSTATION_STALL->inst_a[ i ];
           OUTPUT->inst_b[i] = RSTATION_STALL->inst_b[ i ];
           OUTPUT->regs_PC[i] = RSTATION_STALL->regs_PC[ i ];
        }
     } */
}

//***********FINISH MODULES*******************/
void execute_main()
{   //Execution of Instruction
                                                                                                                                                                                                              
   bool alu_fu_available = 0;
   bool mul_fu_available = 0;
   bool br_fu_available = 0;
   bool ld_fu_available = 0;
   bool ot_fu_available = 0;
   unsigned int alu_width_cntr = 0;
   unsigned int mul_width_cntr = 0;
   unsigned int br_width_cntr = 0;
   unsigned int ld_width_cntr = 0;
   unsigned int ot_width_cntr = 0;
   //int finiID;

    inst_execute* OUTPUT = &next_data_ptr->inst_ex;
    inst_issue* INPUT = &cur_data_ptr->inst_is;
    inst_finish* FU_STALL = &cur_data_ptr->inst_fn;
    inst_complete* CMPLT_STALL= &cur_data_ptr->inst_cp;

   // reorderBufferPORTS* REO = &cur_data_ptr->reoPORTS;
   //reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;
   // reorder_busy* REOBUSY = &next_data_ptr->reoBusyPORTS;
   //reg_RR_bus* OUTPUT_RF = &next_data_ptr->regfilePORTS;

  //-----------Round Robin Issue Pointers-----------
   alu_width = alu_rr_ptr;
   mul_width = mul_rr_ptr;
   br_width = br_rr_ptr;
   ld_width = ld_rr_ptr;
   other_width = ot_rr_ptr;
 //**************INCREMENT THE FUNC POINTERS******************************
 //****The below for loops can be parallelized on OPEN MP directives*****
   for ( unsigned int alu_i = 0; alu_i < ALU_WIDTH; alu_i++ )
   {
      if ( !FU_STALL->alu_StallUp[alu_i] ) // Increment if No StallUp
      {
         alu_unit[alu_i].hdPtr = alu_unit[alu_i].hdPtr - 1 ;//Reorder Buffer Full, but will start to load from the tail ptr.
         if ( alu_unit[alu_i].hdPtr < 0 )
         { alu_unit[alu_i].hdPtr = (ALU_LAT - 1); } //reset Tail Ptr
                                                                                                                                                   
         (alu_unit[alu_i].tailPtr ) = alu_unit[alu_i].tailPtr - 1;;
         if ( alu_unit[alu_i].tailPtr < 0 )
          { alu_unit[alu_i].tailPtr  = (ALU_LAT - 1); }  //reset Tail Ptr
      }
    }
                                                                                                                                                   
   for ( unsigned int mul_i = 0; mul_i < MUL_WIDTH; mul_i++ )
   {
      if ( !FU_STALL->mul_StallUp[ mul_i] ) // Increment if No StallUp
      {
         mul_unit[mul_i].hdPtr = mul_unit[mul_i].hdPtr - 1 ;//Reorder Buffer Full, but will start to load from the tail ptr.
         if ( mul_unit[mul_i].hdPtr < 0 )
         { mul_unit[mul_i].hdPtr = (MUL_LAT - 1); } //reset Tail Ptr
                                                                                                                                                   
         (mul_unit[mul_i].tailPtr) = mul_unit[mul_i].tailPtr - 1;;
         if ( mul_unit[mul_i].tailPtr < 0 )
          { mul_unit[mul_i].tailPtr = (MUL_LAT - 1); }  //reset Tail Ptr
      }
    }

   for ( unsigned int br_i = 0; br_i < BR_WIDTH; br_i++ )
   {
      if ( !FU_STALL->br_StallUp[ br_i] ) // Increment if No StallUp
      {
         branch_unit[br_i].hdPtr = branch_unit[br_i].hdPtr - 1 ;//Reorder Buffer Full, but will start to load from the tail ptr.
         if ( branch_unit[br_i].hdPtr < 0 )
         { branch_unit[br_i].hdPtr = (BR_LAT - 1); } //reset Tail Ptr
                                                                                                                                                   
         (branch_unit[br_i].tailPtr) = branch_unit[br_i].tailPtr - 1;;
         if ( branch_unit[br_i].tailPtr < 0 )
          { branch_unit[br_i].tailPtr = (BR_LAT - 1); }  //reset Tail Ptr
      }
    }

   for ( unsigned int ld_i = 0; ld_i < LD_WIDTH; ld_i++ )
   {
      if ( !FU_STALL->ld_StallUp[ ld_i] ) // Increment if No StallUp
      {
         load_unit[ld_i].hdPtr = load_unit[ld_i].hdPtr - 1 ;//Reorder Buffer Full, but will start to load from the tail ptr.
         if ( load_unit[ld_i].hdPtr < 0 )
         { load_unit[ld_i].hdPtr = (LD_LAT - 1); } //reset Tail Ptr
                                                                                                                                                   
         (load_unit[ld_i].tailPtr) = load_unit[ld_i].tailPtr - 1;;
         if ( load_unit[ld_i].tailPtr < 0 )
          { load_unit[ld_i].tailPtr = (LD_LAT - 1); }  //reset Tail Ptr
      }
    }

  for ( unsigned int ot_i = 0; ot_i < OT_WIDTH; ot_i++ )
   {
      if ( !FU_STALL->ot_StallUp[ ot_i ] )
      {
         (other_unit[ot_i].hdPtr) = other_unit[ot_i].hdPtr - 1;//Reorder Buffer Full, but will start to load from the tail ptr.
         if ( other_unit[ot_i].hdPtr< 0 )
         { other_unit[ot_i].hdPtr = (OT_LAT - 1); }  //reset Tail Ptr
                                                                                                                                                   
         (other_unit[ot_i].tailPtr) = other_unit[ot_i].tailPtr - 1;
         if ( other_unit[ot_i].tailPtr < 0 )
         { other_unit[ot_i].tailPtr = (OT_LAT - 1); } //reset Tail Ptr
      }
    }

   reoBufferPtr = NULL; // Set reoBufferPtr to NULL

  //fprintf(stderr,"\n---------------Finish Stage-------------\n");

   for ( i = 0; (unsigned) i < ISSUE_WIDTH ; i++)
   {
      OUTPUT->stallUp[i] = 0; // Clear the Stall Signal
      if ( CMPLT_STALL->stallBubble )
       {
         INPUT->regs_PC[i] = 0;
         INPUT->inst_a[i] = 0;
       }

     //----------------------------------------------------
     if ( INPUT->regs_PC[i] == 0 ) continue; // skip this bus iteration and proceed the For loop
    //-----------------------------------------------------
      finiID = INPUT->reoID[i]; 
   //  if (cycle_count >20)
    //  fprintf(stderr," Test Issue[%d]= %u\n",i, finiID);
     // if ( REOBUSY->finished[ finiID ] == 0 && REOBUSY->busy[ finiID ] == 1 && /*REOBUSY->issued[ finiID ] == 1 && */(INPUT->inst_a[i] > 0) && !fu_stall )
      if (reoBuffer[finiID].finished == 0 && reoBuffer[finiID].busy == 1 &&/* reoBuffer[ PUT->reoID[i] ].issued == 1 &&*/ (INPUT->inst_a[i] > 0)/* && !fu_stall*/ )
      {
           reoBufferPtr = &reoBuffer[ finiID ];
          // if ( reoBufferPtr->misspeculated == 0 ) // Execute Only if it is Not Speculated
           {  //*****ISSUE ALU FUNCTION UNIT*******
	      if ( reoBufferPtr->alu ) 
              {
	       // alu_width_cntr = 0;
                alu_fu_available = 0;
                while ( alu_width_cntr < ALU_WIDTH ) 
                {
                  alu_width_cntr ++;
                  if ( !FU_STALL->alu_StallUp[alu_width] )
                  {
                   if ( reoBuffer[finiID].thrdID != INPUT->thrdID[i] || reoBuffer[finiID].regs_PC != INPUT->regs_PC[i] || reoBuffer[finiID].rd_new != INPUT->rd_new[i] ) break; 
                   alu_fu_available = 1;
                   reoBufferPtr->issued = 1; //Set Issued bit (wr_port at Dispatch stage disabled have to fix it)

                   alu_ptr = &alu_unit[alu_width].aluQ[ alu_unit[alu_width].hdPtr];
                   alu_ptr->reoID = finiID;
                   //if (cycle_count > 1750)
                    // fprintf(stderr,"ALU ISSUED[%d] Fu[%d]= %u pc = %u\n",i, alu_width, finiID, INPUT->regs_PC[i]);

                   alu_ptr->inst_a = INPUT->inst_a[i];
                   alu_ptr->inst_b = INPUT->inst_b[i];
                   alu_ptr->regs_PC = INPUT->regs_PC[i];
              	   alu_ptr->rd_new = INPUT->rd_new[i];
                   alu_ptr->spec = INPUT->spec[i];
              	   alu_ptr->rs_data = regs_cp.regs_R[ reoBufferPtr->rs ];
              	   alu_ptr->rt_data =  regs_cp.regs_R[ reoBufferPtr->rt ];
       //           fprintf(stderr," use alu_width %d\n", alu_width);

                   alu_width++;
                   if ( alu_width >= ALU_WIDTH )
                    alu_width = 0;
                   break;
                  }
                   // Issue Round Robin Pointer Update
                    alu_width++; // Find the FU that is free
                    if ( alu_width >= ALU_WIDTH )
                      alu_width = 0;

                } // end of while ( alu_width < ALU_WIDTH )

                //-----No available slots----------
                if ( !alu_fu_available )
                {
                  OUTPUT->stallUp[i] = 1;
                  //if (cycle_count > 1750)
                   // fprintf(stderr," ALU Stall Bus = %d Reo = %d at cycle = %u\n", i, finiID, cycle_count);
                //  alu_width_cntr = ALU_WIDTH; 
                  aluFUStallCntr++;
          	  //issReadyQ.slotID[ issReadyQ.hdPtr ] = finiID;  // Store the Inst. Window Slot ID directly in the Ready Q
                  //issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                  //issReadyQ.hdPtr++; 
                   //if ( issReadyQ.hdPtr == REORDER_WIDTH )
                    //  issReadyQ.hdPtr = 0;
                }

	      }
	      else if ( reoBufferPtr->mult && ! (reoBufferPtr->readLO | reoBufferPtr->readHI)  ) //---mul/div Function Unit---
              {// *******MUL/Div Instruction************
                mul_fu_available = 0;
                while (  mul_width_cntr < MUL_WIDTH )
                {
                    mul_width_cntr ++;
                  if ( !FU_STALL->mul_StallUp[ mul_width ] )
                  {
                   if ( reoBuffer[finiID].thrdID != INPUT->thrdID[i] || reoBuffer[finiID].regs_PC != INPUT->regs_PC[i] || reoBuffer[finiID].rd_new != INPUT->rd_new[i] ) break; 
                    mul_fu_available = 1;
                    reoBufferPtr->issued = 1; //Set Issued bit (wr_port at Dispatch stage disabled have to fix it)

                    mul_ptr = &mul_unit[mul_width].mulQ[ mul_unit[mul_width].hdPtr];
                    mul_ptr->reoID = finiID;
                    mul_ptr->inst_a = INPUT->inst_a[i];
                    mul_ptr->inst_b = INPUT->inst_b[i];
                    mul_ptr->regs_PC = INPUT->regs_PC[i];
               	    mul_ptr->rd_new = INPUT->rd_new[i];
                    mul_ptr->spec = INPUT->spec[i];
              	    mul_ptr->rs_data = regs_cp.regs_R[ reoBufferPtr->rs ];
              	    mul_ptr->rt_data =  regs_cp.regs_R[ reoBufferPtr->rt ];

                     mul_width++;
                     if ( mul_width >= MUL_WIDTH )
                      mul_width = 0;
                     break;
                   }
                    // Issue Round Robin Pointer Update
                   // mul_rr_ptr++;
                    //if ( mul_rr_ptr >= MUL_WIDTH )
                     // mul_rr_ptr = 0;
                    mul_width++;
                     if ( mul_width >= MUL_WIDTH )
                      mul_width = 0;

                 } // end of while ( mul_width < MUL_WIDTH )
                if ( !mul_fu_available )
                {
                  OUTPUT->stallUp[i] = 1;
                 // fprintf(stderr," mUL Bus = %d at cycle = %u\n", i, cycle_count);
                  mulFUStallCntr++;
          	 // issReadyQ.slotID[ issReadyQ.hdPtr ] = finiID;  // Store the Inst. Window Slot ID directly in the Ready Q
                  //issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                  //issReadyQ.hdPtr++; 
                   //if ( (unsigned) issReadyQ.hdPtr == REORDER_WIDTH )
                    //  issReadyQ.hdPtr = 0;
                }

	      }
              else if ( reoBufferPtr->br )
              { //******ISSUE BR FUNCTIONAL UNIT************
                br_fu_available = 0;
                //width_cntr = 0;
                while (  br_width_cntr < BR_WIDTH )
                {
                  br_width_cntr ++;
                 if ( !FU_STALL->br_StallUp[br_width] )
                 {
                   if ( reoBuffer[finiID].thrdID != INPUT->thrdID[i] || reoBuffer[finiID].regs_PC != INPUT->regs_PC[i] || reoBuffer[finiID].rd_new != INPUT->rd_new[i] ) break; 
                   br_fu_available = 1;
                   reoBufferPtr->issued = 1; //Set Issued bit (wr_port at Dispatch stage disabled have to fix it)
                   
                   br_ptr = &branch_unit[br_width].brQ[ branch_unit[br_width].hdPtr];

                   br_ptr->reoID = finiID;
                   br_ptr->inst_a = INPUT->inst_a[i];
                   br_ptr->inst_b = INPUT->inst_b[i];
                   br_ptr->regs_PC = INPUT->regs_PC[i];
                   br_ptr->rd_new = INPUT->rd_new[i];
                   br_ptr->spec = INPUT->spec[i];

                   br_ptr->rs_data = regs_cp.regs_R[ reoBufferPtr->rs ];
                   br_ptr->rt_data =  regs_cp.regs_R[ reoBufferPtr->rt ];

                   br_width++; // for the next Unit on the same issue grp
                     if ( br_width >= BR_WIDTH )
                       br_width = 0;
                    break;
                  }
                  br_width++;
                  if ( br_width >= BR_WIDTH )
                     br_width = 0;

                } // end of while ( ot_width < OT_WIDTH )

               if ( !br_fu_available )
                {
                  OUTPUT->stallUp[i] = 1;
                  //fprintf(stderr," br Bus = %d at cycle = %u\n", i, cycle_count);
          	  brFUStallCntr++;
          	  //issReadyQ.slotID[ issReadyQ.hdPtr ] = finiID;  // Store the Inst. Window Slot ID directly in the Ready Q
                  //issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                  //issReadyQ.hdPtr++; 
                   //if ( (unsigned) issReadyQ.hdPtr == REORDER_WIDTH )
                    //  issReadyQ.hdPtr = 0;
                } // if !ot_stallup

              }
              else if ( reoBufferPtr->lD || reoBufferPtr->inOrder )
              { //*******ISSUE LD/ST FUNCTION UNIT***********
        //        fprintf(stderr," Test 2 Ld/Sw[%d]= %u\n",i, finiID);
                ld_fu_available = 0;
                while (  (unsigned)ld_width_cntr < LD_WIDTH )
                {
                  ld_width_cntr ++;
                 if ( !FU_STALL->ld_StallUp[ld_width] )
                 {
                   if ( reoBuffer[finiID].thrdID != INPUT->thrdID[i] || reoBuffer[finiID].regs_PC != INPUT->regs_PC[i] || reoBuffer[finiID].rd_new != INPUT->rd_new[i] ) break; 
                   ld_fu_available = 1;
                   reoBufferPtr->issued = 1; //Set Issued bit (wr_port at Dispatch stage disabled have to fix it)
                   
                   ld_ptr = &load_unit[ld_width].ldQ[ load_unit[ld_width].hdPtr];

                   ld_ptr->reoID = finiID;
                //   if (cycle_count > 2240)
                 //    fprintf(stderr,"LD ISSUED[%d] Fu[%d]= %u\n",i, ld_width, finiID);
                   ld_ptr->inst_a = INPUT->inst_a[i];
                   ld_ptr->inst_b = INPUT->inst_b[i];
                   ld_ptr->regs_PC = INPUT->regs_PC[i];
                   ld_ptr->rd_new = INPUT->rd_new[i];
                   ld_ptr->spec = INPUT->spec[i];

                   ld_ptr->rs_data = regs_cp.regs_R[ reoBufferPtr->rs ];
                   ld_ptr->rt_data =  regs_cp.regs_R[ reoBufferPtr->rt ];

                    ld_width++; // for the next Unit on the same issue grp
                     if (  ld_width >= LD_WIDTH )
                       ld_width = 0;
                    break;
                  }
                  ld_width++;
                  if (  ld_width >= LD_WIDTH )
                     ld_width = 0;

                } // end of while ( ot_width < OT_WIDTH )

               if ( !ld_fu_available )
                {
                  OUTPUT->stallUp[i] = 1;
 //                 fprintf(stderr," ld Bus = %d at cycle = %u\n", i, cycle_count);
           //       fprintf ( stderr, " stall ld_PC = %d \n", INPUT->regs_PC[i] );
          	  ldFUStallCntr++;
          	 //issReadyQ.slotID[ issReadyQ.hdPtr ] = finiID;  // Store the Inst. Window Slot ID directly in the Ready Q
                  //issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                  //issReadyQ.hdPtr++; 
                   //if ( (unsigned) issReadyQ.hdPtr == REORDER_WIDTH )
                    //  issReadyQ.hdPtr = 0;
                } // if !ot_stallup
                
              }
              else //-----Other Instructions/MFLO/MFHI -----------
	      { //***ISSUE: Other Function Unit********
                ot_fu_available = 0;
                while (  ot_width_cntr < OT_WIDTH )
                {
                  ot_width_cntr ++;
                 if ( !FU_STALL->ot_StallUp[other_width] )
                 {
                   if ( reoBuffer[finiID].thrdID != INPUT->thrdID[i] || reoBuffer[finiID].regs_PC != INPUT->regs_PC[i] || reoBuffer[finiID].rd_new != INPUT->rd_new[i] ) break; 
                   ot_fu_available = 1;
                   reoBufferPtr->issued = 1; //Set Issued bit (wr_port at Dispatch stage disabled have to fix it)
                // issReadyQ.valid[ issReadyQ.tailPtr ] = 0;
                // issReadyQ.tailPtr++;
                   
                   other_ptr = &other_unit[other_width].otQ[ other_unit[other_width].hdPtr];
                   other_ptr->reoID = finiID;
                   other_ptr->inst_a = INPUT->inst_a[i];
                   other_ptr->inst_b = INPUT->inst_b[i];
                   other_ptr->regs_PC = INPUT->regs_PC[i];
                   other_ptr->rd_new = INPUT->rd_new[i];
                   other_ptr->spec = INPUT->spec[i];

                   other_ptr->rs_data = regs_cp.regs_R[ reoBufferPtr->rs ];
                   other_ptr->rt_data =  regs_cp.regs_R[ reoBufferPtr->rt ];
                   //--------Mul/Div------------------
                   if ( reoBufferPtr->mult )
                   {  // MFHI and MFLO Insns
                      if (reoBufferPtr->readLO ) // read LO
                      {
                    	other_ptr->rs_data = regs_cp.regs_R[ reoBufferPtr->rs ]; //Read LO
                        other_ptr->rt_data = 0;
                      }
                      if ( reoBufferPtr->readHI ) // read HI 
                      {
                    	other_ptr->rs_data =  regs_cp.regs_R2[ reoBufferPtr->rs ]; // read HI
                        other_ptr->rt_data = 0;
                       }
		   }

                    other_width++; // for the next Unit on the same issue grp
                     if (  other_width >= OT_WIDTH )
                       other_width = 0;
                    break;
                  }
                    // Issue Round Robin Pointer Update
                   // ot_rr_ptr++;
                   // if ( ot_rr_ptr >= OT_WIDTH )
                    //  ot_rr_ptr = 0;
                  other_width++;
                  if ( other_width >= OT_WIDTH )
                     other_width = 0;

                } // end of while ( ot_width < OT_WIDTH )

               if ( !ot_fu_available )
                {
                  OUTPUT->stallUp[i] = 1;
                 //fprintf(stderr," ot Bus = %d at cycle = %u\n", i, cycle_count);
          	  otFUStallCntr++;
          	 // issReadyQ.slotID[ issReadyQ.hdPtr ] = finiID;  // Store the Inst. Window Slot ID directly in the Ready Q
                 // issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                  //issReadyQ.hdPtr++; 
                   //if ( (unsigned) issReadyQ.hdPtr == REORDER_WIDTH )
                    //  issReadyQ.hdPtr = 0;
                } // if !ot_stallup
                
              } // if ( type of insn )

            } //Mispeculated
         }

       } // For Loop i

    //******* Issue Round Robin Pointer Update*********
      alu_rr_ptr = alu_width;
    //  fprintf(stderr," store alu_width %d\n", alu_rr_ptr);
      br_rr_ptr = br_width;
      ld_rr_ptr = ld_width;
      mul_rr_ptr = mul_width;
      ot_rr_ptr = other_width;

 } // end of Execute

void finish_main()
 {
    inst_finish* OUTPUT = &next_data_ptr->inst_fn;
    inst_finish* FU_STALL = &cur_data_ptr->inst_fn;
   // reorderBufferPORTS* REO = &cur_data_ptr->reoPORTS;
    //reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;
   // reorder_busy* REOBUSY = &next_data_ptr->reoBusyPORTS;
    reg_RR_bus* OUTPUT_RF = &next_data_ptr->regfilePORTS;
   register md_addr_t addr;
   unsigned  int tPtr = 0;
 //  prevWB = 0;
 //  readyCheck = 0;
   mulCheck = 0;
   //-*-*-*-*-*-*-*-*-Execute all the instructions that are ready-*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*    
  
    //******RESET StallUp Signals************OPEN MP Parallelization***
    for ( unsigned int alu_i =0; alu_i < ALU_WIDTH; alu_i++)
      OUTPUT->alu_StallUp[alu_i] = 0;

    for ( unsigned int mul_i =0; mul_i < MUL_WIDTH; mul_i++)
      OUTPUT->mul_StallUp[mul_i] = 0;

    for ( unsigned int ld_i =0; ld_i < LD_WIDTH; ld_i++)
      OUTPUT->ld_StallUp[ld_i] = 0;

    for ( unsigned int br_i =0; br_i < BR_WIDTH; br_i++)
      OUTPUT->br_StallUp[br_i] = 0;

    for (unsigned  int ot_i =0; ot_i < OT_WIDTH; ot_i++)
      OUTPUT->ot_StallUp[ot_i] = 0;

    //---------Initialize all write back ports to zero--------------
      OUTPUT_RF->wr_enableFini = 0; //reoBuffer[ finiID ].rd_new;
      for ( i = 0; (unsigned) i < (WB_WIDTH); i++ )
      {
        OUTPUT_RF->wr_addrValidFini[i] = 0; //reoBuffer[ finiID ].rd_new;
	OUTPUT->finishBit[i] = 0 ;
      }

  //---------Group the insns in the Priority Queus----- ***OPEN MP PARALLELIZATION***
     tPtr = 0;
     for (unsigned  int aluIndx = 0; aluIndx < ALU_WIDTH; aluIndx++)
     {
      //fprintf ( stderr," alu_stall = %d PC = %d \n", FU_STALL->alu_StallUp[aluIndx], alu_ptr->regs_PC);
  //     OUTPUT->alu_StallUp[aluIndx] = 0;
      if ( !FU_STALL->alu_StallUp[ aluIndx ] )
      {
        tPtr = alu_unit[aluIndx].tailPtr; 
        alu_ptr = &alu_unit[aluIndx].aluQ[tPtr];

       if ( alu_ptr->regs_PC > 0 )
       {
//         if ( wakeUpTbl[alu_ptr->reoID].slotLength > 1 )
         {
            hPriorityQ[ hPQ_tailPtr ] = aluIndx;      
     //      fprintf ( stderr, " ALU hPQ_tailPtr = %d PC = %d reoID = %d \n", hPQ_tailPtr, alu_ptr->regs_PC, alu_ptr->reoID );
            hPQ_tailPtr ++;
            if (hPQ_tailPtr >= REORDER_WIDTH)
             hPQ_tailPtr = 0;
         }
       }

      } // end of if (alu_FU_Stall) 
     } // end of for ( alu_FU_STALL )
  // -----------Mul FU --------------------
     tPtr = 0;
     for (unsigned  int mulIndx = 0; mulIndx < MUL_WIDTH; mulIndx++)
     {
 //     OUTPUT->mul_StallUp[mulIndx] = 0;
      if ( !FU_STALL->mul_StallUp[mulIndx] )
      {
        tPtr = mul_unit[mulIndx].tailPtr; 
        mul_ptr = &mul_unit[mulIndx].mulQ[tPtr];

        if ( mul_ptr->regs_PC > 0 )
        {
   //      if ( wakeUpTbl[mul_ptr->reoID].slotLength > 1 )
         {
            hPriorityQ[ hPQ_tailPtr ] = ( ALU_WIDTH ) + mulIndx;      
      //   fprintf ( stderr, " mul hPQ_tailPtr = %d PC = %d reoID = %d \n", hPQ_tailPtr, mul_ptr->regs_PC[ mulIndx ], mul_ptr->reoID[mulIndx] );
            hPQ_tailPtr ++;
            if ( (unsigned)hPQ_tailPtr >= REORDER_WIDTH)
             hPQ_tailPtr = 0;
         }
       }
      }// end of if ( mul_stallUp)
     } // end of for ( mulIndx )

     tPtr = 0;
     for (unsigned  int brIndx = 0; brIndx < BR_WIDTH; brIndx++)
     {
 //     OUTPUT->mul_StallUp[mulIndx] = 0;
      if ( !FU_STALL->br_StallUp[brIndx] )
      {
        tPtr = branch_unit[brIndx].tailPtr; 
        br_ptr = &branch_unit[brIndx].brQ[tPtr];

        if ( br_ptr->regs_PC > 0 )
        {
   //      if ( wakeUpTbl[mul_ptr->reoID].slotLength > 1 )
         {
            hPriorityQ[ hPQ_tailPtr ] = ( ALU_WIDTH + MUL_WIDTH ) + brIndx;      
        // fprintf ( stderr, " br hPQ_tailPtr = %d PC = %d reoID = %d brIndx = %d \n", hPQ_tailPtr, br_ptr->regs_PC, br_ptr->reoID, hPriorityQ[ hPQ_tailPtr ] );
            hPQ_tailPtr ++;
            if ( (unsigned)hPQ_tailPtr >= REORDER_WIDTH)
             hPQ_tailPtr = 0;
         }
       }
      }// end of if ( br_stallUp)
     } // end of for ( brIndx )

   //--------LOAD/ST FU-----------------
     tPtr = 0;
     for ( unsigned int ldIndx = 0; ldIndx < LD_WIDTH; ldIndx++)
     {
 //     OUTPUT->mul_StallUp[mulIndx] = 0;
      if ( !FU_STALL->ld_StallUp[ldIndx] )
      {
        tPtr = load_unit[ldIndx].tailPtr; 
        ld_ptr = &load_unit[ldIndx].ldQ[tPtr];

        if ( ld_ptr->regs_PC > 0 )
        {
   //      if ( wakeUpTbl[mul_ptr->reoID].slotLength > 1 )
         {
            hPriorityQ[ hPQ_tailPtr ] = ( ALU_WIDTH + MUL_WIDTH + BR_WIDTH ) + ldIndx;      
            hPQ_tailPtr ++;
            if ( (unsigned)hPQ_tailPtr >= REORDER_WIDTH)
             hPQ_tailPtr = 0;
         }
       }
      }// end of if (ld_stallUp)
     } // end of for ( ldIndx )
  //-------Other FU---------------------
     tPtr = 0;
     for ( unsigned int otIndx = 0; otIndx < OT_WIDTH; otIndx++)
     {
//      OUTPUT->ot_StallUp[otIndx] = 0;
      if ( !FU_STALL->ot_StallUp[ otIndx ] )
      {
        tPtr = other_unit[otIndx].tailPtr;
        other_ptr = &other_unit[otIndx].otQ[tPtr];
        if ( other_ptr->regs_PC > 0 )
        {
      //   if ( wakeUpTbl[other_ptr->reoID].slotLength > 1 )
         {
            hPriorityQ[ hPQ_tailPtr ] = ( ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH ) + otIndx;      
//          fprintf ( stderr, " OT length = %d  hPQ_tailPtr = %d PC = %d reoID = %d \n", wakeUpTbl[other_ptr->reoID].slotLength, hPQ_tailPtr, other_ptr->regs_PC, other_ptr->reoID );
            hPQ_tailPtr ++;
            
            if ( (unsigned)hPQ_tailPtr >= REORDER_WIDTH)
             hPQ_tailPtr = 0;
         }
       }
     } // end of if ( ot_StallUp )
    }// end of for --ot_stallUp


  //***********WRITE-BACK STAGE******************************
      tPtr = 0; //temp FU container
      for (  i = 0; (unsigned) i < (WB_WIDTH); i++ )
      {
        //OUTPUT_RF->wr_addrValidFini[i] = 0; //reoBuffer[ finiID ].rd_new;
  //      fprintf ( stderr, " wbPtr = %d alu_width %d\n", wbPtr, alu_width );
        inst.a = 0;
        inst.b = 0;
        regs.regs_PC = 0;
        wb_bus[i].rd_new = 0;  

       //switch ( wbPtr )
        {
 //               fprintf ( stderr, " hPQ.hdPtr = %d hPQ.tPtr = %d \n ", hPQ_hdPtr, hPQ_tailPtr );
                if ( hPQ_hdPtr != hPQ_tailPtr )
                 {
                    alu_width = hPriorityQ[ hPQ_hdPtr ];
                    if ( alu_width < ALU_WIDTH )
                    {
                      //alu_ptr = &alu_unit.aluQ[ alu_unit.tailPtr[ alu_width ] ];
                      tPtr =  alu_unit[alu_width].tailPtr; 
                      alu_ptr = &alu_unit[alu_width].aluQ[tPtr];
                     }
                     else if ( alu_width >= ALU_WIDTH &&  alu_width < (ALU_WIDTH + MUL_WIDTH) ) 
                     {
                        mul_width = alu_width - ALU_WIDTH;
                        tPtr = mul_unit[mul_width].tailPtr;
                        alu_ptr = &mul_unit[mul_width].mulQ[tPtr];
                      }
                     else if ( alu_width >= (ALU_WIDTH + MUL_WIDTH) &&  alu_width < (ALU_WIDTH + MUL_WIDTH + BR_WIDTH) ) 
                     {
                        //fprintf ( stderr, "br hPQ.hd = %d PC = %d\n ", br_width, regs.regs_PC );
                        br_width = alu_width - (ALU_WIDTH + MUL_WIDTH);
                        tPtr = branch_unit[br_width].tailPtr;
                        alu_ptr = &branch_unit[br_width].brQ[tPtr];
                      }
                     else if ( alu_width >= (ALU_WIDTH + MUL_WIDTH + BR_WIDTH) &&  alu_width < (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH) ) 
                     {
                        //fprintf ( stderr, "ld hPQ.hd = %d PC = %d\n ", ld_width, regs.regs_PC );
                        ld_width = alu_width - (ALU_WIDTH + MUL_WIDTH + BR_WIDTH);
                        tPtr = load_unit[ld_width].tailPtr;
                        alu_ptr = &load_unit[ld_width].ldQ[tPtr];
                      }
                      else if ( alu_width >= (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH) &&  alu_width < (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH + OT_WIDTH) )
                      {
                        other_width = (alu_width - (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH) );
         //             fprintf ( stderr, "other hPQ.hd = %d alu_width = %d PC = %d\n ", other_width, alu_width, regs.regs_PC );
                        tPtr = other_unit[ other_width ].tailPtr; 
                        alu_ptr = &other_unit[ other_width ].otQ[tPtr];
                      }
   	              inst.a = alu_ptr->inst_a;
                      inst.b = alu_ptr->inst_b;
               	      regs.regs_PC = alu_ptr->regs_PC;
                      wb_bus[i].reoID = alu_ptr->reoID;
      //                fprintf ( stderr, " WB hPQ.hd = %d reoID = %d PC = %d\n ", alu_width, wb_bus[i].reoID, regs.regs_PC );
                      wb_bus[i].spec = alu_ptr->spec;
                      wb_bus[i].rd_new = alu_ptr->rd_new;
                      wb_bus[i].rs_data = alu_ptr->rs_data;
                      wb_bus[i].rt_data = alu_ptr->rt_data;
                      alu_ptr->inst_a = 0; 
                      alu_ptr->regs_PC = 0;
                      alu_ptr->rd_new = 0;
                      hPQ_hdPtr++;
                      if ( (unsigned)hPQ_hdPtr >= REORDER_WIDTH )
                      { hPQ_hdPtr = 0; }
                  } // end of if ( hdPtr != tailPtr ) High Priority Q
          } //End of Round Robin Selection

          if ( regs.regs_PC != 0 )
          { 
                //unsigned int ex1MSK = 0;
            reoBufferPtr = &reoBuffer[ wb_bus[i].reoID ];
            if ( inst.a > 0  )  //execute only valid instructions and correctly speculated instructions
            {
              if ( !reoBufferPtr->misspeculated && !reoBufferPtr->exception /*&& !reoBufferPtr->inOrder */)
              {
                //fprintf(stderr,"PC %d \t ", regs.regs_PC);
                 //   md_print_insn( inst, regs.regs_PC,  stderr);

                MD_SET_OPCODE(op, inst);
                 switch (op)
                 {
                  #define DEFINST(OP,MSK,NAME,OPFORM,RES,FLAGS,O1,O2,I1,I2,I3)               \
                  case OP:                                                   \
                  /*if ( !reoBufferPtr->inOrder ) (0x0b == MSK || MSK == 0x0c )   \
                     || (0x30 <= MSK && MSK <= 0x3a) \
                     || (0x29 <= MSK && MSK <= 0x2d) \
                     || (0xc0 <= MSK && MSK <= 0xd2 ) \
                     || (0x70 <= MSK && MSK <= 0x97 ) \
                     ||  (0xa0 <= MSK && MSK <= 0xa1) \
                     || (0xa3 <= MSK && MSK <= 0xa8 ) ) \
                    { /*Skip Stores & Mult/Div/mflo's/double loads dlw for Complete Stage } \
                 else*/  \
                    { SYMCAT(OP, _IMPL);  }     \
                  break;
                  #define DECLARE_FAULT(FAULT)                                                \
                   {  break; }
                  #include "machine_oo.def"

                }

              } // if (!misspeculated)

            } // if Inst.a > 0
              //Finish the InOrder Instruction, since Stores & Lds are sequenced by the queue;

            if ( wb_bus[i].rd_new > 0 || inst.a > 0)  // Finish the Speculated Instruction and other valid instructions
             {
              //------SET Finish Bit ---------------
                if ( (reoBufferPtr->regs_PC == regs.regs_PC && reoBufferPtr->rd_new == wb_bus[i].rd_new)  )
                {
                 //       fprintf(stderr,"PC %d reo = %d valid %d\t ", regs.regs_PC, wb_bus[i].reoID, thrdPC_Q.valid[reoBufferPtr->thrdID]);
                  OUTPUT->finishAddr[i] = wb_bus[i].reoID;
                  OUTPUT->finishBit[i] = 1; 
               //----Set Wake Up Ptr----

                 if ( (!reoBufferPtr->exception  && !reoBufferPtr->misspeculated && followBrPred )||\
                            (!reoBufferPtr->exception  && !reoBufferPtr->misspeculated && !followBrPred && reoBufferPtr->thrdIDValid && thrdPC_Q.valid[reoBufferPtr->thrdID]))
                 {
                  //********THREAD DISCARD LOGIC: To save fetch width from being used by unnecessary paths****************
                if ( reoBufferPtr->thrdIDValid && !reoBufferPtr->followBr && (MD_OP_FLAGS(op) &  F_COND) )
                  {
                        unsigned int thrdMask = 1;
                  //      fprintf(stderr,"PC %d reo = %d \t ", regs.regs_PC, wb_bus[i].reoID);
                        //md_print_insn( inst, regs.regs_PC,  stderr);
          //              print_reorder();
                   //    fprintf(stderr,"cycle %d ptr = %d thdID = %d \n", cycle_count, reoBufferPtr->thrdBitPtr, reoBufferPtr->thrdID );
                             // fprintf(stderr," %d  continue thrdID %d ptr %d = %d \n", cycle_count, i, thrdMask, thrdPC_Q.continueFetch[i]);
               
                       int curID = 0;                                       
                       list<unsigned int>::iterator  it; 
                       for (it = activeList.begin(); it != activeList.end(); it++)
                        {
                          thrdMask = 1;

                         if ( reoBufferPtr->thrdBitPtr > 0 && reoBufferPtr->thrdBitPtr < THREAD_LEVEL)
                          thrdMask = thrdMask << (reoBufferPtr->thrdBitPtr );
                         //Get Thread ID
                          curID =  *it;

                          if ( thrdPC_Q.valid[curID] && thrdPC_Q.continueFetch[curID] )
                          {
                           if ( threadMatch( reoBufferPtr->thrdBitPtr, reoBufferPtr->thrdID, thrdPC_Q.bitPtr[curID], curID ) )
                            {
                             // fprintf(stderr," %d  continue thrdID %d ptr %d = %d \n", cycle_count, i, thrdMask, thrdPC_Q.continueFetch[i]);
                              threadUpdate = 1; 
                              if (reoBufferPtr->regs_NPC)
                              {
                                thrdPC_Q.continueFetch[curID] =  (( curID/* ThreadID */ & (thrdMask)) != 0); // Taken: True;else 0 
                              //  thrdPC_Q.valid[curID] =  (( curID/* ThreadID */ & (thrdMask)) != 0); // Taken: True;else 0 
                                //fprintf(stderr," %d  continue thrdID %d reoID = %d thrdBitPtr %d ptr %d = %d \n", cycle_count, curID, wb_bus[i].reoID, reoBufferPtr->thrdBitPtr, thrdMask, thrdPC_Q.valid[i]);
                              }
                              else
                              {
                                thrdPC_Q.continueFetch[curID] =  (( curID/* ThreadID */ & (thrdMask)) == 0); //Not Taken: True;else 0 
                               // thrdPC_Q.valid[curID] =  (( curID/* ThreadID */ & (thrdMask)) == 0); // Taken: True;else 0 
                               // fprintf(stderr," %d continue NotTaken thrdID %d ptr %d = %d \n", cycle_count, curID,thrdMask ,  thrdPC_Q.valid[i]);
                               }

                               if (!thrdPC_Q.continueFetch[curID])
                               { //Remove the inactive thrdID
                   //               fprintf(stderr," %d  erase %d thrdID %d  \n", cycle_count, wb_bus[i].reoID, curID);
                                  threadDiscard[ thrdPC_Q.threadCount[curID] ] ++; // Count the no. of insn. lost due to thread discarding.
                                  it = activeList.erase(it); // Erases current and returns next it
                                  it --;
                               }
                             }//thread Match
                       //    if (cycle_count > 9358580)
                        //      fprintf(stderr," Br PC = %d Valid[%d] = %d \n", reoBufferPtr->regs_PC, i, thrdPC_Q.valid[i]);
                          }//valid
                        }// end of for
                        //temphdPtr=activeList.end(); //Reinitialize the active it
                       //Permanently Erase the Thread IDs from ActiveList
                    }
                  //********End of Thread Discard Logic*********

                   wakeUpPtr = &wakeUpTbl[wb_bus[i].reoID];
                   if ( wakeUpPtr->valid )
                   {
                   for (ready = 0; ready < wakeUpPtr->slotLength ; ready++)
                   {
                     if ( (reoBuffer[ wakeUpPtr->slotID[ready] ].busy) 
                             && (reoBuffer[ wakeUpPtr->slotID[ready]].regs_PC == wakeUpPtr->regs_PC[ready]) &&
                               (reoBuffer[ wakeUpPtr->slotID[ready]].rd_new == wakeUpPtr->rd_new[ready]) &&
                                (reoBuffer[ wakeUpPtr->slotID[ready]].thrdID == wakeUpPtr->thrdID[ready])  ) 
                    {
               	     if ( reoBuffer[ wakeUpPtr->slotID[ready] ].wakeUp )
                     {
                       // fprintf( stderr, " Ready Now = %d hdPtr = %d ", ready, issReadyQ.hdPtr );
                      //  if ( reoBuffer[ wakeUpPtr->slotID[ready] ].busy) 
                        
                  	  issReadyQ.slotID[ issReadyQ.hdPtr ] = wakeUpPtr->slotID[ready];  // Store the Inst. Window Slot ID directly in the Ready Q
                 /*    if (cycle_count > 46000 && issReadyQ.slotID[issReadyQ.hdPtr] == 2695)
                       { fprintf( stderr, " cycle = %d Reo = %d WakeReoId[%d] = %d\n ", cycle_count, wb_bus[i].reoID,  issReadyQ.hdPtr, issReadyQ.slotID[ issReadyQ.hdPtr ]); 
                      }*/
                     
                    //   fprintf( stderr, "  2 Ready Now = %d hdPtr = %d\n ",  wb_bus[i].reoID, issReadyQ.slotID[ issReadyQ.hdPtr ] );
                  	  issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                  	  issReadyQ.discard[ issReadyQ.hdPtr ] = 0;
                  	  issReadyQ.hdPtr++; 
                  	  if ( issReadyQ.hdPtr == REORDER_WIDTH )
                      	     issReadyQ.hdPtr = 0;
                  	  if ( issReadyQ.hdPtr == issReadyQ.tailPtr )
		      	    { /*OUTPUT->stallUp = 1;*/ issQStallCntr++; }
               	     }
               	    else
              	    {
                        //fprintf( stderr, "\n Wake Up \n " );
                     //  fprintf( stderr, "  WakeUp Now = %d hdPtr = %d\n ",  wb_bus[i].reoID, issReadyQ.slotID[ issReadyQ.hdPtr ] );
                     //if (cycle_count > 46000 && wakeUpPtr->slotID[ready] == 2695)
                      //  fprintf( stderr, "\n  Wake Up %d\n", wakeUpPtr->slotID[ready] );

			 reoBuffer[ wakeUpPtr->slotID[ready] ].wakeUp = 1;
                	// reoBuffer[ ready ].wakeUp = 1;
               	     }
			// wakeUpTbl[wb_bus[i].reoID].valid[ready] = 0;  //Reset the entry
                    }//if busy and matching check
                   } //For ready()

                     wakeUpPtr->valid  = 0;
	             wakeUpPtr->slotLength = 0; //Reset 
	       	  } // if wakeup.Valid

              }//if !exception
             // ----SET RF Ports Valid------------
                if ( (!reoBufferPtr->misspeculated && followBrPred) || \
                        (!reoBufferPtr->misspeculated && !followBrPred && reoBufferPtr->thrdIDValid && thrdPC_Q.valid[reoBufferPtr->thrdID]) )
                {
                  OUTPUT_RF->wr_enableFini = 1;
                  OUTPUT_RF->wr_addrValidFini[i] = wb_bus[i].rd_new;
                  OUTPUT_RF->wr_validFini[i] = 1;
                }
              } // if regsPC match
            }// if rd_new > 0

        }//if regs.regs_PC != 0
        else
        {
           i = WB_WIDTH; // break for ( wbPtr )
        }

      }  //For loop Wb_WIDTH

//--------------Check if there is WB CONTENTION; If True then StallUp---------------
    wbPtr = 0;
    tPtr = 0;
    //--------Set the Other Func. Ptr------------
  if ( hPQ_hdPtr != hPQ_tailPtr )
    {
       wbPtr = hPQ_hdPtr;
       while ( (unsigned) wbPtr != hPQ_tailPtr )
       {
         tPtr = hPriorityQ[ wbPtr ];  
         if (  (unsigned)tPtr < ALU_WIDTH )
         {
         // alu_ptr = &alu_unit.aluQ[ alu_unit.tailPtr[ alu_width ] ];
   	  //            inst.a = alu_ptr->inst_a[ alu_width ];
          aluWBStallCntr++;
          OUTPUT->alu_StallUp[tPtr] = 1;
         }
         else if (  (unsigned)tPtr >= ALU_WIDTH && (  (unsigned)tPtr < ALU_WIDTH + MUL_WIDTH) )
         {
           mulWBStallCntr++;
           OUTPUT->mul_StallUp[ tPtr - ALU_WIDTH] = 1;
         }
         else if ( (  (unsigned)tPtr >= (ALU_WIDTH + MUL_WIDTH ) ) && (  (unsigned)tPtr < (ALU_WIDTH + MUL_WIDTH + BR_WIDTH ) ) )
         {
             brWBStallCntr++;
             OUTPUT->br_StallUp[ tPtr - (ALU_WIDTH + MUL_WIDTH)] = 1;
         }
         else if ( (  (unsigned)tPtr >= (ALU_WIDTH + MUL_WIDTH + BR_WIDTH) ) && (  (unsigned)tPtr < (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH) ) )
         {
             ldWBStallCntr++;
             OUTPUT->ld_StallUp[ tPtr - (ALU_WIDTH + MUL_WIDTH + BR_WIDTH)] = 1;
         }
         else if ( (  (unsigned)tPtr >= (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH) ) && (  (unsigned)tPtr < (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH + OT_WIDTH) ) )
         {
             otWBStallCntr++;
             OUTPUT->ot_StallUp[ tPtr - (ALU_WIDTH + MUL_WIDTH + BR_WIDTH + LD_WIDTH)] = 1;
         }
       //if ( OUTPUT->alu_StallUp && OUTPUT->mul_StallUp &&  OUTPUT->ot_StallUp ) break;
                                                                                                                                                       
          wbPtr ++;
          if (  (unsigned) wbPtr >= REORDER_WIDTH )
           wbPtr = 0;
        } // end of while ( wbPtr != hPQ_tailPtr )
    } // end of hPQ_hdPtr != hPQ_tailPtr


// fprintf( stderr, " ---finish -- \n");
//----------------------------------------------------------------------------------------

}


//---------COMPLETE STAGE-----------

void complete_main ()
{
    register md_addr_t addr;
    bool mem_violation_exe = 0;
    bool sw_exe = 0;
    bool thrdUpdate = 0;
 //   int finiID;
   int exMSK = 0;  // Exception mask
   int vctrID = 0;  // Exception mask

   reg_busy* OUTPUT_BUSY = &next_data_ptr->busyPORTS;
   inst_complete* OUTPUT = &next_data_ptr->inst_cp;
   reg_bus* OUTPUT_ARP = &next_data_ptr->arpPORTS;
   //reorder_busy* REOBUSY = &next_data_ptr->reoBusyPORTS;

  // fprintf( stderr, "\n-----------COMPLETE -----------\n" );
   OUTPUT->stallBubble = 0;
   OUTPUT->restartFetch = 0;
   OUTPUT->regs_PC = 0;
   //inst_complete* CMPLT_STALL= &cur_data_ptr->inst_cp;
   OUTPUT->completeBit = cur_data_ptr->inst_cp.completeBit;
   wdTimer ++;

  //Initialize wr ports
   OUTPUT_BUSY->wr_enable= 0;  
   {
     for (i = 0; (unsigned) i < COMPLETE_WIDTH; i++)
     {
       OUTPUT_BUSY->wr_addr_cp[i]  = 0;
       OUTPUT_ARP->wr_addr_cp[i]  = 0;
     //  OUTPUT_ARP->wr_data_cp[i]  = 0;
     }
   }

   for ( unsigned int i = 0; (unsigned) i < COMPLETE_WIDTH; i++)
   {
         //mem_violation_exe = 1; // SET to 1 to disable CHECKER
         reoBufferPtr = &reoBuffer[tailPtr];  // Get the Pointer to Complete
     //    fprintf( stderr," %u complete %d tail= %d %d %d %d \t", cycle_count, i, tailPtr, reoBufferPtr->finished, reoBufferPtr->issued, reoBufferPtr->busy);
      //---Check if it is in the Correct State ----------
      if (  reoBufferPtr->finished == 1 && reoBufferPtr->busy == 1 && reoBufferPtr->issued == 1 ||
               (reoBufferPtr->misspeculated == 1 && reoBufferPtr->busy == 1 && reoBufferPtr->issued == 0)  ||
                   (reoBufferPtr->thrdIDValid && !thrdPC_Q.valid[reoBufferPtr->thrdID] && reoBufferPtr->thrdBitPtr > 0 && reoBufferPtr->busy == 1 && reoBufferPtr->issued == 0)  ) //check completed bit for precise exceptions
      {
         wdTimer = 0;  // Reset
        //--------Reset Thrd Busy if the ThrdCount is zero----------
       if (!reoBufferPtr->misspeculated )
        {
         if ( /* thrdPC_Q.completeBit &&*/ reoBufferPtr->thrdIDValid ) 
         {
            //---------Check if the Thread is good to complete---------
           if ( reoBufferPtr->rd_new > 0 )
           { 
             if ( regVectorSearch ( reoBufferPtr->thrdID ) )
             {
                if ( (reg_ii)->ptr[reoBufferPtr->thrdBitPtr][reoBufferPtr->rd] == reoBufferPtr->rd_new )
                    (reg_ii)->valid[reoBufferPtr->thrdBitPtr][reoBufferPtr->rd] = 0;
             }
           else
            {
              fprintf(stderr,"not thread found\n");
             print_reorder();
              exit(0);
            }

           } 
            // thrdPC_Q.valid[reoBufferPtr->thrdID] = !reoBufferPtr->misspeculated ;  // If Mis-Speculated Reset Valid Bit
         //    if (cycle_count > 9000 )
       
            if ( thrdPC_Q.threadCount[reoBufferPtr->thrdID] > 0 )
            {   
               thrdPC_Q.threadCount[reoBufferPtr->thrdID]--;
           //    fprintf(stderr," thrdID %d reset ",reoBufferPtr->thrdID);

               if ( thrdPC_Q.threadCount[reoBufferPtr->thrdID] == 0 )
               {
                // if ( (thrdBits.BITS  & thrdBits.hdPtr) != (reoBufferPtr->thrdID & (thrdBits.hdPtr)) ) // Flushout the Bad Path
        //	 if (!thrdPC_Q.valid[reoBufferPtr->thrdID])
                 {
                    //if (cycle_count > 13200)
                  //   fprintf(stderr,"\n thrdID %d FREE ",reoBufferPtr->thrdID);
                   /*for (unsigned k=1; k <= (THREAD_LEVEL); k++) // Lo & Hi
                   {
                      for (unsigned int j=0; j<(MD_NUM_IREGS + 1); j++) // Lo & Hi
                      {
                          rRegPtr[k][reoBufferPtr->thrdID].valid[j] = 0;
                      }
                   }
                    thrdPC_Q.thrdParentID[reoBufferPtr->thrdID] = 0;
                    thrdPC_Q.thrdParentLevel[reoBufferPtr->thrdID] = 0;
                    threadBusyList.remove(reoBufferPtr->thrdID);
                   */   thrdPC_Q.busy[reoBufferPtr->thrdID] = 0; 
                    thrdPC_Q.bitPtr[reoBufferPtr->thrdID] = 0; 
                   if ( regVectorSearch ( reoBufferPtr->thrdID) )
                     {
                        rRegVector.erase(reg_ii); // Register Pointer
                     }
                  //  if( cycle_count > 9127500) 
                   //   fprintf(stderr," Reset delete %d\n", reoBufferPtr->thrdID);
                 }// if flushout
               } // if threadCoutn == 0
            } // if reoThrdValid
             //fprintf(stderr," CMPthrdID %d Count = %d ",reoBufferPtr->thrdID, thrdPC_Q.threadCount[reoBufferPtr->thrdID]);
            //Decision based of thrdBits.BTIS
            //reoBufferPtr->misspeculated =  ((thrdBits.BITS/* & thrdBits.hdPtr*/) ^ (reoBufferPtr->thrdID  /* & thrdBits.hdPtr*/));
            reoBufferPtr->misspeculated = !thrdPC_Q.valid[reoBufferPtr->thrdID];//  ((thrdBits.BITS/* & thrdBits.hdPtr*/) ^ (reoBufferPtr->thrdID  /* & thrdBits.hdPtr*/));
             // Invalidate only if it matches as later insn can change it
               // if (cycle_count > 13200)
          //   if( cycle_count > 9127500) 
           //    fprintf(stderr," %d mis-spec[%d]= %d Ptr %d = %d  hd = %d\n", cycle_count, tailPtr, reoBufferPtr->misspeculated, reoBufferPtr->thrdID, thrdBits.BITS, thrdBits.hdPtr);
               //thrd_Active();
              if ( thrdPC_Q.threadCount[reoBufferPtr->thrdID] < 0 ) { fprintf(stderr,"count"); exit(-1); }
         } // End of if (reoThrdValid)
        } // End of if (misspeculated)

         if ( reoBufferPtr->misspeculated != 1 ) //Precise Exception
         {
            /* keep an instruction count */
             sim_num_insn++;
           //------Wake-Up instructions that are exceptions to Recover Precisely----
           if ( reoBufferPtr->exception == 1 /*|| reoBufferPtr->inOrder == 1*/   ) //If Store Buffer is modelled
           {
                 wakeUpPtr = &wakeUpTbl[ tailPtr ];
                  if ( wakeUpPtr->valid )
                  {
                   for ( ready = 0; ready < wakeUpPtr->slotLength ; ready++)
                   {
             //             fprintf( stderr, " ReoId = %d, valid = %d", wb_bus[i].reoID, wakeUpTbl[wb_bus[i].reoID].valid[ready] );
                     if ( (reoBuffer[ wakeUpPtr->slotID[ready] ].busy) 
                             && (reoBuffer[ wakeUpPtr->slotID[ready]].regs_PC == wakeUpPtr->regs_PC[ready]) &&
                               (reoBuffer[ wakeUpPtr->slotID[ready]].rd_new == wakeUpPtr->rd_new[ready]) &&
                                (reoBuffer[ wakeUpPtr->slotID[ready]].thrdID == wakeUpPtr->thrdID[ready])  ) 
                    {
                       // fprintf( stderr, " Ready Now = %d hdPtr = %d ", ready, issReadyQ.hdPtr );
                    if ( reoBuffer[wakeUpPtr->slotID[ready] ].wakeUp )
                     {
                        issReadyQ.slotID[ issReadyQ.hdPtr ] = wakeUpPtr->slotID[ready];  // Store the Inst. Window Slot ID directly in the Ready Q
                        issReadyQ.valid[ issReadyQ.hdPtr ] = 1;
                        issReadyQ.discard[ issReadyQ.hdPtr ] = 0;
                    /* if (cycle_count > 46000 && wakeUpPtr->slotID[ready] == 2695)
                       { fprintf( stderr, "cmp1 cycle = %d Reo = %d WakeReoId[%d] = %d\n ", cycle_count, tailPtr, issReadyQ.hdPtr, issReadyQ.slotID[ issReadyQ.hdPtr ]); 
                       }*/

                        issReadyQ.hdPtr++;
                        if ( issReadyQ.hdPtr == REORDER_WIDTH )
                            issReadyQ.hdPtr = 0;
                        if ( issReadyQ.hdPtr == issReadyQ.tailPtr )
		      	   { OUTPUT->stallUp = 1; issQStallCntr++; }
                     }
                    else
                    {
                    // if (cycle_count > 46000 && wakeUpPtr->slotID[ready] == 2695)
                     //   fprintf( stderr, "\n cmp Wake Up %d\n", wakeUpPtr->slotID[ready] );
                         reoBuffer[ wakeUpPtr->slotID[ready] ].wakeUp = 1;
                        // reoBuffer[ ready ].wakeUp = 1;
                     }
                        // wakeUpTbl[wb_bus[i].reoID].valid[ready] = 0;  //Reset the entry
                    }// end of if busy and matching check
                   }//end of for loop

                     wakeUpPtr->valid  = 0;
                     wakeUpPtr->slotLength = 0; //Reset
                  }
          }
    //----------------Register Complete Update--------------------------//
             
           /*if ( reoBufferPtr->rd_new > 0 )
           { 
             if ( regVectorSearch ( reoBufferPtr->thrdID ) )
             {
                if ( (reg_ii)->ptr[reoBufferPtr->thrdBitPtr][reoBufferPtr->rd] == reoBufferPtr->rd_new )
                 {
                    (reg_ii)->valid[reoBufferPtr->thrdBitPtr][reoBufferPtr->rd] = 0;
                  }
             }
             if (rRegPtr[reoBufferPtr->thrdBitPtr][reoBufferPtr->thrdID].ptr[reoBufferPtr->rd] == reoBufferPtr->rd_new )
                rRegPtr[reoBufferPtr->thrdBitPtr][reoBufferPtr->thrdID].valid[reoBufferPtr->rd] = 0; //Default Level +1

              if (  (reg_ii)->valid[reoBufferPtr->thrdBitPtr][reoBufferPtr->rd] !=  rRegPtr[reoBufferPtr->thrdBitPtr][reoBufferPtr->thrdID].valid[reoBufferPtr->rd])
 {
 fprintf(stderr,"cmplt 2\n");
 exit(0);
 }
   }//reoBuffer > 0
*/
             OUTPUT_BUSY->wr_enable= 1;
             OUTPUT_BUSY->wr_busy_cp[i] = 0;
             OUTPUT_BUSY->wr_addr_cp[i] =  reoBufferPtr->rd_old; 
             //Read the Old Value from the ARP to Free it 
             //OUTPUT_BUSY->wr_addr_cp[i] = aRegPtr[reoBufferPtr->rd];  
          //  if ( cycle_count > 9790015 )
           //  fprintf( stderr,"reo = %d CMP A %d\n",tailPtr, OUTPUT_BUSY->wr_addr_cp[i]); 

             OUTPUT_ARP->wr_addr_cp[i] = reoBufferPtr->rd;
             OUTPUT_ARP->wr_data_cp[i] = reoBufferPtr->rd_new;
    //             fprintf( stderr, " addr_cp = %d data_cp = %d \n",  OUTPUT_ARP->wr_addr_cp[i], OUTPUT_ARP->wr_data_cp[i]);  
           //  aRegPtr [ reoBufferPtr->rd ] = reoBufferPtr->rd_new;

        //*********Execute Stores at Complete (Retirement of Stores)********************
            finiID = tailPtr;
            inst.a = reoBufferPtr->inst_a;
            inst.b = reoBufferPtr->inst_b;
            regs.regs_PC = reoBufferPtr->regs_PC;
            regs.regs_NPC = reoBufferPtr->regs_PC + sizeof(md_inst_t);
             
          /* if ( cycle_count > 9000 ) {
            fprintf(stderr,"  %d\n", regs.regs_PC);
            md_print_insn( inst,   regs.regs_PC, stderr);
            fprintf(stderr,"\n"); }
           */
            MD_SET_OPCODE(op, inst);

           unsigned tempAregPtr = aRegPtr[ reoBufferPtr->rd ]; 
           aRegPtr [ reoBufferPtr->rd ] = reoBufferPtr->rd_new; // Update for the Exception execution 
         //  if (cycle_count > 18676930 )
          //      fprintf(stderr,"new aRegPtr%d\n", aRegPtr[reoBufferPtr->rd]);
 // Update the Register File for Syscall usage
           switch (op)
           {
             #define DEFINST(OP,MSK,NAME,OPFORM,RES,FLAGS,O1,O2,I1,I2,I3)               \
             case OP:                                                   \
                if ( reoBufferPtr->exception || reoBufferPtr->inOrder )/*((0x0b == MSK) || (MSK == 0x0c ))   \
                     || ((0x30 <= MSK) && (MSK <= 0x3a)) \
                     || (0x46 <= MSK && MSK <= 0x4d)  \
                     || ((0x29 <= MSK) && (MSK <= 0x2d)) \
                     || ((0xc0 <= MSK) && (MSK <= 0xd2 )) \
                     || ((0x70 <= MSK) && (MSK <= 0x97)) \
                     ||  ((0xa0 <= MSK) && (MSK <= 0xa1)) \
                     || ((0xa3 <= MSK) && (MSK <= 0xa8 )) )*/\
                 {                     exMSK = MSK;  SYMCAT(OP, _IMPL); }       \
              break;
            #define DECLARE_FAULT(FAULT)                                                \
             { /*fault = (FAULT);*/ break; }
            #include "machine.def"
            default:
            fprintf(stderr,"\nInvalid code execution: NOP" );
            } 
     //---------If a Store Instruction--------- 
          if ( reoBufferPtr->inOrder )
          {
           //-------------Check Load Memory Violation---------------------
            if (sw_hdPtr != sw_tPtr )
            {
              sw_ldRecovery (sw_exe); // disabled on eager Threads
              sw_buffer[sw_hdPtr].valid = 0;
              sw_hdPtr++;  \
              if ((unsigned)sw_hdPtr >= REORDER_WIDTH) \
                sw_hdPtr = 0; \
            }
          }
         
         //--------If a Load Instruction------------
          if ( reoBufferPtr->lD )
          {
             if (ld_hdPtr != ld_tPtr )
             {
                if ( ld_buffer[ ld_hdPtr ].ld_fwd )  //ReoID of Reorder Buffer
                    ldFwdCntr ++; \

              if ( (ld_buffer[ld_hdPtr].mem_violation | ld_buffer[ld_hdPtr].mem_recover) && ld_buffer[ld_hdPtr].valid /* && !ld_buffer[ld_hdPtr].ld_fwd */)
              {
                 //-------------SW Addr Speculation Update -------------------
                 if (ld_buffer[ld_hdPtr].mem_violation)
                 {
                   ldpred_update ( ldpred, /* Ld Pred Instance */
                                  ld_buffer[ld_hdPtr].sw_pc, /* Memory Addr */
                                  ld_buffer[ld_hdPtr].ld_addr, /* Destination Memory Addr */
                                  1, /*taken */
                                  0, /*Correct Prediction */
                                  op
                                ); 
                 }
                 //-----Recover the Register State-----------
                 aRegPtr [ reoBufferPtr->rd ] = tempAregPtr; //reoBufferPtr->rd_old;  // Update the Reg File for Debugging
                // if (cycle_count > 18676930 )
               //  if (cycle_count > 18703000 )
                //   fprintf(stderr,"old aRegPtr%d\n", aRegPtr[reoBufferPtr->rd]);
                 OUTPUT_ARP->wr_addr_cp[i] = reoBufferPtr->rd;
                 OUTPUT_ARP->wr_data_cp[i] = tempAregPtr; //reoBufferPtr->rd_old;
               // fprintf( stderr, " Ld addr_cp = %d data_cp = %d \n",  OUTPUT_ARP->wr_addr_cp[i], OUTPUT_ARP->wr_data_cp[i]);  

                 OUTPUT_BUSY->wr_addr_cp[i] = reoBufferPtr->rd_new; 
          //  if ( cycle_count > 9790015 )
           //      fprintf( stderr,"reo = %d CMP B %d\n",tailPtr, OUTPUT_BUSY->wr_addr_cp[i]); 
                 OUTPUT->regs_PC =  reoBufferPtr->regs_PC; // Re-Fetch Ld Instruction ( Load Forwarding could be done here )
                 OUTPUT->stallBubble = 1;
                 mem_violation_exe = 1;
                /* Decrement the instruction count as the load instruction cannot complete */
                 sim_num_insn--;
                  
                //-------------Load Addr specuation Update----------------------------------------//
                 if (ld_buffer[ld_hdPtr].mem_violation)
                 {
                   ldpred_update ( ldpred, /* Ld Pred Instance */
                                  reoBufferPtr->regs_PC, /* Memory Addr */
                                  ld_buffer[ld_hdPtr].ld_addr, /* Destination Memory Addr */
                                  1, /*taken */
                                  0, /*Correct Prediction */
                                  op
                                ); 
                 //  fprintf(stderr," \nSave count %d cycle %d TailPtr = %d ld_PC = %d ld_addr = %d\n", ldRecvrCntr, cycle_count, tailPtr, reoBufferPtr->regs_PC, ld_buffer[ld_hdPtr].ld_addr);
                 }
               //-----------end of load speculation update-------------------------------
                if (ld_buffer[ld_hdPtr].mem_recover)
                  lw_mis_recvr++;
 
                if (ld_buffer[ld_hdPtr].mem_violation)
                  ldRecvrCntr ++;  //Load Recover Counter

                //if (ldRecvrCntr > 0)
                //{
                  // fprintf(stderr,"count %d cycle %d ld_hdPtr = %d ld_reoID = %d sw_pc = %u TailPtr = %d\n", ldRecvrCntr, cycle_count, ld_hdPtr, ld_buffer[ld_hdPtr].reoID, ld_buffer[ld_hdPtr].sw_pc, tailPtr);
             //     if (ldRecvrCntr == 36)
              //     exit(-1);

                 //}
                  //fprintf( stderr, "load cycle = %d PC = %d NPC = %d predPC = %d\n", \
                                 cycle_count, reoBufferPtr->regs_PC, reoBufferPtr->regs_NPC, reoBufferPtr->pred_PC  );
                 recovery_logic(); // Recovery Logic to Flush the RRP STATE
              }
              ld_buffer[ld_hdPtr].valid = 0;
              ld_hdPtr++;  \
              if ((unsigned)ld_hdPtr >= REORDER_WIDTH) \
                ld_hdPtr = 0; \

             }
          }


 // ****************Bulit-in Checker********************************
         if (  !mem_violation_exe ) {
            regs.regs_PC = cmpFetchPC;
            regs.regs_NPC = regs.regs_PC + sizeof(md_inst_t);
            MD_FETCH_INST(inst, mem, cmpFetchPC );

    /*  if ( cycle_count > 100000 ) 
       {
           fprintf(stderr,"PC %d \t ", regs.regs_PC);
               md_print_insn( inst,
                   regs.regs_PC,
                    stderr);
             fprintf(stderr, "\n");
        //     fprintf(stderr, "\n");vlMSK == 0xa0 || MSK == 0xa1 
         //       if ( !(reoBufferPtr->exception || reoBufferPtr->inOrder)  ) \
          //      if ( !(exMSK == 0xa0 || exMSK == 0xa1 || reoBufferPtr->inOrder)  ) 
        }
     */       MD_SET_OPCODE(op, inst);
           switch (op)
           {
             #define DEFINST(OP,MSK,NAME,OPFORM,RES,FLAGS,O1,O2,I1,I2,I3)               \
             case OP:                                                   \
                if ( !(reoBufferPtr->exception || reoBufferPtr->inOrder)  ) \
                 { SYMCAT(OP, _IMPL) ; }       \
              break;
            #define DECLARE_FAULT(FAULT)                                                \
             {  break; }
            #include "/home/aswinr/simplesim-3.0/machine.def"
           default:
            fprintf(stderr,"\nInvalid code execution: NOP" );
          } 

          if ( (exMSK == 0x0b || exMSK == 0x0c) && reoBufferPtr->regs_NPC ) // Changes NPC & treated as Exception
          {
              cmpFetchPC = reoBufferPtr->regs_NPC; 
           //   fprintf ( stderr, " %u NPC = %d Excep = %d \n", cycle_count, cmpFetchPC, reoBufferPtr->exception);
          }
          else
           cmpFetchPC = regs.regs_NPC; 

           if ( (exMSK == 0xa0 || exMSK == 0xa1 )  ) \
           {
              for (unsigned int t = 0; t < (MD_NUM_IREGS); t++)
                 SET_GPR(t, regs_cp.regs_R[ aRegPtr[t] ] );  //Re-initializes the Register state for debugging
           }
      //     if ( cycle_count > 14758150 )
          // fprintf(stderr," %u cmpFetch = %u\n",cycle_count, cmpFetchPC );
        }
  //--------------------------------------------------------------------------------

             reoBufferPtr->completed = 1; //To check for Speculation
       //*****************Precise Exception Logic*************************************
              if (  reoBufferPtr->exception ) /* || reoBufferPtr->inOrder )// (0x0b == exMSK || exMSK == 0x0c )  *\
                     || (0x30 <= exMSK && exMSK <= 0x3a) \
                     || (0x29 <= exMSK && exMSK <= 0x2d) \
                     || (0xc0 <= exMSK && exMSK <= 0xd2 ) \
                     || (0x70 <= exMSK && exMSK <= 0x97 ) \
                     ||  (0xa0 <= exMSK && exMSK <= 0xa1) \
                     || (0xa3 <= exMSK && exMSK <= 0xa8 ) ) */\
            {   //Syscall Recovery
              // fprintf(stderr, " \nSysCall " );
              if (MD_OP_FLAGS(op)  & F_CTRL)
              { //BC1T and BC1F does not need to recover unless misspeculated
                if ( reoBufferPtr->regs_NPC )
                  OUTPUT->regs_PC = reoBufferPtr->regs_NPC;
                else 
                  OUTPUT->regs_PC =  reoBufferPtr->regs_PC + sizeof(md_inst_t);
              }
              else
              {
                 OUTPUT->regs_PC =  reoBufferPtr->regs_PC + sizeof(md_inst_t);
                 excepCntr++; 
               //  brRecvrCntr++;
                 recovery_logic(); // Call RECOVER LOGIC
                 // fprintf(stderr,"PC %d \t ", OUTPUT->regs_PC);
                 OUTPUT->stallBubble = 1;
               }
            }
 
        
      //***************Branch Specuation**************************//
           if (MD_OP_FLAGS(op)  & F_CTRL)
           {   
               sim_num_branches ++;
                    //  fprintf( stderr, " check NPC valid %d follow Br %d \n", reoBufferPtr->thrdIDValid , reoBufferPtr->followBr);
             if ( !reoBufferPtr->thrdIDValid || (reoBufferPtr->thrdIDValid & reoBufferPtr->followBr) ) 
             {
               if ( speculation_check( tailPtr ) == 1) // NO Spec Check for Thrds
               {
                //--Recover the Register Access FIFO stack for procedure calls -jr ---
                  bpred_recover(pred, reoBufferPtr->regs_PC, reoBufferPtr->thrdID, reoBufferPtr->stack_recover_idx);
                //-----------------------------------------------------------
                  unknownTarget = 0;
                 // fprintf( stderr, " Br PC Update  \n"); 
                     if ( reoBufferPtr->regs_NPC )  
                       OUTPUT->regs_PC = reoBufferPtr->regs_NPC;
                     else 
                       OUTPUT->regs_PC =  reoBufferPtr->regs_PC + sizeof(md_inst_t);

                     OUTPUT->stallBubble = 1;
                     if ( (MD_OP_FLAGS(op) & (F_UNCOND|F_DIRJMP)) == (F_UNCOND|F_DIRJMP))
                     { brDirJmp++; }
                     else if ( (MD_OP_FLAGS(op) & (F_UNCOND|F_DIRJMP|F_CALL)) == (F_UNCOND|F_DIRJMP|F_CALL))
{ brDirCall++; }
		     else if ( (MD_OP_FLAGS(op) & (F_UNCOND|F_INDIRJMP)) == (F_UNCOND|F_INDIRJMP) )
{ brInDirJmp++; }
		     else if ( (MD_OP_FLAGS(op) & (F_COND|F_DIRJMP)) == (F_COND|F_DIRJMP) && !reoBufferPtr->exception )
                     {
                      //fprintf(stderr," reocycle = %d cycle = %d\n", reoBufferPtr->br_cycle, cycle_count);
                     //if ( (cycle_count - reoBufferPtr->br_cycle) < 100 )
                       brCondJmp++;
                     }
                     else if ( (MD_OP_FLAGS(op) & (F_UNCOND|F_INDIRJMP|F_CALL)) == (F_UNCOND|F_INDIRJMP|F_CALL) )
                   { brUnCondInDirJmp ++; }
                  
                   if ( !reoBufferPtr->exception )//Count only MisPredicted Branches Not Br. Exceptions
                     brMisPredCntr ++;
                   //  fprintf( stderr, "br cycle = %d PC = %d NPC = %d predPC = %d\n", \
                                 cycle_count, reoBufferPtr->regs_PC, reoBufferPtr->regs_NPC, reoBufferPtr->pred_PC  );
              //       print_reorder();

                    // inst.a = reoBufferPtr->inst_a;
                     //inst.b = reoBufferPtr->inst_b;
                     //md_print_insn( inst,          
                      // reoBufferPtr->regs_PC,            
                       //stderr);            
                     //fprintf(stderr, "\n");
                  //  fprintf( stderr, "FLUSH \n");
                }
                  //else
                   // fprintf( stderr, "SELECT \n");
              } // ThrdID Valid
              else
              {
                  if ( reoBufferPtr->regs_NPC) // Make sure NPC is not Zeor
                  {
                     // fprintf( stderr, " check NPC \n");
                    
                        if (reoBufferPtr->regs_NPC != reoBufferPtr->pred_PC ) // Both the Paths are Wrong; Got to flush out!
                        { // Recover the machine-state
                            recovery_logic();
                           //--Recover the Register Access FIFO stack for procedure calls -jr ---
                            bpred_recover(pred, reoBufferPtr->regs_PC, reoBufferPtr->thrdID, reoBufferPtr->stack_recover_idx);
                            OUTPUT->regs_PC = reoBufferPtr->regs_NPC;
                            OUTPUT->stallBubble = 1;
                            brMisPredCntr ++;
                      
                            fprintf( stderr, " cycle = %d Recovery PC = %d NPC = %d predPC = %d\n", \
                                      cycle_count, reoBufferPtr->regs_PC, reoBufferPtr->regs_NPC, reoBufferPtr->pred_PC  );
                            print_reorder(); //exit(-1);      
                        }
                   }
                }

                bool predTaken = 0;
                if ( reoBufferPtr->pred_PC )
                   predTaken = (reoBufferPtr->pred_PC != (reoBufferPtr->regs_PC + sizeof(md_inst_t))) ? 1 : 0;
                else
                   predTaken = 0;

                if ( reoBufferPtr->thrdIDValid && !reoBufferPtr->followBr && (MD_OP_FLAGS(op) &  F_COND) )
                 {
                 //  print_reorder();
                  // fprintf(stderr,"Cycle = %d\n", cycle_count);
                   if ( !OUTPUT->stallBubble )
                   {
                      unsigned int compBitPos = 1;
                      unsigned int resolve = 0;
                      OUTPUT->completeBit = 1;
                  // thrdPC_Q.completeBit = 1;
                      if ( reoBufferPtr->regs_NPC )
                        resolve = (reoBufferPtr->regs_NPC != (reoBufferPtr->regs_PC +sizeof(md_inst_t)));
                      else
                        resolve = 0;

                //if ( cycle_count > 20924200 ) 
                   //if ( cycle_count > 700 ) 
                   //    fprintf( stderr, "PC = %d Resolving %d shift = %d %d followBr = %d\n", reoBufferPtr->regs_PC, resolve, (reoBufferPtr->thrdBitPtr ), resolve  << (reoBufferPtr->thrdBitPtr ), reoBufferPtr->followBr );
                  // fprintf( stderr, " Reg2 = %d Ptr = %d\n", regs_cp.regs_R[aRegPtr[2]], aRegPtr[2]);
                   //fprintf( stderr, " Reg2 = %d Ptr = %d\n", regs.regs_R[2]);
                   //  if ( cycle_count > 9000 ) 
                    // {   fprintf( stderr, " BITS = %d hdptr = %d\n", thrdBits.BITS, thrdBits.hdPtr );
                     // }
                   
                       if ( resolve == 0 ) // Not Taken
                       { // 
                      //    fprintf( stderr, " Not Taken \n");
                          if ( reoBufferPtr->thrdBitPtr != THREAD_LEVEL )
                            compBitPos = (compBitPos  << (reoBufferPtr->thrdBitPtr ));
                          if ( compBitPos > (THREAD_WIDTH/2)) { /*fprintf(stderr,"HD RESET\n"); */ compBitPos = 1; }

                          compBitPos = (THREAD_WIDTH - 1) ^ compBitPos; // (1111 ^ 0001) = ( 1110 ) 
                          thrdBits.BITS = thrdBits.BITS & (compBitPos) ; // ( BITS & 1110 )
                       }
                       else
                       { // Shift to the bit position
                          resolve = (resolve  << (reoBufferPtr->thrdBitPtr  ));
                          if ( resolve > (THREAD_WIDTH/2)) { /*fprintf(stderr,"HD RESET\n"); */ resolve = 1; }

                          thrdBits.BITS = thrdBits.BITS | (resolve) ; //BITS: Represents the level that is resolved or whose outcome is known
                        }

                     //if ( cycle_count > 20924200 ) 
                        if ( thrdBits.hdPtr == 0 )
                          thrdBits.hdPtr = 1; //  1 bit-level is resolved
                        else 
                          thrdBits.hdPtr = thrdBits.hdPtr << 1; // Shift Left by 1

                        if (thrdBits.hdPtr > (THREAD_WIDTH/2)) { /*fprintf(stderr,"HD RESET\n"); */ thrdBits.hdPtr = 1; }

              //Invalidate the thread entries in the Table. Have to invalidate here because thread levels can overlap and there is has to be a mechansim to differentiate
                       // thrdMask = 1;
                        //thrdMask = ( thrdMask <<  ( reoBufferPtr->thrdBitPtr - 1)); // Since Level Count is Sub. earlier 
               //********THREAD DISCARD LOGIC****************
                       //list<int>::iterator  it; 
                      // if (cycle_count > 1000 )
                            // fprintf(stderr," Br reo %d PC = %d  hdptr %d BITS %d\n", tailPtr, reoBufferPtr->regs_PC, thrdBits.hdPtr, thrdBits.BITS);
                       for ( list<unsigned int>::iterator it = activeValidList.begin(); it != activeValidList.end(); it++)
                       // for (int i = 0; i < THREAD_WIDTH; i++)
                        {
                          if ( thrdPC_Q.valid[*it] )
                          {
                            thrdPC_Q.valid[*it] =  !((thrdBits.BITS  &  thrdBits.hdPtr) != ( *it/* ThreadID */ & (thrdBits.hdPtr))); // Flushout the Bad Path
                            //if (cycle_count > 1000)
                          //     fprintf(stderr," cur check %d valid %d\n", *it, thrdPC_Q.valid[*it]);
                            threadUpdate = 1; 
                            if (!thrdPC_Q.valid[*it])
                            {
                           //  if( cycle_count > 9127500) 
                            //   fprintf(stderr,"%d erase valid %d count = %d busy = %d\n", cycle_count, *it, thrdPC_Q.threadCount[*it], thrdPC_Q.busy[*it]) ;
                              if ( thrdPC_Q.continueFetch[*it] )
                              {
                           //  fprintf(stderr," erase valid %d count = %d\n", *it, thrdPC_Q.threadCount[*it]) ;
                            //  exit(0);
                                threadDiscard[ thrdPC_Q.threadCount[*it] ] ++; // Count the no. of insn. lost due to thread discarding.
                                activeList.remove(*it);
                                //temphdPtr = activeList.end();
                              }
                              if ( thrdPC_Q.threadCount[*it] == 0)
                              { // if count is Zero remove it
                         //       fprintf(stderr," remove %d\n", *it, thrdPC_Q.threadCount[*it]) ;
                              /*  for (unsigned k=1; k <= (THREAD_LEVEL); k++) // Lo & Hi
                                {
                                 for (unsigned int i=0; i<(MD_NUM_IREGS + 1); i++) // Lo & Hi
                                   {
                                     rRegPtr[k][*it].valid[i] = 0;
                                   }
                                }*/
                              if ( regVectorSearch (*it) )
                               {
                                 rRegVector.erase(reg_ii); // Register Pointer
                                //fprintf(stderr," complete delete %d\n", *it);
                               }
                                thrdPC_Q.busy[*it] = 0;
                                thrdPC_Q.bitPtr[*it] = 0;
                              //  fprintf(stderr," complete busy delete %d\n", *it);
                                //thrdPC_Q.thrdParentID[*it] = 0;
                                //thrdPC_Q.thrdParentLevel[*it] = 0;
                               // threadBusyList.remove(*it);
                              } // if threadCount == 0;
                             
                              it = activeValidList.erase(it);
                              if ( it != activeValidList.begin())
                                it --;
                            //if (cycle_count > 2000)
                        //       fprintf(stderr," Next check %d\n", *it) ;
                              if (*it > THREAD_WIDTH) { fprintf(stderr," Erase errors %d count %d \n", cycle_count, activeValidList.size()); exit(0);}

                              /*if ( regVectorSearch (*it) )
                               {
                                 rRegVector.erase(reg_ii); // Register Pointer
                               }
                              */
                              
                            }
                       //    if (cycle_count > 5190 )
                        //      fprintf(stderr," Br PC = %d Valid[%d] = %d hdptr %d BITS %d\n", reoBufferPtr->regs_PC, i, thrdPC_Q.valid[i], thrdBits.hdPtr, thrdBits.BITS);
                          }
                        }
                      //-----Invalidate the Issue Ready Queue---------
                        //for (int i = 0; i < REORDER_WIDTH; i++)
                        int issTail = issReadyQ.tailPtr;
                       while ( issReadyQ.valid[ issTail ]  )
                        {
                           issReadyQ.discard[issTail] = !thrdPC_Q.valid[issReadyQ.thrdID[issTail]]; // if not Valid; then Discard
                           issTail++;
                           if (issTail >= REORDER_WIDTH)
                             issTail = 0;
                        }
                //********End of Thread Discard Logic*********
                    // ALU Q
                    //   issue_ptr = NULL; 

/*                       issue_ptr = &ot_insn;
                       issTail = issue_ptr->hdPtr;
                       while ( issue_ptr->valid[ issTail ]  )
                        {
                           issue_ptr->discard[ issTail ]= !thrdPC_Q.valid[issue_ptr->thrdID[issTail]]; // if not Valid; then Discard
                           issTail++;
                           if (issTail >= REORDER_WIDTH)
                             issTail = 0;
                        }
                      
                      issue_ptr = NULL; */
                     //      if (cycle_count > 9358580)
                      //        fprintf(stderr," BIT = %d hdPtr = %d, ID = %d, level = %d\n", thrdBits.BITS, thrdBits.hdPtr, reoBufferPtr->thrdID, reoBufferPtr->thrdBitPtr);
//                           fprintf(stderr," Reset Level thrdID = %d ParLevel %d to %d\n", reoBufferPtr->thrdID, thrdPC_Q.thrdParentLevel[ reoBufferPtr->thrdID ], reoBufferPtr->thrdBitPtr);
                       //if (cycle_count > 9504900)
                        //   print_reorder();

                        thrdPC_Q.thrdParentLevel[ reoBufferPtr->thrdID ] = reoBufferPtr->thrdBitPtr;  // Current Thread becomes the Parent Thread

                     //  fprintf(stderr," Resolved ThrdID = %d PC %d BITS = %d Ptr = %d followBr = %d\n", reoBufferPtr->thrdID, reoBufferPtr->regs_PC, thrdBits.BITS, thrdBits.hdPtr, reoBufferPtr->followBr);

                     //if ( cycle_count > 9000 ) 
                     //{   fprintf( stderr, " BITS = %d hdptr = %d\n", thrdBits.BITS, thrdBits.hdPtr );
                      //}
                    } // if stallBubble
                 } // if  F_CTRL|F_COND|F_DIRJMP

                if ( reoBufferPtr->regs_NPC )
                {
                  bpred_update(pred,
                               /* branch address */reoBufferPtr->regs_PC,
                               /* actual target address */reoBufferPtr->regs_NPC,
                               /* taken? */reoBufferPtr->regs_NPC != (reoBufferPtr->regs_PC +
                                                       sizeof(md_inst_t)),
                               /* pred taken? */ predTaken,
                               /* correct pred? */reoBufferPtr->pred_PC == reoBufferPtr->regs_NPC,
                               /* opcode */op,
			       /* thrdID */ reoBufferPtr->thrdID,
                               /* predictor update ptr */&reoBufferPtr->dir_update);

/*                if ( cycle_count > 400 ) {
                   /*  inst.a = reoBufferPtr->inst_a;
                     inst.b = reoBufferPtr->inst_b;
                     md_print_insn( inst,          
                       reoBufferPtr->regs_PC,            
                       stderr);            
                     fprintf(stderr, "\n");
                  
                 unsigned int fe_pred_PC = btb_lookup ( pred, reoBufferPtr->regs_PC );
                 
                 fprintf(stderr," Saved ThrdID = %d PC %d Pred %d UnRes = %d followBr = %d\n", reoBufferPtr->thrdID, reoBufferPtr->regs_PC, fe_pred_PC, unResolvedCntr, reoBufferPtr->followBr);
                }*/

                  confpred_update ( confpred, /* Confidence Pred Instance */
                                  /* branch address */reoBufferPtr->regs_PC,
                                  /* actual target address */reoBufferPtr->regs_NPC,
                                  /* taken? */reoBufferPtr->regs_NPC != (reoBufferPtr->regs_PC +
                                                       sizeof(md_inst_t)),
                                  /* correct pred? */reoBufferPtr->pred_PC == reoBufferPtr->regs_NPC,
                                  op
                                ); 
                       
                  }
             }
        //--------------------------------------------------------------------//

          } //Precise Exception
         else
         {  // If Mis-speculated Instruction
       //     if ( /* thrdPC_Q.completeBit &&/ reoBufferPtr->thrdIDValid ) 
          /*  {
            //---------Check if the Thread is good to complete---------
               thrdPC_Q.threadCount[reoBufferPtr->thrdID]--;

               if ( thrdPC_Q.threadCount[reoBufferPtr->thrdID] == 0 )
               {
        	 if (!thrdPC_Q.valid[reoBufferPtr->thrdID])
                 {
                    thrdPC_Q.busy[reoBufferPtr->thrdID] = 0; 
                    thrdPC_Q.bitPtr[reoBufferPtr->thrdID] = 0; 
                 }// if flushout
               } // if threadCoutn == 0
             // Invalidate only if it matches as later insn can change it
            // if (rRegPtr[reoBufferPtr->thrdBitPtr][reoBufferPtr->thrdID].ptr[reoBufferPtr->rd] == reoBufferPtr->rd_new )
            
              if ( thrdPC_Q.threadCount[reoBufferPtr->thrdID] < 0 ) { fprintf(stderr,"count"); exit(-1); }
            } // if reoThrdValid*/
         
             //----------------Ld/Sw Buffer Update----------------
          //  if (rRegPtr[reoBufferPtr->thrdBitPtr][reoBufferPtr->thrdID].ptr[reoBufferPtr->rd] == reoBufferPtr->rd_new )
           //    rRegPtr[reoBufferPtr->thrdBitPtr][reoBufferPtr->thrdID].valid[reoBufferPtr->rd] = 0; //Default Level +1

              if ( reoBufferPtr->inOrder )
              {
                if (sw_hdPtr != sw_tPtr )
                {
                  sw_misRecovery(0);
                  sw_buffer[sw_hdPtr].valid = 0;
                  sw_hdPtr++;  \
                  if ((unsigned)sw_hdPtr >= REORDER_WIDTH) \
                   sw_hdPtr = 0; \
                 }
              }

              if ( reoBufferPtr->lD )
              {
                if (ld_hdPtr != ld_tPtr )
                {
                  ld_buffer[ld_hdPtr].valid = 0;
                  ld_hdPtr++;  \
                  if ((unsigned)ld_hdPtr >= REORDER_WIDTH) \
                   ld_hdPtr = 0; \

               //   if ( cycle_count > 10329040 ) \
                //   fprintf(stderr,"mis ldHptr = %d cycle = %d \n",ld_hdPtr, cycle_count); 
                 }
               }
             //---------Check Dependencies--------------------//
                 wakeUpPtr = &wakeUpTbl[ tailPtr ];
                  if ( wakeUpPtr->valid )
                  {
                     wakeUpPtr->valid  = 0;
                     wakeUpPtr->slotLength = 0; //Reset
                  }
      //------Free the Old Register-----------
            //rRegPtr[reoBufferPtr->thrdBitPtr][reoBufferPtr->thrdID].valid[reoBufferPtr->rd] = 0; //Default Level +1
            OUTPUT_BUSY->wr_enable = 1; //fprintf(stderr," Not Updated\n" );
            OUTPUT_BUSY->wr_busy_cp[i] = 0;
            OUTPUT_BUSY->wr_addr_cp[i] =  reoBufferPtr->rd_new;
        //    if ( cycle_count > 3420 )
         //   if ( cycle_count > 9790015 )
          //   fprintf( stderr,"reo = %d CMP C %d\n", tailPtr, OUTPUT_BUSY->wr_addr_cp[i]); 
         } // End of if (misspeculation)
     //-----Reset Instruction Window Entry--------
         reoBufferPtr->busy = 0;
         reoBufferPtr->issued = 0;
         reoBufferPtr->finished = 0;
         reoBufferPtr->misspeculated = 0;

         //-----------------------------------------------------------
          tailCntr = ( (tailPtr + 1) % REORDER_WIDTH );
          if ( tailCntr != headPtr )
            {
              tailPtr  = tailCntr;
            }
           else
            {
          //Breaks and waits till the instruction in this slot finishes.
       //-------------TEST-------------------------------
             tailPtr  = tailCntr;// (tailPtr + 1) % REORDER_WIDTH;  //next tail Pointer
             break;
           }
      //-----------------------------------------------------------
        }
    else
       {
          break; // If the top instruction is not finished. 
       }

         if ( !mem_violation_exe ) 
           check_regs( ); // Have to check at Update
   } // end of for loop

   if ( wdTimer > REORDER_WIDTH ) // Watch-Dog Timer
      { print_reorder(); print_regs(); fprintf ( stderr, " Explode!! tail = %d cycle = %d \n", tailPtr, cycle_count );
       exit(0);
       }
  //------Limit Instruction Execution to 6Billion----
  if (sim_num_insn >= max_exe_insn_6B )
       {
        print_reorder();
        fprintf(stderr,"Final Unresol %u\n", unResolvedCntr);
       for (unsigned int k=0; k < 16; k++)
         fprintf(stderr, "\nN Br Conf Hits = %llu misses = %llu \n ", confpred->conf.hits[k], confpred->conf.miss[k]);
        longjmp(sim_exit_buf, /* exitcode + fudge */regs.regs_R[4]+1); }
                                                                                                                                                                 
   else if (sim_num_insn >= max_exe_insn_5B && !max_prn_insn_5B  )
    { sim_print_stats(stderr); max_prn_insn_5B = 1;}
                                                                                                                                                                 
   else if (sim_num_insn >= max_exe_insn_4B && !max_prn_insn_4B )
     { sim_print_stats(stderr); max_prn_insn_4B = 1; }
                                                                                                                                                                 
   else if (sim_num_insn >= max_exe_insn_3B && !max_prn_insn_3B )
     { sim_print_stats(stderr); max_prn_insn_3B = 1; }
                                                                                                                                                                 
   else if (sim_num_insn >= max_exe_insn_2B && !max_prn_insn_2B )
      { sim_print_stats(stderr); max_prn_insn_2B = 1; }
                                                                                                                                                                 
   else if (sim_num_insn >= max_exe_insn_1B && !max_prn_insn_1B )
      { sim_print_stats(stderr); max_prn_insn_1B = 1; }

//   if (sim_num_insn >= max_exe_insn )
 //      { longjmp(sim_exit_buf, /* exitcode + fudge */regs.regs_R[4]+1); }
}


/*******Additional Support Modules for Load Forwarding, ByPassing and Memory Violation Recovery***********/
 //*********If data are equal; then Recover since it has been from the wrong path's sw*******
inline void  sw_misRecovery (bool sb_insn) \
 { \
   unsigned int temp_ld_ptr = 0;\
 //   fprintf( stderr," SW Recover %d \n", cycle_count);
   temp_ld_ptr = ld_hdPtr; \

     while ( temp_ld_ptr != (unsigned) ld_tPtr )
     { \
       if ( (ld_buffer[ temp_ld_ptr ].ld_addr >> 2) == (sw_buffer[ sw_hdPtr ].sw_addr >> 2) && ld_buffer[ temp_ld_ptr ].valid) { \
             if ( ld_buffer[temp_ld_ptr].sw_uniqueID == sw_buffer[ sw_hdPtr ].sw_uniqueID ) { \
                        ld_buffer[ temp_ld_ptr ].mem_recover = 1;        \
                        //ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
              //       return reoBuffer[ld_buffer[temp_ld_ptr].reoID].regs_PC; 
                }\
                     /*  fprintf ( stderr,"SW_Recovery 1 %d to %d = %d \n", sw_buffer[ sw_hdPtr ].reoID, ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].sw_data);*/\
                     /* SET_NEW_GPR( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].rd_new, sw_buffer[ sw_hdPtr ].sw_data);*//* break;*/  \
           }\
        temp_ld_ptr++;\
        if ( temp_ld_ptr >= REORDER_WIDTH ) temp_ld_ptr = 0; 
      }\
 }


/*******Additional Support Modules for Load Forwarding, ByPassing and Memory Violation Recovery***********/

inline void  sw_ldRecovery (bool sb_insn) \
 { \
   unsigned int temp_ld_ptr = 0;\
   bool addrMatch = 0;
 //   fprintf( stderr," SW Recover %d \n", cycle_count);
   temp_ld_ptr = ld_hdPtr; \

   if (  !sb_insn ){ \
     while ( temp_ld_ptr != (unsigned) ld_tPtr ) { \
      if ( (ld_buffer[ temp_ld_ptr ].ld_addr >> 2) == (sw_buffer[ sw_hdPtr ].sw_addr >> 2) /*&& ld_buffer[ temp_ld_ptr ].thrdID == sw_buffer[ sw_hdPtr ].thrdID*/ &&\
               ld_buffer[ temp_ld_ptr ].valid) { \
          if ( headPtr > tailPtr ) { \
              if ( ld_buffer[ temp_ld_ptr ].reoID > sw_buffer[ sw_hdPtr ].reoID ) {\
                 if ( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].issued &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                    if ( (ld_buffer [ temp_ld_ptr ].ld_data !=  sw_buffer[ sw_hdPtr ].sw_data)  && !((ld_buffer[temp_ld_ptr].sw_uniqueID > sw_buffer[ sw_hdPtr ].sw_uniqueID) & (ld_buffer[temp_ld_ptr].ld_fwd))  /* && !ld_buffer[temp_ld_ptr].match_exists */) { \
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      // fprintf(stderr,"cycle %d pc = %d ld = %d sw_data = %d\n",cycle_count, reoBuffer[tailPtr].regs_PC, ld_buffer [ temp_ld_ptr ].ld_data, sw_buffer[ sw_hdPtr ].sw_data);
                       //fprintf(stderr,"cycle %d pc = %d\n",cycle_count, reoBuffer[tailPtr].regs_PC); print_reorder();
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
              //       return reoBuffer[ld_buffer[temp_ld_ptr].reoID].regs_PC; 
                    }\
                     /*  fprintf ( stderr,"SW_Recovery 1 %d to %d = %d \n", sw_buffer[ sw_hdPtr ].reoID, ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].sw_data);*/\
                     /* SET_NEW_GPR( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].rd_new, sw_buffer[ sw_hdPtr ].sw_data);*//* break;*/  \
                  }\
                 if ( !ld_buffer[ temp_ld_ptr ].is_lw &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                      lb_mem_recvr++;
                      ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                  }\
                }\
             }\
            else {\
               /*  fprintf ( stderr,"SW_LD Recovery 2 ld %d sw %d \n", ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].reoID );*/\
              if ( ld_buffer[ temp_ld_ptr ].reoID < tailPtr  ) { \
               if ( ld_buffer[ temp_ld_ptr ].reoID <  sw_buffer[ sw_hdPtr ].reoID ) { \
                 if ( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].issued /* && !ld_buffer[ temp_ld_ptr ].ld_fwd*/ &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                    if ( (ld_buffer [ temp_ld_ptr ].ld_data !=  sw_buffer[ sw_hdPtr ].sw_data)  && !((ld_buffer[temp_ld_ptr].sw_uniqueID > sw_buffer[ sw_hdPtr ].sw_uniqueID) & (ld_buffer[temp_ld_ptr].ld_fwd))  /* && !ld_buffer[temp_ld_ptr].match_exists */) { \
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                       //fprintf(stderr,"2 cycle %d\n",cycle_count); print_reorder();
                     //return reoBuffer[ld_buffer[temp_ld_ptr].reoID].regs_PC; 
                    }\
                      /* fprintf ( stderr,"SW_Recovery 2 %d to %d = %d \n", sw_buffer[ sw_hdPtr ].reoID, ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].sw_data);*/\
                     /* SET_NEW_GPR( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].rd_new, sw_buffer[ sw_hdPtr ].sw_data);  && ld_buffer[temp_ld_ptr].sw_reoID == tailPtr*/  \
                  }\
                 if ( !ld_buffer[ temp_ld_ptr ].is_lw &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                      lb_mem_recvr++;
                      ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                  }\
                }\
               }\
              else if ( ld_buffer[ temp_ld_ptr ].reoID > tailPtr ){ \
               if ( ld_buffer[ temp_ld_ptr ].reoID >  sw_buffer[ sw_hdPtr ].reoID ) { \
                 if ( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].issued &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                    if ( (ld_buffer [ temp_ld_ptr ].ld_data !=  sw_buffer[ sw_hdPtr ].sw_data)  && !((ld_buffer[temp_ld_ptr].sw_uniqueID > sw_buffer[ sw_hdPtr ].sw_uniqueID) & (ld_buffer[temp_ld_ptr].ld_fwd))  /* && !ld_buffer[temp_ld_ptr].match_exists */) { \
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                       //fprintf(stderr," 3 cycle %d\n",cycle_count); print_reorder();
               //      return reoBuffer[ld_buffer[temp_ld_ptr].reoID].regs_PC; 
                     }\
                     /* SET_NEW_GPR( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].rd_new, sw_buffer[ sw_hdPtr ].sw_data);*/   \
                 }\
                 if ( !ld_buffer[ temp_ld_ptr ].is_lw &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                      lb_mem_recvr++;
                      ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                  }\
                }\
               }\
             }\
           }\
       temp_ld_ptr++;\
       if ( temp_ld_ptr >= REORDER_WIDTH ) temp_ld_ptr = 0; } \
      }\
     else {\
      /*if ( (ld_buffer[ temp_ld_ptr ].ld_addr <= (sw_buffer[ sw_hdPtr ].sw_addr + 3) &&  ld_buffer[ temp_ld_ptr ].ld_addr >= (sw_buffer[ sw_hdPtr ].sw_addr - 3)) && ld_buffer[ temp_ld_ptr ].valid) { \*/
     while ( temp_ld_ptr != ld_tPtr ) { \
      addrMatch = 0;
      if ( ld_buffer[ temp_ld_ptr ].is_lb )
            addrMatch = ((ld_buffer[ temp_ld_ptr ].ld_addr) == (sw_buffer[ sw_hdPtr ].sw_addr));
      else if ( ld_buffer[ temp_ld_ptr ].is_lh )
            addrMatch = ((ld_buffer[ temp_ld_ptr ].ld_addr >> 1) == (sw_buffer[ sw_hdPtr ].sw_addr >> 1));
      else if ( ld_buffer[ temp_ld_ptr ].is_lw )
            addrMatch = ((ld_buffer[ temp_ld_ptr ].ld_addr >> 2) == (sw_buffer[ sw_hdPtr ].sw_addr >> 2));
     /* if ( cycle_count > 304300 && ld_buffer[ temp_ld_ptr ].valid)
      fprintf(stderr," cycle %u ld_addr[%d] = %u sw_addr[%d] = %u\n", cycle_count, ld_buffer[ temp_ld_ptr ].reoID, ((ld_buffer[ temp_ld_ptr ].ld_addr)>>2  ),  sw_buffer[ sw_hdPtr ].reoID,( (sw_buffer[ sw_hdPtr ].sw_addr)>>2 ));*/ 
      if ( addrMatch &&/* ld_buffer[ temp_ld_ptr ].thrdID == sw_buffer[ sw_hdPtr ].thrdID  &&*/ \
              ld_buffer[ temp_ld_ptr ].valid) { \
          if ( headPtr > tailPtr ) { \
              if ( ld_buffer[ temp_ld_ptr ].reoID > sw_buffer[ sw_hdPtr ].reoID ) {\
                 if ( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].issued  &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                    if ( (ld_buffer [ temp_ld_ptr ].ld_data != ((ld_buffer[temp_ld_ptr].is_signed) ? (word_t)(sword_t)sw_buffer[ sw_hdPtr ].sw_data : sw_buffer[ sw_hdPtr ].sw_data))  && !((ld_buffer[temp_ld_ptr].sw_uniqueID > sw_buffer[ sw_hdPtr ].sw_uniqueID) & (ld_buffer[temp_ld_ptr].ld_fwd))  /* && !ld_buffer[temp_ld_ptr].match_exists */) { \
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                       //fprintf(stderr," 4 cycle %d\n",cycle_count); print_reorder();
                  //   return reoBuffer[ld_buffer[temp_ld_ptr].reoID].regs_PC; 
                     }\
                     /*  fprintf ( stderr,"SW_Recovery 1 %d to %d = %d \n", sw_buffer[ sw_hdPtr ].reoID, ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].sw_data);*/\
                     /* SET_NEW_GPR( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].rd_new, sw_buffer[ sw_hdPtr ].sw_data);*/   \
                  }\
                   else if ( (!reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].finished & ld_buffer[temp_ld_ptr].is_lw)  &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                        sb_mem_recvr++;
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                        ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                      } 
                }\
             }\
            else {\
               /*  fprintf ( stderr,"SW_LD Recovery 2 ld %d sw %d \n", ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].reoID );*/\
              if ( ld_buffer[ temp_ld_ptr ].reoID < tailPtr ) { \
               if ( ld_buffer[ temp_ld_ptr ].reoID <  sw_buffer[ sw_hdPtr ].reoID ) { \
                 if ( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].issued &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                    if ( (ld_buffer [ temp_ld_ptr ].ld_data !=  ((ld_buffer[temp_ld_ptr].is_signed) ? (word_t)(sword_t)sw_buffer[ sw_hdPtr ].sw_data : sw_buffer[ sw_hdPtr ].sw_data))  && !((ld_buffer[temp_ld_ptr].sw_uniqueID > sw_buffer[ sw_hdPtr ].sw_uniqueID) & (ld_buffer[temp_ld_ptr].ld_fwd))  /* && !ld_buffer[temp_ld_ptr].match_exists */) { \
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                      ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                       //fprintf(stderr," 5 cycle %d\n",cycle_count); print_reorder();
                    // return reoBuffer[ld_buffer[temp_ld_ptr].reoID].regs_PC; 
                     }\
                      /* fprintf ( stderr,"SW_Recovery 2 %d to %d = %d \n", sw_buffer[ sw_hdPtr ].reoID, ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].sw_data);*/\
                     /* SET_NEW_GPR( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].rd_new, sw_buffer[ sw_hdPtr ].sw_data);*/   \
                  }\
                   else if ( (!reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].finished & ld_buffer[temp_ld_ptr].is_lw)  &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                        sb_mem_recvr++;
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                        ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                      } 
                }\
               }\
              else if ( ld_buffer[ temp_ld_ptr ].reoID > tailPtr ){ \
               if ( ld_buffer[ temp_ld_ptr ].reoID >  sw_buffer[ sw_hdPtr ].reoID ) { \
                 if ( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].issued  &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                    if ( (ld_buffer [ temp_ld_ptr ].ld_data != ((ld_buffer[temp_ld_ptr].is_signed) ? (word_t)(sword_t)sw_buffer[ sw_hdPtr ].sw_data : sw_buffer[ sw_hdPtr ].sw_data))  && !((ld_buffer[temp_ld_ptr].sw_uniqueID > sw_buffer[ sw_hdPtr ].sw_uniqueID) & (ld_buffer[temp_ld_ptr].ld_fwd))  /* && !ld_buffer[temp_ld_ptr].match_exists */) { \
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                        ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                       //fprintf(stderr," 6 cycle %d\n",cycle_count); print_reorder();
                   //  return reoBuffer[ld_buffer[temp_ld_ptr].reoID].regs_PC; 
                    }\
                      /* fprintf ( stderr,"SW_Recovery 4 %d to %d = %d \n", sw_buffer[ sw_hdPtr ].reoID, ld_buffer[ temp_ld_ptr ].reoID, sw_buffer[ sw_hdPtr ].sw_data);*/\
                     /* SET_NEW_GPR( reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].rd_new, sw_buffer[ sw_hdPtr ].sw_data);*/   \
                 }\
                   else if ( (!reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].finished & ld_buffer[temp_ld_ptr].is_lw)  &&  !reoBuffer[ld_buffer[ temp_ld_ptr ].reoID].misspeculated ) {\
                        sb_mem_recvr++;
                        ld_buffer[ temp_ld_ptr ].mem_violation = 1;        \
                        ld_buffer[ temp_ld_ptr ].sw_pc = reoBuffer[tailPtr].regs_PC;      \
                      } 
                }\
               }\
             }\
           }\
       temp_ld_ptr++;\
       if ( temp_ld_ptr >= REORDER_WIDTH ) temp_ld_ptr = 0; } \
      }\
 }

bool threadMatch( unsigned targetLevel, unsigned targetID, unsigned thrdBitPtr, unsigned thrdID )
 {
   unsigned int thrdMask = 1;
   unsigned int levelCnt = 0, thrdLevel = 0;
   unsigned int curThrdID = 0;
   unsigned int siblingThrdID = 0;
   bool regMapped = 0;
   if ( targetLevel ==0 && targetID == 0 ) return 1; //Default Thread Match

    //-----------Finding Top UnResolved Level------------
       /* unsigned int topLevel = 0; // top level unresolved branch level
        unsigned int tempHdPtr = 0;
        if ( thrdBits.hdPtr !=0 )
        {
          tempHdPtr = thrdBits.hdPtr;
          for (unsigned i = 0; i < THREAD_LEVEL; i++)
          {
            tempHdPtr = tempHdPtr >> 1; 
            topLevel ++;
            if ( tempHdPtr == 0 )
            {
              break;
            }
          }
       //   fprintf(stderr," entered %d \n", topLevel);
        }
        else
           topLevel = 1;*/
    //--------------------------------------------------

      
      levelCnt = 0;
     // thrdLevel = reoBufferPtr->thrdBitPtr; //Start from Current Level
      //curThrdID = reoBufferPtr->thrdID; //Start from Current ThrdID
    //  thrdLevel = thrdBitPtr;
     // curThrdID = thrdID;

       if ( !regMapped )
        {
           levelCnt = 0;
           thrdLevel = thrdBitPtr; //Start from Current Level

           curThrdID = thrdID; //Start from Current ThrdID
           while ( levelCnt < THREAD_LEVEL ) 
           { // Checks for same ThrdID
             //if ( curThrdID == INPUT->thrdID[i] )
              // Check if the Renamed Register is Valid 
                //   if ( cycle_count > 10329040 )
                 //   fprintf(stderr,"bitPtr = %d ThrdLevel = %d\n", targetLevel, thrdLevel);

               if ( targetID == curThrdID && targetLevel == thrdLevel)//VALID_RRP_RS(i) == 1 ) //rRegPtr.valid[in_rs] == 1 )
                {//-------Read from the RRP--------------------
                    regMapped = 1;
               //   if (cycle_count > 17575000 )
                //    fprintf(stderr,"Matched ThrdLevel = %d\n", thrdLevel);

                     return 1;
      //             fprintf(stderr," RT[%d] = %d\n", INPUT->rt[i], rRegPtr[thrdLevel][curThrdID].ptr[ INPUT->rt[i] ]);
                    //break; // break while
                 }
             if ( !regMapped ) 
             {
                if (thrdLevel == 0) break;
                //if (thrdLevel == thrdBits.hdPtr) break; // TopLevel

                thrdMask = 1;
                thrdMask = ( thrdMask <<  (thrdLevel - 1)); // Since Level Count is Sub. earlier 
                siblingThrdID = ( thrdMask ^  curThrdID ); // 2^(thrdLevel+1)/2 
                if ( (thrdPC_Q.thrdParentLevel[curThrdID] == thrdPC_Q.thrdParentLevel[siblingThrdID]) == 1 )
                { levelCnt = THREAD_LEVEL; break;}
               //   if (cycle_count > 7200 )
               //       fprintf(stderr," thrd Mask = %d curID = %d sib = %d par = %d sib_par= %d\n",  thrdMask, curThrdID, siblingThrdID, thrdPC_Q.thrdParentID[curThrdID],thrdPC_Q.thrdParentID[siblingThrdID]);
                  thrdLevel = thrdLevel - 1; // Move above 1 thrdLevel
                  if (thrdLevel <= 0) 
                  {
                    thrdLevel = THREAD_LEVEL; // Move above 1 thrdLevel
                  }

                  if (thrdPC_Q.thrdParentID[ curThrdID ] == siblingThrdID && thrdPC_Q.thrdParentLevel[curThrdID] == thrdLevel ) 
                   {
                      //if ( thrdPC_Q.thrdIDValid[ siblingThrdID ] )
                         curThrdID = siblingThrdID;
                   }
               // if (cycle_count > 700)
                //          fprintf(stderr," RT PC = %d  thrd ID = %d lvl = %d top = %d hdPtr = %d\n", INPUT->regs_PC[i], curThrdID, thrdLevel, topLevel, thrdBits.hdPtr);

                levelCnt++;

                //prevThrdID = curThrdID - 2; // 2^(thrdLevel+1)/2 
                //if (prevThrdID < 0 ) prevThrdID = 0;
             } // !regMapped

            } // end of while(thrdLevel)
             

         } // !regMapped
       return 0;
  } // *******End of Thread Match()*************

/* To diable Load Bypass replace the function call at dispatch_main() with a 0 */
bool  ld_bypassLogic () \
{\
    int temp_sw_ptr = 0;\
    bool thrdMatch = 0;

   temp_sw_ptr = sw_tPtr; \
    while ( temp_sw_ptr != sw_hdPtr ){ \
     thrdMatch = 0;
     temp_sw_ptr--;
     if ( temp_sw_ptr < 0) {\
         temp_sw_ptr =  REORDER_WIDTH - 1;} \


     if ( sw_buffer[ temp_sw_ptr ].pred_sw_addr > 0 &&  reoBufferPtr->ld_pred_addr > 0 ) { \

       if (sw_buffer[temp_sw_ptr].valid)
       {
          if ( sw_buffer[temp_sw_ptr].thrdBitPtr == 0 )
            thrdMatch = 1;
          else
            thrdMatch = threadMatch( sw_buffer[temp_sw_ptr].thrdBitPtr, sw_buffer[temp_sw_ptr].thrdID, reoBufferPtr->thrdBitPtr, reoBufferPtr->thrdID );
       }
    
       if ( /*sw_buffer[ temp_sw_ptr ].thrdID == reoBufferPtr->thrdID*/thrdMatch  && (thrdPC_Q.valid[ sw_buffer[temp_sw_ptr].thrdID ]|followBrPred)  && sw_buffer[ temp_sw_ptr ].pred_sw_addr == reoBufferPtr->ld_pred_addr && sw_buffer[ temp_sw_ptr ].valid ) { \
                
          if ( headPtr > tailPtr ) { \
              if ( sw_buffer[ temp_sw_ptr ].reoID  < headPtr ) {\
                 if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    issReadyQ.swID = sw_buffer[ temp_sw_ptr ].reoID; 
                    return 0; //cannot bypass
                  }
                  break;
               }
             }
           else { \
              if ( sw_buffer[ temp_sw_ptr ].reoID <= tailPtr && headPtr  <= tailPtr ) { \
               if ( sw_buffer[ temp_sw_ptr ].reoID < headPtr ) { \
                 if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    issReadyQ.swID = sw_buffer[ temp_sw_ptr ].reoID; 
                    return 0;
                   }
                 }
               }
              else if ( sw_buffer[ temp_sw_ptr ].reoID >= tailPtr &&  headPtr >= tailPtr ){ \
               if ( sw_buffer[ temp_sw_ptr ].reoID < headPtr ) { \
                 if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    issReadyQ.swID = sw_buffer[ temp_sw_ptr ].reoID; 
                    return 0;
                   }
                   break;
                 }
               }
              else if ( sw_buffer[ temp_sw_ptr ].reoID >= tailPtr &&  headPtr <= tailPtr ){ \
               if ( sw_buffer[ temp_sw_ptr ].reoID >  headPtr ) { \
                 if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    issReadyQ.swID = sw_buffer[ temp_sw_ptr ].reoID; 
                    return 0;
                   }
                   break;
                 }
               }

            }
           // return 0;  //cannot by pass
          // }
         //  break;  // can by pass
          
           }
        }\
     //  if ( temp_sw_ptr <= 0) {\
      //     temp_sw_ptr =  REORDER_WIDTH;} \
       //  temp_sw_ptr--;
       } \

       return 1; //can byPass 
}



/*Load Forwarding Logic called by Machine_oo.def*/
/*No forwarding while is_sw = 0 => store byte or store half*/
inline bool  lw_forwardLogic (void) \
{\
   signed int temp_sw_ptr = 0;\
   bool thrdMatch = 0;
   bool lw_fwded = 0; \
   temp_sw_ptr = sw_tPtr; \
    while ( temp_sw_ptr != sw_hdPtr ){ \
     thrdMatch = 0;
     temp_sw_ptr--;
     if ( temp_sw_ptr < 0) {\
         temp_sw_ptr =  REORDER_WIDTH - 1;} \

     if (sw_buffer[temp_sw_ptr].valid)
      {
         if ( sw_buffer[temp_sw_ptr].thrdBitPtr == 0 ) \
            thrdMatch = 1;\
         else\
           thrdMatch = threadMatch( sw_buffer[temp_sw_ptr].thrdBitPtr, sw_buffer[temp_sw_ptr].thrdID, reoBufferPtr->thrdBitPtr, reoBufferPtr->thrdID );\
      }
      if ( /*(unsigned) sw_buffer[ temp_sw_ptr ].thrdID == reoBufferPtr->thrdID*/ thrdMatch &&  (thrdPC_Q.valid[ sw_buffer[temp_sw_ptr].thrdID ]|followBrPred)  && (unsigned) sw_buffer[ temp_sw_ptr ].sw_addr == (GPR_RT + OFS) && !(sw_buffer[ temp_sw_ptr ].is_sw ^ ld_buffer [ reoBufferPtr->ld_reoID ].is_lw) ) { \
          if ( headPtr > tailPtr ) { \
              if ( sw_buffer[ temp_sw_ptr ].reoID  <  ld_buffer [ reoBufferPtr->ld_reoID ].reoID ) {\
                    ld_buffer[  reoBufferPtr->ld_reoID ].match_exists = 1;   \
                 if ( reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated && sw_buffer[ temp_sw_ptr ].valid) {\
                    if ( ld_buffer[ reoBufferPtr->ld_reoID ].is_signed )
                     {
                       if (ld_buffer[ reoBufferPtr->ld_reoID ].is_lb)
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                       else
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                     }
                    else
                    {
                       SET_NEW_GPR( NEW_RD, (word_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                       ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                    }
                    ld_buffer [ reoBufferPtr->ld_reoID ].sw_uniqueID =  sw_buffer[ temp_sw_ptr ].sw_uniqueID; \
                    ld_buffer [ reoBufferPtr->ld_reoID ].ld_fwd = 1; \
             /*       if (cycle_count > 9630700)
                    fprintf(stderr," reoID = %d addr = %d sw_data = %d sw_reo = %d is_sw = %d\n", ld_buffer [ reoBufferPtr->ld_reoID ].reoID, (GPR_RT + OFS), sw_buffer[ temp_sw_ptr ].sw_data, sw_buffer[ temp_sw_ptr ].reoID, sw_buffer[ temp_sw_ptr ].is_sw);  
              */      lw_fwded = 1; \
                    return 1;
                  }\
               /* else if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished  &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    fprintf ( stderr,"RE_ISSUED \n");\
                    reoBufferPtr->issued = 0; \
                    wakeUpPtr = &wakeUpTbl[ sw_buffer[ temp_sw_ptr ].reoID ];\
		    wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = ld_buffer [ reoBufferPtr->ld_reoID ].reoID ;\ 
	            wakeUpPtr->slotLength++;\
                    wakeUpPtr->valid = 1; \
                 }*/\
                /* print_reorder();*/\
                 /*fprintf( stderr,"SW 1 Match Found: %d and %d \n", ld_buffer [ reoBufferPtr->ld_reoID ].reoID, sw_buffer[ temp_sw_ptr ].reoID ); */break; } \
             } \
           else { \
              if ( sw_buffer[ temp_sw_ptr ].reoID < tailPtr && ld_buffer [ reoBufferPtr->ld_reoID ].reoID  < tailPtr ) { \
               if ( sw_buffer[ temp_sw_ptr ].reoID <  ld_buffer [ reoBufferPtr->ld_reoID ].reoID ) { \
                    ld_buffer[  reoBufferPtr->ld_reoID ].match_exists = 1;   \
                 if ( reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated && sw_buffer[ temp_sw_ptr ].valid/*&& sw_buffer[ temp_sw_ptr ].sw_dataValid*/) {\
                    if ( ld_buffer[ reoBufferPtr->ld_reoID ].is_signed )
                     {
                       if (ld_buffer[ reoBufferPtr->ld_reoID ].is_lb)
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                       else
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                     }
                    else
                    {
                       SET_NEW_GPR( NEW_RD, (word_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                       ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                    }
                    ld_buffer [ reoBufferPtr->ld_reoID ].sw_uniqueID =  sw_buffer[ temp_sw_ptr ].sw_uniqueID; \
                    ld_buffer [ reoBufferPtr->ld_reoID ].ld_fwd = 1; \
                    lw_fwded = 1; \
                    return 1;
                  }\
               /* else if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished  &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    fprintf ( stderr,"RE_ISSUED \n");\
                    reoBufferPtr->issued = 0; \
                    wakeUpPtr = &wakeUpTbl[ sw_buffer[ temp_sw_ptr ].reoID ];\
		    wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = ld_buffer [ reoBufferPtr->ld_reoID ].reoID ;\ 
	            wakeUpPtr->slotLength++;\
                    wakeUpPtr->valid = 1; \
                 }*/\
                 /*print_reorder();*/\
                 /*fprintf( stderr,"SW 2 Match Found: %d and %d \n", ld_buffer [ reoBufferPtr->ld_reoID ].reoID, sw_buffer[ temp_sw_ptr ].reoID ); */break; } \
              } \
              else if ( sw_buffer[ temp_sw_ptr ].reoID >= tailPtr ){ \
               if ( sw_buffer[ temp_sw_ptr ].reoID < ld_buffer [ reoBufferPtr->ld_reoID ].reoID &&  ld_buffer [ reoBufferPtr->ld_reoID ].reoID > tailPtr ) { \
                    ld_buffer[  reoBufferPtr->ld_reoID ].match_exists = 1;   \
                 if ( reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated && sw_buffer[ temp_sw_ptr ].valid/*&& sw_buffer[ temp_sw_ptr ].sw_dataValid*/) {\
                    if ( ld_buffer[ reoBufferPtr->ld_reoID ].is_signed )
                     {
                       if (ld_buffer[ reoBufferPtr->ld_reoID ].is_lb)
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                       else
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                     }
                    else
                    {
                       SET_NEW_GPR( NEW_RD, (word_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                       ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                    }
                    ld_buffer [ reoBufferPtr->ld_reoID ].sw_uniqueID =  sw_buffer[ temp_sw_ptr ].sw_uniqueID; \
                    ld_buffer [ reoBufferPtr->ld_reoID ].ld_fwd = 1; \
                    lw_fwded = 1; \
                    return 1;
                  }\
                /*else if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished  &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    fprintf ( stderr,"RE_ISSUED \n");\reoBufferPtr->ld_reoID 
                    reoBufferPtr->issued = 0; \
                    wakeUpPtr = &wakeUpTbl[ sw_buffer[ temp_sw_ptr ].reoID ];\
		    wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = ld_buffer [ reoBufferPtr->ld_reoID ].reoID ;\ 
	            wakeUpPtr->slotLength++;\
                    wakeUpPtr->valid = 1; \
                 }*/\
                 /*print_reorder();*/\
                 /*fprintf( stderr,"SW 3 Match Found: %d and %d \n", ld_buffer [ reoBufferPtr->ld_reoID ].reoID, sw_buffer[ temp_sw_ptr ].reoID ); */break; } \
              else if (  ld_buffer [ reoBufferPtr->ld_reoID ].reoID < tailPtr ){ \
               if ( sw_buffer[ temp_sw_ptr ].reoID >  ld_buffer [ reoBufferPtr->ld_reoID ].reoID ) { \
                    ld_buffer[  reoBufferPtr->ld_reoID ].match_exists = 1;   \
                 if ( reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated && sw_buffer[ temp_sw_ptr ].valid/*&& sw_buffer[ temp_sw_ptr ].sw_dataValid*/) {\
                    if ( ld_buffer[ reoBufferPtr->ld_reoID ].is_signed )
                     {
                       if (ld_buffer[ reoBufferPtr->ld_reoID ].is_lb)
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(sbyte_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                       else
                       {
                         SET_NEW_GPR( NEW_RD, (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                         ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)(sword_t)(shalf_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                       }
                     }
                    else
                    {
                       SET_NEW_GPR( NEW_RD, (word_t)sw_buffer[ temp_sw_ptr ].sw_data);  \
                       ld_buffer [ reoBufferPtr->ld_reoID ].ld_data = (word_t)sw_buffer[ temp_sw_ptr ].sw_data; \
                    }
                    ld_buffer [ reoBufferPtr->ld_reoID ].sw_uniqueID =  sw_buffer[ temp_sw_ptr ].sw_uniqueID; \
                    ld_buffer [ reoBufferPtr->ld_reoID ].ld_fwd = 1; \
                    lw_fwded = 1; \
                    return 1;
                  }\
                /*else if ( !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].finished  &&  !reoBuffer[sw_buffer[ temp_sw_ptr ].reoID].misspeculated ) {\
                    fprintf ( stderr,"RE_ISSUED \n");\
                    reoBufferPtr->issued = 0; \
                    wakeUpPtr = &wakeUpTbl[ sw_buffer[ temp_sw_ptr ].reoID ];\
		    wakeUpPtr->slotID[ wakeUpPtr->slotLength ] = ld_buffer [ reoBufferPtr->ld_reoID ].reoID;\ 
	            wakeUpPtr->slotLength++;\
                    wakeUpPtr->valid = 1; \
                 }*/\
               /*  print_reorder();*/\
                 /*fprintf( stderr,"SW 4 Match Found: %d and %d \n", ld_buffer [ reoBufferPtr->ld_reoID ].reoID, sw_buffer[ temp_sw_ptr ].reoID );*/ break; } \
                 } \
              }\
           } \
        } \
     //  if ( temp_sw_ptr <= 0) {\
           temp_sw_ptr =  REORDER_WIDTH;} \
      //   temp_sw_ptr--;
        } \
      // return lw_fwded;
       return 0;
}

void check_regs( )
{
   int reg;
// fprintf(stderr,"Checking Regs\n");
  if ( regs.regs_PC )
  {            
   for (  i= 0;  i < MD_NUM_IREGS; i++ )
    {
       // if ( rRegPtr[0].valid[ i ] )
        //      reg =  rRegPtr[0].ptr[i];
        // else
         //     reg =  aRegPtr[i];
      
       if ( regs.regs_R[i] != regs_cp.regs_R[ aRegPtr[i] ]  )
       {
            fprintf(stderr,"CycleCount %d \t ", cycle_count );
            fprintf(stderr,"complete insn %u\n", sim_num_insn);
            fprintf(stderr,"PC %d \t ", regs.regs_PC);
               md_print_insn( inst,          
                    regs.regs_PC,            
                    stderr);            
             fprintf(stderr, "\n");
           fprintf(stderr,"Register %d: Reo %d  Does not match %d and %d;aregPtr= %d \n",i, tailPtr, regs.regs_R[i], regs_cp.regs_R[ aRegPtr[i] ], aRegPtr[i] );
           fprintf(stderr,"Final Unresol %u\n", unResolvedCntr);
           print_reorder();
           print_regs();
           exit(0);
       }

   }

   if (  regs.regs_C.lo !=  regs_cp.regs_R[ aRegPtr[32] ] )
    {
            fprintf(stderr," LO CycleCount %d \t ", cycle_count );
            fprintf(stderr,"PC %d \t ", regs.regs_PC);
               md_print_insn( inst,          
                    regs.regs_PC,            
                    stderr);            
             fprintf(stderr, "\n");
           fprintf(stderr,"Register Lo:  Does not match %d and %d;addr= %d \n", regs.regs_C.lo, regs_cp.regs_R[ aRegPtr[32] ], aRegPtr[32] );
           print_reorder();
           print_regs();
           exit(0);
    }

   if (  regs.regs_C.hi != regs_cp.regs_R2[ aRegPtr[32] ] )
    {
            fprintf(stderr," HI CycleCount %d \t ", cycle_count );
            fprintf(stderr,"PC %d \t ", regs.regs_PC);
               md_print_insn( inst,          
                    regs.regs_PC,            
                    stderr);            
             fprintf(stderr, "\n");
           fprintf(stderr,"Register HI:  Does not match %d and %d;addr= %d \n", regs.regs_C.hi, regs_cp.regs_R2[ aRegPtr[32] ], aRegPtr[32] );
           print_reorder();
           print_regs();
           exit(0);
    }
  }
}

bool speculation_check( int  tailIndex )
{
   unsigned int mNPC;
   
   ////fprintf(stderr," tail = %d ", tailIndex );
  if ( reoBuffer[tailIndex].regs_NPC == 0 )
      reoBuffer[tailIndex].regs_NPC = reoBuffer[tailIndex].regs_PC + sizeof(md_inst_t);
 //Disable PredPC; later models should have it enabled.
   /*if ( reoBuffer[tailIndex].followBr )
    { // No prediciton
      mNPC = reoBuffer[tailIndex].regs_PC + sizeof(md_inst_t);
    }
   else*/ if (reoBuffer[ tailIndex ].pred_PC > 10000 ) 
    {
       mNPC = reoBuffer[tailIndex].pred_PC;
       //fprintf(stderr," predPC =  %d ", mNPC );
    }
   else
    {
      mNPC = reoBuffer[tailIndex].regs_PC + sizeof(md_inst_t);
    }

   if ( reoBuffer[ tailIndex ].regs_NPC != mNPC )
    {
     //  if ( !reoBuffer[ tailIndex ].thrdIDValid ) 
         recovery_logic();
       return 1;
    }
       return 0;
}

/*bool isThreadIDFree ()
{

   for ( int i = 0; i < THREAD_WIDTH; i++ )
    {
       if ( thrdPC_Q.threadCount[i] )
         return 0;
    }

   return 1;
}*/

void recovery_logic()
{

   for ( i = 0; i < REORDER_WIDTH; i++)
     {

        issReadyQ.swID = 0;
        issReadyQ.valid[i] = 0;
        //----Individual Issue Queue------

        alu_insn.hdPtr = 0;
        alu_insn.tailPtr = 0;
        alu_insn.valid[ i ] = 0;
        mul_insn.hdPtr = 0;
        mul_insn.tailPtr = 0;
        mul_insn.valid[ i ] = 0;
        ls_insn.hdPtr = 0;
        ls_insn.tailPtr = 0;
        ls_insn.valid[ i ] = 0;
        br_insn.hdPtr = 0;
        br_insn.tailPtr = 0;
        br_insn.valid[ i ] = 0;
        ot_insn.hdPtr = 0;
        ot_insn.tailPtr = 0;
        ot_insn.valid[ i ] = 0;
        //----Wake-Up Table---------
        wakeUpTbl[i].valid = 0;
        wakeUpTbl[i].slotLength = 0; //Reset
     }

    unResolvedCntr = 0;
    issReadyQ.hdPtr = 0;
    issReadyQ.tailPtr = 0;
    hPQ_hdPtr = 0;
    lPQ_hdPtr = 0;
    hPQ_tailPtr = 0;
    lPQ_tailPtr = 0;

    resetPtr = tailPtr;

 //  if( cycle_count > 9127500) 
  //   fprintf(stderr," Recovery cycle %d \n", cycle_count);
    while ( ( (resetPtr + 1) % REORDER_WIDTH ) != headPtr ) 
     {
         resetPtr  = (resetPtr + 1) % REORDER_WIDTH; //Reset next ptr from the Jump Statement
         reoBuffer[ resetPtr ].misspeculated = 1; //To check for Speculation
 //        reoBuffer[ resetPtr ].issued = 1; //To check for Speculation
//         reoBuffer[ resetPtr ].finished = 1; //To check for Speculation
         reoBuffer[ resetPtr ].exception = 0; //To check for Speculation
      }
//-------clear the issue queue after the exception----------
    threadUpdate = 1; 
    curPtr = 0;  // Current Thread Pointer
    thrdBits.tailPtr = 0;
    thrdBits.hdPtr = THREAD_WIDTH/2;
    thrdBits.BITS = 0;
    firstSpawn = 0;
//    evenThrdCnt = 2;
 //   oddThrdCnt = 3;
    //thrdPC_Q.completeBit = 0; 
   // next_data_ptr->inst_cp.completeBit = 0;
    //cur_data_ptr->inst_cp.completeBit = 0;
 // for (unsigned k=0; k <= (THREAD_LEVEL); k++) // Lo & Hi
//   for (unsigned j=0; j<(THREAD_WIDTH); j++) // Lo & Hi
 threadBusyList.unique();
 for ( list<unsigned int>::iterator it = threadBusyList.begin(); it != threadBusyList.end(); it++)
   {
      thrdPC_Q.threadCount[*it] = 0;
      thrdPC_Q.valid[*it] = 0; // Free the Threads
      thrdPC_Q.busy[*it] = 0;
      thrdPC_Q.bitPtr[*it] = 0;
      thrdPC_Q.thrdParentID[*it] = 0;
      thrdPC_Q.thrdParentLevel[*it] = 0;
     
   }

//   rRegVector.clear();
   //rRegVector.resize(0);
   rRegVector.clear();
   
 //  for (reg_ii = rRegVector.begin(); reg_ii != rRegVector.end(); reg_ii++)
 //  for ( int ii = 0; ii < regSize; ii++)
     {
   //     rRegVector.pop_back(); 
/*       for (unsigned k=0; k <= (THREAD_LEVEL); k++) // Lo & Hi
        {
         for (unsigned int i=0; i<(MD_NUM_IREGS + 1); i++) // Lo & Hi
          {
            rRegPtr1.valid [k][i]= 0;// INPUT_RRP->wr_valid[i];
          //  reg_ii->valid[k][i] = 0;
          }
        } 
  */
        //reg_ii =  rRegVector.erase(reg_ii);
   //fprintf(stderr," Reg cleard %d \n", rRegVector.size()); 
        //if ( reg_ii != rRegVector.begin() || reg_ii != rRegVector.end())
         //       reg_ii --;
     //      for (unsigned int i=0; i<(MD_NUM_IREGS + 1); i++) // Lo & Hi
      //         (reg_ii)->valid[0][i] = 0;
     }

  // fprintf(stderr," End Reg cleard \n"); 
 // exit(0); 
/*
   for (unsigned k=0; k <= (THREAD_WIDTH); k++) // Lo & Hi
    {
      if (  thrdPC_Q.busy[k] )
       {
           fprintf(stderr," Not Removed %d \n", k);
           print_reorder();
            exit(0);
       }
    }
*/
    activeList.clear();
    activeValidList.clear();
    threadBusyList.clear();
    priorityList.clear();
   //-------Enable on Checker Mode---------
       regs.regs_C.lo = regs_cp.regs_R[ aRegPtr[32] ]; 
       regs.regs_C.hi = regs_cp.regs_R2[ aRegPtr[32] ];
}
