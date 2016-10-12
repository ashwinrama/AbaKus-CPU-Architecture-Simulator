/******Main File of the AbaKus Simulator*********************************/
/*******Aswin Ramachandrn & Louis Johnson ********************************/ 
/*Description:*/
/* Superscalar processors with wide instruction fetch only results in diminishing performance returns.*/  
/* The aim of this research to find what causes these limitations.  */
/* In addition, a new cycle-accurate computer architecture simulator – AbaKus - is developed to study and */
/* evaluate the performance of the architecture designs. */
/* Oklahoma State University, 2008
/************************************************************************/
// File: full_main.cc

#include <iostream>
#include <list>


extern "C" {
#include "host.h"
#include "regs.h"
#include "misc.h"
#include "host.h"
#include "machine.h"
#include "endian.h"
#include "options.h"
#include "loader.h"
#include "bpred.h"
#include "sim.h"
#include "stats.h"
//#include "sim-init.h"
}


#include "sim-print.h"
#ifndef DATATYPE
#define DATATYPE 
#include "sc_datatypes.h"
#endif
using namespace std;

void regCheck();
void simsafe_main(int, char**, char**);
//extern unsigned int aRegPtr[MD_NUM_IREGS + MD_XREGS]; // Architected Register Pointer File

  
simulationDataStruct simDataA, simDataB, *cur_data_ptr, *next_data_ptr;

bool cycle_toggle = 0;

unsigned long long cycle_count = 0;

int main(int argc, char** argv, char** envp) {
 
 cout << "Simulation begins..." << endl;//Flush the buffer

//Load the program into simulated mem. system and initialize
  simsafe_main(argc,argv,envp);
//Initialize Pointers
  cur_data_ptr = &simDataA;
  next_data_ptr = &simDataB;
  
  initialize_ptrs();

 do
  {
//------Evaluate---------
    regs_Update();  //writes the current register values into the storage elements
   // fprintf ( stderr, " Cycle Cnt %d\n", cycle_count );
    fetch_main();    //Fetch Stage
   //if ( cycle_count >= 0 ) \
      fprintf ( stderr, " ******fetch******\n");
   decode_main();
   //if ( cycle_count >= 0 ) \
      fprintf ( stderr, " dec\n");
    dispatch_main();//Decode Stage
   //if ( cycle_count >= 0 ) \
     fprintf ( stderr, " dis\n");
    issue_main();
   //if ( cycle_count >= 0 ) \
      fprintf ( stderr, " iss\n");
    execute_main();
   //if ( cycle_count >= 0 ) \
      fprintf ( stderr, " exe\n");
    finish_main();
   //if ( cycle_count >= 0 ) \
      fprintf ( stderr, " finish\n");
    complete_main();
  // if ( cycle_count >= 0 ) \
      fprintf ( stderr, " complete\n");

//------update------------
   cycle_toggle = !cycle_toggle;
  if (cycle_toggle)
  {
    cur_data_ptr = &simDataB;
    next_data_ptr = &simDataA;
  }
  else
  {
    cur_data_ptr = &simDataA;
    next_data_ptr = &simDataB;
  }
  //cout<<  "----------Cycle Count----------------" << cycle_count <<endl;
 // cout<<  "\n" << cycle_count <<endl;
   cycle_count++ ;
  } while (1);
//  cout<<  "Cycle Count\n" << cycle_count <<endl;
}
