#ifndef __EXTENSION_SYMBOLIC_COUNTERSTRATEGY
#define __EXTENSION_SYMBOLIC_COUNTERSTRATEGY

#include "gr1context.hpp"
#include <string>

/**
 * A class that computes an explicit state counterstrategy for an unrealizable specification
 */
template<class T> class XExtractSymbolicCounterStrategy : public T {
protected:
    // New variables
    std::string outputFilename;

    // Inherited stuff used
    using T::mgr;
    using T::strategyDumpingData;
    using T::livenessGuarantees;
    using T::livenessAssumptions;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::varCubePostOutput;
    using T::varCubePostInput;
    using T::varCubePreOutput;
    using T::varCubePreInput;
    using T::varCubePre;
    using T::varCubePost;
    using T::safetyEnv;
    using T::safetySys;
    using T::winningPositions;
    using T::initEnv;
    using T::initSys;
    using T::preVars;
    using T::postVars;
    using T::variableTypes;
    using T::variables;
    using T::variableNames;
    using T::realizable;
    using T::determinize;
    using T::postInputVars;
    using T::postOutputVars;
    using T::doesVariableInheritType;
    using T::addVariable;

    //foundCutConditions will eventually contain transitions that prevent the
    //counterstrategy from enforcing livelock/deadlock.
    // -- For deadlock, ALL transitions that satisfy foundCutConditions must be excluded.
    // -- For livelock, ONE transition that satisfies foundCutConditions must be excluded PER GOAL.
    // -- Computes cuts symbolically
  
  std::vector<int> counterVarNumbers1;
  std::vector<int> counterVarNumbers2;
  int goalTransitionSelectorVar;

  XExtractSymbolicCounterStrategy<T>(std::list<std::string> &filenames): T(filenames) {}

  void init(std::list<std::string> &filenames) {
        T::init(filenames);
        if (filenames.size()==0) {
            std::cerr << "Error: Need a file name for extracting a symbolic counterstrategy.\n";
            throw "Please adapt the parameters.";
        } else {
	    outputFilename = filenames.front();
            filenames.pop_front();
        }

    }
  
public:

/**
 * @brief Compute and print out (to stdout) an explicit-state counter strategy that is winning for
 *        the environment. The output is compatible with the old JTLV output of LTLMoP.
 *        This function requires that the unrealizability of the specification has already been
 *        detected and that the variables "strategyDumpingData" and
 *        "winningPositions" have been filled by the synthesis algorithm with meaningful data.
 * @param outputStream - Where the strategy shall be printed to.
 */
void execute() {
        T::execute();
        if (!realizable) {
            if (outputFilename=="") {
                throw "Internal Error.";
            } else {
               computeAndPrintSymbolicStrategy(outputFilename);
            }
        }
}

    
  void computeAndPrintSymbolicStrategy(std::string filename) {

    // We don't want any reordering from this point onwards, as
    // the BDD manipulations from this point onwards are 'kind of simple'.
    mgr.setAutomaticOptimisation(false);

    // List of states in existance so far. The first map
    // maps from a BF node pointer (for the pre variable valuation) and a goal
    // to a state number. The vector then contains the concrete valuation.
    std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > lookupTableForPastStates;
    std::vector<BF> bfsUsedInTheLookupTable;
    std::list<std::pair<size_t, std::pair<unsigned int, unsigned int> > > todoList;
   
    // Prepare positional strategies for the individual goals
    std::vector<std::vector<BF> > positionalStrategiesForTheIndividualGoals(livenessAssumptions.size());
    for (unsigned int i=0;i<livenessAssumptions.size();i++) {
        //BF casesCovered = mgr.constantFalse();
        std::vector<BF> strategy(livenessGuarantees.size()+1);
        for (unsigned int j=0;j<livenessGuarantees.size()+1;j++) {
            strategy[j] = mgr.constantFalse();
        }
        for (auto it = strategyDumpingData.begin();it!=strategyDumpingData.end();it++) {
            if (boost::get<0>(*it) == i) {
                //Have to cover each guarantee (since the winning strategy depends on which guarantee is being pursued)
                //Essentially, the choice of which guarantee to pursue can be thought of as a system "move".
                //The environment always to chooses that prevent the appropriate guarantee.
                strategy[boost::get<1>(*it)] |= boost::get<2>(*it).UnivAbstract(varCubePostOutput) & !(strategy[boost::get<1>(*it)].ExistAbstract(varCubePost));
	
            }
        }
        positionalStrategiesForTheIndividualGoals[i] = strategy;
    }

 
   	// Allocate counter variables
        for (unsigned int i=1;i<=livenessAssumptions.size();i = i << 1) {
            std::ostringstream os;
            os << "_jx1_b" << counterVarNumbers1.size();
            counterVarNumbers1.push_back(addVariable(SymbolicStrategyCounterVar,os.str()));
        }
	for (unsigned int i=1;i<=livenessGuarantees.size();i = i << 1) {
            std::ostringstream os;
            os << "_jx2_b" << counterVarNumbers2.size();
            counterVarNumbers2.push_back(addVariable(SymbolicStrategyCounterVar,os.str()));
        }
        goalTransitionSelectorVar = addVariable(SymbolicStrategyCounterVar,"strat_type");

	 
        BF combinedStrategy = mgr.constantFalse();
        for (unsigned int i=0;i<livenessAssumptions.size();i++) {
            BF thisEncoding = mgr.constantTrue();
	   
	    
            for (unsigned j=0;j<counterVarNumbers1.size();j++) {
                if (j&(1 << i)) {
                    thisEncoding &= variables[counterVarNumbers1[j]];
                } else {
                    thisEncoding &= !variables[counterVarNumbers1[j]];
                }
            }
	    for (unsigned int k=0;k<livenessGuarantees.size();k++) {
	      BF thisEncodingNew = thisEncoding;
	      for (unsigned j=0;j<counterVarNumbers2.size();j++) {
                if (j&(1 << k)) {
                    thisEncodingNew &= variables[counterVarNumbers2[j]];
                } else {
                    thisEncodingNew &= !variables[counterVarNumbers2[j]];
                }
	      }
	      
	      combinedStrategy |= thisEncodingNew & positionalStrategiesForTheIndividualGoals[i][k] &
                ((!variables[goalTransitionSelectorVar]) | livenessAssumptions[i]);
	      
	     
	    }
	}
  
	
	      
        std::ostringstream fileExtraHeader;
        fileExtraHeader << "# This file is a BDD exported by the SLUGS\n#\n# This BDD is a strategy.\n";
        fileExtraHeader << "#\n# This header contains extra information used by LTLMoP's BDDStrategy.\n";
        fileExtraHeader << "# Currently, the only metadata is 1) the total number of system goals\n";
        fileExtraHeader << "# and 2) the mapping between variable numbers and proposition names.\n#\n";
        fileExtraHeader << "# Some special variables are also added:\n";
        fileExtraHeader << "#       - `_jx1_b*` are used as a binary vector (b0 is LSB) to indicate\n";
	fileExtraHeader << "#         the index of the currently-pursued environment goal.\n";
        fileExtraHeader << "#       - `_jx2_b*` are used as a binary vector (b0 is LSB) to indicate\n";
        fileExtraHeader << "#         the index of the currently-prevented system goal.\n";
        fileExtraHeader << "#       - `strat_type` is a binary variable used to indicate whether we are\n";
	fileExtraHeader << "#          moving closer to the current environment goal (0) or transitioning to the next goal (1)\n#\n";
	fileExtraHeader << "# Num environment goals: " << livenessAssumptions.size() << "\n";
        fileExtraHeader << "# Num system goals: " << livenessGuarantees.size() << "\n";
        fileExtraHeader << "# Variable names:\n";
        for (unsigned int i=0;i<variables.size();i++) {
            fileExtraHeader << "       " << i << ": " << variableNames[i] << "\n";
        }
        fileExtraHeader << "#\n# For information about the DDDMP format, please see:\n";
        fileExtraHeader << "#    http://www.cs.uleth.ca/~rice/cudd_docs/dddmp/dddmpAllFile.html#dddmpDump.c\n#\n";
        fileExtraHeader << "# For information about how this file is generated, please see the SLUGS source.\n#\n";

	
        mgr.writeBDDToFile(filename.c_str(),fileExtraHeader.str(),combinedStrategy,variables,variableNames);
	
	
    
}


    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XExtractSymbolicCounterStrategy<T>(filenames);
    }
};

#endif

