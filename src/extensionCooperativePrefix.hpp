#ifndef __EXTENSION_COOPERATIVE_PREFIX_HPP
#define __EXTENSION_COOPERATIVE_PREFIX_HPP

#include "gr1context.hpp"
#include <string>

/**
 * A class that computes the environment cooperation to make an unrealizable 
 * strategy realizable. 
 */

template<class T> class XCooperativePrefix : public T {
protected:

    // Inherited stuff used
    using T::mgr;
    using T::strategyDumpingData;
    using T::livenessGuarantees;
    using T::livenessAssumptions;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::varCubePreOutput;
    using T::varCubePreInput;
    using T::varCubePostOutput;
    using T::varCubePostInput;
    using T::varCubePost;
    using T::safetyEnv;
    using T::safetySys;
    using T::initSys;
    using T::initEnv;
    using T::winningPositions;
    using T::realizable;

    std::vector<BF> cooperativeProgressPaths;
    bool cooperativePrefixExists;
  

    // Constructor
    XCooperativePrefix<T>(std::list<std::string> &filenames) : T(filenames) {}

public:

    /**
     * @brief Modified basic synthesis algorithm - adds to 'strategyDumpingData' transitions
     * that represent "a bias for action"
     */
    void computeWinningPositions() {

        // The greatest fixed point - called "Z" in the GR(1) synthesis paper
        BFFixedPoint nu2(mgr.constantTrue());
        unsigned int nu2Nr = 0;

        // Iterate until we have found a fixed point
        for (;!nu2.isFixedPointReached();) {
            nu2Nr++;

            // To extract a strategy in case of realizability, we need to store a sequence of 'preferred' transitions in the
            // game structure. These preferred transitions only need to be computed during the last execution of the outermost
            // greatest fixed point. Since we don't know which one is the last one, we store them in every iteration,
            // so that after the last iteration, we obtained the necessary data. Before any new iteration, we need to
            // clear the old data, though.
            strategyDumpingData.clear();

            // Iterate over all of the liveness guarantees. Put the results into the variable 'nextContraintsForGoals' for every
            // goal. Then, after we have iterated over the goals, we can update nu2.
            BF nextContraintsForGoals = mgr.constantTrue();
            for (unsigned int j=0;j<livenessGuarantees.size()-livenessAssumptions.size();j++) {

                // Start computing the transitions that lead closer to the goal and lead to a position that is not yet known to be losing.
                // Start with the ones that actually represent reaching the goal (which is a transition in this implementation as we can have
                // nexts in the goal descriptions).
                BF livetransitions = livenessGuarantees[j] & (nu2.getValue().SwapVariables(varVectorPre,varVectorPost));

                // Compute the middle least-fixed point (called 'Y' in the GR(1) paper)
                BFFixedPoint mu1(mgr.constantFalse());
                unsigned int mu1Nr = 0;
                for (;!mu1.isFixedPointReached();) {
                    mu1Nr++;

                    // Update the set of transitions that lead closer to the goal.
                    livetransitions |= mu1.getValue().SwapVariables(varVectorPre,varVectorPost);

                    // { std::ostringstream os;
                    // os << "/tmp/livetransitions" << nu2Nr << "-" << j << "-" << mu1Nr << ".dot";
                    // BF_newDumpDot(*this,livetransitions,"Pre Post",os.str()); }

                    // Iterate over the liveness assumptions. Store the positions that are found to be winning for *any*
                    // of them into the variable 'goodForAnyLivenessAssumption'.
                    BF goodForAnyLivenessAssumption = mu1.getValue();
                    for (unsigned int i=0;i<livenessAssumptions.size();i++) {

                        // Prepare the variable 'foundPaths' that contains the transitions that stay within the inner-most
                        // greatest fixed point or get closer to the goal. Only used for strategy extraction
                        BF foundPaths = mgr.constantTrue();

                        // Allocate space for storing the transitions that allow the satisfaction of
                        // the liveness assumptions
                        std::vector<BF> livenessAssumptionProgressPaths;

                        // Inner-most greatest fixed point. The corresponding variable in the paper would be 'X'.
                        BFFixedPoint nu0(mgr.constantTrue());
                        unsigned int nu0Nr = 0;
                        for (;!nu0.isFixedPointReached();) {

                            nu0Nr++;

                            // Compute a set of paths that are safe to take - used for the enforceable predecessor operator ('cox')
                            foundPaths = livetransitions | ((nu0.getValue()).SwapVariables(varVectorPre,varVectorPost) & !(livenessAssumptions[i]));
                            foundPaths &= safetySys;

                            // { std::ostringstream os;
                            // os << "/tmp/foundPathsFinal" << nu2Nr << "-" << j << "-" << mu1Nr << "-" << i << ".dot";
                            // BF_newDumpDot(*this,foundPaths,"Pre Post",os.str()); }


                            // Update the inner-most fixed point with the result of applying the enforcable predecessor operator
                            nu0.update(safetyEnv.Implies(foundPaths).ExistAbstract(varCubePostOutput).UnivAbstract(varCubePostInput));

                            // { std::ostringstream os;
                            // os << "/tmp/nu0-" << nu2Nr << "-" << j << "-" << mu1Nr << "-" << i << "-" << nu0Nr << ".dot";
                            // BF_newDumpDot(*this,nu0.getValue(),"Pre Post",os.str()); }

                        }

                        // Update the set of positions that are winning for some liveness assumption
                        goodForAnyLivenessAssumption |= nu0.getValue();

                        strategyDumpingData.push_back(std::pair<unsigned int,BF>(j,foundPaths));
                        
                    }

                    // Update the middle fixed point
                    mu1.update(goodForAnyLivenessAssumption);

                    // { std::ostringstream os;
                    // os << "/tmp/mu1-" << nu2Nr << "-" << j << "-" << mu1Nr << ".dot";
                    // BF_newDumpDot(*this,mu1.getValue(),"Pre Post",os.str()); }
                }

                // Update the set of positions that are winning for any goal for the outermost fixed point
                nextContraintsForGoals &= mu1.getValue();
            }

            // Update the outer-most fixed point
            nu2.update(nextContraintsForGoals);

            // { std::ostringstream os;
            // os << "/tmp/nu2-" << nu2Nr << ".dot";
            // BF_newDumpDot(*this,nu2.getValue(),"Pre Post",os.str()); }
        }

        // We found the set of winning positions
        winningPositions = nu2.getValue();

    }

      void computePathToWin() {

        // Compute system transitions that are not environment dead-ends.
        // The system is only allowed to ask for these.
        BF nonDeadEndSafetySys = safetySys & safetyEnv.ExistAbstract(varCubePost).SwapVariables(varVectorPre,varVectorPost);
        // BF_newDumpDot(*this,nonDeadEndSafetySys,"Pre Post","/tmp/nonDeadEndSys.dot");
 
	// Cooperation: Compute set of states from which a winning state can be
	// reached (somehow)

	BFFixedPoint muCoop(mgr.constantFalse());
	
	unsigned int muCoopNr = 0;
	cooperativeProgressPaths.clear();
	cooperativeProgressPaths.push_back(winningPositions);

	BF foundPaths = mgr.constantTrue();
	 
	for (;!muCoop.isFixedPointReached();) {
	  muCoopNr++;
	  foundPaths = winningPositions | (muCoop.getValue().SwapVariables(varVectorPre,varVectorPost));
	  foundPaths &= nonDeadEndSafetySys;

	  // { std::ostringstream os;
	  // os << "/tmp/foundPaths" << nu2Nr << "-" << j << "-" << mu1Nr << "-" << i << "-" << nu0Nr << "--" << muCoopNr << ".dot";
	  // BF_newDumpDot(*this,foundPaths,"Pre Post",os.str()); }

	  cooperativeProgressPaths.push_back(foundPaths);
	  muCoop.update((safetyEnv & foundPaths).ExistAbstract(varCubePost));

	  // { std::ostringstream os;
	  // os << "/tmp/muCoop" << nu2Nr << "-" << j << "-" << mu1Nr << "-" << i << "-" << nu0Nr << "--" << muCoopNr << ".dot";
	  // BF_newDumpDot(*this,muCoop.getValue(),"Pre Post",os.str()); }
	}

	BF result;
	result = (initEnv & initSys).Implies(foundPaths).UnivAbstract(varCubePreOutput).UnivAbstract(varCubePreInput);
	// Check if the result is well-defind. Might fail after an incorrect modification of the above algorithm
	if (!result.isConstant()) throw "Internal error: Could not establish existence of cooperative prefix.";

	cooperativePrefixExists = result.isTrue();
    }


  void checkRealizability() {

    computeWinningPositions();

    // Check if for every possible environment initial position the system has a good system initial position
    BF result;
    result = (initEnv & initSys).Implies(winningPositions).UnivAbstract(varCubePreOutput).UnivAbstract(varCubePreInput);

    // Check if the result is well-defind. Might fail after an incorrect modification of the above algorithm
    if (!result.isConstant()) throw "Internal error: Could not establish realizability/unrealizability of the specification.";

    // Return the result in Boolean form.
    realizable = result.isTrue();

    if (!realizable) {
      computePathToWin();
    }
    
  }

  
    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XCooperativePrefix<T>(filenames);
    }
  
};

#endif
