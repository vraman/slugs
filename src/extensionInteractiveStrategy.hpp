#ifndef __EXTENSION_INTERACTIVE_STRATEGY_HPP
#define __EXTENSION_INTERACTIVE_STRATEGY_HPP

#include <boost/algorithm/string.hpp>


/**
 * A class that opens an interactive shell to allow examining the property of strategies computed
 *
 */
template<class T> class XInteractiveStrategy : public T {
protected:
    XInteractiveStrategy<T>(std::list<std::string> &filenames) : T(filenames) {}

    using T::checkRealizability;
    using T::realizable;
    using T::variables;
    using T::variableNames;
    using T::variableTypes;
    using T::mgr;
    using T::winningPositions;
    using T::livenessAssumptions;
    using T::livenessGuarantees;
    using T::safetyEnv;
    using T::safetySys;
    using T::varCubePostOutput;
    using T::varCubePre;
    using T::postOutputVars;
    using T::determinize;
    using T::initEnv;
    using T::initSys;
    using T::preVars;
    using T::postVars;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::varCubePostInput;

    std::vector<boost::tuple<unsigned int, unsigned int,BF> > strategyDumpingData;

public:
    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XInteractiveStrategy<T>(filenames);
    }
    
    
    
    
    void computeWinningPositions() {

        // The greatest fixed point - called "Z" in the GR(1) synthesis paper
        BFFixedPoint nu2(mgr.constantTrue());
    
        //keep track of distance from goal (i.e. "level" in current Y set)
        unsigned int cy = 0;
                
        // Iterate until we have found a fixed point
        for (;!nu2.isFixedPointReached();) {
    
            // To extract a strategy in case of realizability, we need to store a sequence of 'preferred' transitions in the
            // game structure. These preferred transitions only need to be computed during the last execution of the outermost
            // greatest fixed point. Since we don't know which one is the last one, we store them in every iteration,
            // so that after the last iteration, we obtained the necessary data. Before any new iteration, we need to
            // clear the old data, though.
            strategyDumpingData.clear();
    
            // Iterate over all of the liveness guarantees. Put the results into the variable 'nextContraintsForGoals' for every
            // goal. Then, after we have iterated over the goals, we can update nu2.
            BF nextContraintsForGoals = mgr.constantTrue();
            for (unsigned int j=0;j<livenessGuarantees.size();j++) {
    
                // Start computing the transitions that lead closer to the goal and lead to a position that is not yet known to be losing.
                // Start with the ones that actually represent reaching the goal (which is a transition in this implementation as we can have
                // nexts in the goal descriptions).
                BF livetransitions = livenessGuarantees[j] & (nu2.getValue().SwapVariables(varVectorPre,varVectorPost));
                
                cy = 0;
                
                // Compute the middle least-fixed point (called 'Y' in the GR(1) paper)
                BFFixedPoint mu1(mgr.constantFalse());
                for (;!mu1.isFixedPointReached();) {
    
                    // Update the set of transitions that lead closer to the goal.
                    livetransitions |= mu1.getValue().SwapVariables(varVectorPre,varVectorPost);
    
                    // Iterate over the liveness assumptions. Store the positions that are found to be winning for *any*
                    // of them into the variable 'goodForAnyLivenessAssumption'.
                    BF goodForAnyLivenessAssumption = mu1.getValue();
                 
                       
                    for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                        
                        // Prepare the variable 'foundPaths' that contains the transitions that stay within the inner-most
                        // greatest fixed point or get closer to the goal. Only used for strategy extraction
                        BF foundPaths = mgr.constantTrue();
    
                        // Inner-most greatest fixed point. The corresponding variable in the paper would be 'X'.
                        BFFixedPoint nu0(mgr.constantTrue());
                        for (;!nu0.isFixedPointReached();) {
    
                            // Compute a set of paths that are safe to take - used for the enforceable predecessor operator ('cox')
                            foundPaths = livetransitions | (nu0.getValue().SwapVariables(varVectorPre,varVectorPost) & !(livenessAssumptions[i]));
                            foundPaths &= safetySys;
    
                            // Update the inner-most fixed point with the result of applying the enforcable predecessor operator
                            nu0.update(safetyEnv.Implies(foundPaths).ExistAbstract(varCubePostOutput).UnivAbstract(varCubePostInput));
                        }
    
                        // Update the set of positions that are winning for some liveness assumption
                        goodForAnyLivenessAssumption |= nu0.getValue();
    
                        // Dump the paths that we just wound into 'strategyDumpingData' - store the current goal long
                        // with the BDD
                        strategyDumpingData.push_back(boost::tuple<unsigned int, unsigned int,BF>(j,cy,foundPaths));
                    }
                    
                    cy++;
    
                    // Update the moddle fixed point
                    mu1.update(goodForAnyLivenessAssumption);
                }
    
                // Update the set of positions that are winning for any goal for the outermost fixed point
                nextContraintsForGoals &= mu1.getValue();
            }
    
            // Update the outer-most fixed point
            nu2.update(nextContraintsForGoals);
    
        }
    
        // We found the set of winning positions
        winningPositions = nu2.getValue();
    }




    void execute() {
        checkRealizability();

        std::vector<std::vector<BF>> positionalStrategiesForTheIndividualGoals(livenessGuarantees.size(),std::vector<BF>(100,mgr.constantFalse()));
        for (unsigned int i=0;i<livenessGuarantees.size();i++) {
            BF casesCovered = mgr.constantFalse();
            BF strategy = mgr.constantFalse();
            for (auto it = strategyDumpingData.begin();it!=strategyDumpingData.end();it++) {
                if (boost::get<0>(*it) == i) {
                    BF newCases = boost::get<2>(*it).ExistAbstract(varCubePostOutput) & !casesCovered;
                    strategy |= newCases & boost::get<2>(*it);
                    positionalStrategiesForTheIndividualGoals[i][boost::get<1>(*it)] |= strategy;
                    casesCovered |= newCases;
                }
            }
            //positionalStrategiesForTheIndividualGoals[i] = strategy;
            //BF_newDumpDot(*this,strategy,"PreInput PreOutput PostInput PostOutput","/tmp/generalStrategy.dot");
        }

        if (realizable) {

            BF currentPosition = mgr.constantFalse();
            unsigned int currentLivenessGuarantee = 0;

            while(true) {

                // The prompt
                std::cout << "> ";
                std::cout.flush();
                std::string command = "";
                while (command=="") {
                    std::getline(std::cin,command);
                    if (std::cin.eof()) return;
                }

                // Check the command
                boost::trim(command);
                boost::to_upper(command);

                if ((command=="QUIT") || (command=="EXIT")) {
                    return;
                } else if (command=="CHECKTRANS") {

                    std::cout << "From: \n";
                    BF from = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if ((variableTypes[i]==PreInput) || (variableTypes[i]==PreOutput)) {
                            std::cout << " - " << variableNames[i] << ": ";
                            std::cout.flush();
                            int value;
                            std::cin >> value;
                            if (std::cin.fail()) {
                                std::cout << "    -> Error reading value. Assuming 0.\n";
                                value = 0;
                            }
                            if (value==0) {
                                from &= !variables[i];
                            } else if (value==1) {
                                from &= variables[i];
                            } else {
                                std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                from &= variables[i];
                            }
                        }
                    }

                    std::cout << "To: \n";
                    BF to = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if ((variableTypes[i]==PostInput) || (variableTypes[i]==PostOutput)) {
                            std::cout << " - " << variableNames[i] << ": ";
                            std::cout.flush();
                            int value;
                            std::cin >> value;
                            if (std::cin.fail()) {
                                std::cout << "    -> Error reading value. Assuming 0.\n";
                                value = 0;
                            }
                            if (value==0) {
                                from &= !variables[i];
                            } else if (value==1) {
                                from &= variables[i];
                            } else {
                                std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                from &= variables[i];
                            }
                        }
                    }

                    std::cout << "Result: \n";
                    if ((from & winningPositions).isFalse()) {
                        std::cout << "- The pre-position is not winning.\n";
                    } else {
                        std::cout << "- The pre-position is winning.\n";
                    }
                    if ((from & to & safetyEnv).isFalse()) {
                        std::cout << "- The transition VIOLATES the SAFETY ASSUMPTIONS\n";
                    } else {
                        std::cout << "- The transition SATISFIES the SAFETY ASSUMPTIONS\n";
                    }
                    if ((from & to & safetySys).isFalse()) {
                        std::cout << "- The transition VIOLATES the SAFETY GUARANTEES\n";
                    } else {
                        std::cout << "- The transition SATISFIES the SAFETY GUARANTEES\n";
                    }
                    std::cout << "- The transition is a goal transition for the following liveness assumptions: ";
                    bool foundOne = false;
                    for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                        if (!(livenessAssumptions[i] & from & to).isFalse()) {
                            if (foundOne) std::cout << ", ";
                            foundOne = true;
                            std::cout << i;
                        }
                    }
                    if (!foundOne) std::cout << "none";
                    std::cout << std::endl;
                    std::cout << "- The transition is a goal transition for the following liveness guarantees: ";
                    foundOne = false;
                    for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                        if (!(livenessGuarantees[i] & from & to).isFalse()) {
                            if (foundOne) std::cout << ", ";
                            foundOne = true;
                            std::cout << i;
                        }
                    }
                    if (!foundOne) std::cout << "none";
                    std::cout << std::endl;

                    // Analyse if it is part of a possible strategy
                    std::cout << "- The transition is a possible transition in a strategy for the following goals: ";
                    foundOne = false;
                    for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                        for (unsigned int j =0; j<positionalStrategiesForTheIndividualGoals[i].size();j++) {
                            if (!(positionalStrategiesForTheIndividualGoals[i][j] & from & to).isFalse()) {
                                if (foundOne) std::cout << ", ";
                                foundOne = true;
                                std::cout << i << " at distance " << j;
                                break;
                            }
                        }
                    }
                    if (!foundOne) std::cout << "none";
                    std::cout << std::endl;

                } else if (command=="SETPOS") {

                    std::cout << "Position: \n";
                    BF from = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if ((variableTypes[i]==PreInput) || (variableTypes[i]==PreOutput)) {
                            std::cout << " - " << variableNames[i] << ": ";
                            std::cout.flush();
                            int value;
                            std::cin >> value;
                            if (std::cin.fail()) {
                                std::cout << "    -> Error reading value. Assuming 0.\n";
                                value = 0;
                            }
                            if (value==0) {
                                from &= !variables[i];
                            } else if (value==1) {
                                from &= variables[i];
                            } else {
                                std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                from &= variables[i];
                            }
                        }
                    }
                    currentPosition = from;
                } else if (command=="MOVE") {

                    if (currentPosition == mgr.constantFalse()) {
                        std::cout << "Error: The current position is undefined. Use SETPOS prior to calling MOVE." << std::endl;
                    } else {

                        std::cout << "Guarantee No.: ";
                        std::cout.flush();
                        unsigned int guarantee;
                        std::cin >> guarantee;
                        if (std::cin.fail()) {
                            std::cout << "    -> Error reading value. Aborting \n";
                        } else if (guarantee>=livenessGuarantees.size()) {
                            std::cout << "    -> Number too large. Aborting \n";
                        } else {

                            BF allowedInputs = (currentPosition & safetyEnv);
                            BF_newDumpDot(*this,allowedInputs,NULL,"/tmp/allowedInputs.dot");

                            std::cout << "To: \n";
                            BF to = mgr.constantTrue();
                            BF nextPosition = mgr.constantTrue();
                            for (unsigned int i=0;i<variables.size();i++) {
                                if (variableTypes[i]==PostInput) {
                                    std::cout << " - " << variableNames[i] << ": ";
                                    std::cout.flush();
                                    int value;
                                    std::cin >> value;
                                    if (std::cin.fail()) {
                                        std::cout << "    -> Error reading value. Assuming 0.\n";
                                        value = 0;
                                    }
                                    if (value==0) {
                                        to &= !variables[i];
                                        nextPosition &= !variables[i];
                                    } else if (value==1) {
                                        to &= variables[i];
                                        nextPosition &= variables[i];
                                    } else {
                                        std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                        to &= variables[i];
                                    }
                                }
                            }
                            
                            
                            BF transition = mgr.constantFalse();
                           
                            //find the BDD at the lowest level with a valid transition
                            for (unsigned int j =0; j<positionalStrategiesForTheIndividualGoals[guarantee].size();j++) {
                                if (!(positionalStrategiesForTheIndividualGoals[guarantee][j] & currentPosition & to).isFalse()) {
                                    transition = currentPosition & to & positionalStrategiesForTheIndividualGoals[guarantee][j];
                                    break;
                                }
                            }
                            

                            if (transition.isFalse()) {
                                std::cout << "    -> Error: Input not allowed here.\n";
                                if (!(currentPosition & to & safetyEnv).isFalse()) {
                                    std::cout << "       -> Actually, that's an internal error!\n";
                                }
                            } else {

                                transition = determinize(transition,postOutputVars);

                                for (unsigned int i=0;i<variables.size();i++) {
                                    if (variableTypes[i]==PostOutput) {
                                        if ((variables[i] & transition).isFalse()) {
                                            std::cout << " - " << variableNames[i] << " = 0\n";
                                            nextPosition &= !variables[i];
                                        } else {
                                            std::cout << " - " << variableNames[i] << " = 1\n";
                                            nextPosition &= variables[i];
                                        }
                                    }
                                }

                                std::cout << "- The transition is a goal transition for the following liveness assumptions: ";
                                bool foundOne = false;
                                for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                                    if (!(livenessAssumptions[i] & transition).isFalse()) {
                                        if (foundOne) std::cout << ", ";
                                        foundOne = true;
                                        std::cout << i;
                                    }
                                }
                                if (!foundOne) std::cout << "none";
                                std::cout << std::endl;
                                std::cout << "- The transition is a goal transition for the following liveness guarantees: ";
                                foundOne = false;
                                for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                                    if (!(livenessGuarantees[i] & transition).isFalse()) {
                                        if (foundOne) std::cout << ", ";
                                        foundOne = true;
                                        std::cout << i;
                                    }
                                }
                                if (!foundOne) std::cout << "none";
                                std::cout << std::endl;

                                // Analyse if it is part of a possible strategy
                                std::cout << "- The transition is a possible transition in a strategy for the following goals: ";
                                foundOne = false;
                                for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                                    for (unsigned int j =0; j<positionalStrategiesForTheIndividualGoals[i].size();j++) {
                                        if (!(positionalStrategiesForTheIndividualGoals[i][j] & transition).isFalse()) {
                                            if (foundOne) std::cout << ", ";
                                            foundOne = true;
                                            std::cout << i << " at distance " << j;
                                            break;
                                        }
                                    }
                                }
                                if (!foundOne) std::cout << "none";
                                std::cout << std::endl;

                                currentPosition = nextPosition.SwapVariables(varVectorPre,varVectorPost);
                            }
                        }
                    }
                }

                //========================================
                // Simplified functions to be called from
                // other tools.
                //========================================
                else if (command=="XMAKETRANS") {
                    std::cout << "\n"; // Get rid of the prompt
                    BF postInput = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PostInput) {
                            char c;
                            std::cin >> c;
                            if (c=='0') {
                                postInput &= !variables[i];
                            } else if (c=='1') {
                                postInput &= variables[i];
                            } else {
                                std::cerr << "Error: Illegal XMAKETRANS string given.\n";
                            }
                        }
                    }
                    BF trans = currentPosition & postInput & safetyEnv;
                    if (trans.isFalse()) {
                        std::cout << "ERROR\n";
                        if (currentPosition.isFalse()) {
                        }
                    } else {
                        
                        BF transition = mgr.constantFalse();
                           
                        //find the BDD at the lowest level with a valid transition
                        for (unsigned int j =0; j<positionalStrategiesForTheIndividualGoals[currentLivenessGuarantee].size();j++) {
                            if (!(positionalStrategiesForTheIndividualGoals[currentLivenessGuarantee][j] & trans).isFalse()) {
                                trans &= positionalStrategiesForTheIndividualGoals[currentLivenessGuarantee][j];
                                break;
                            }
                        }
                            
                        
                        // Switching goals
                        BF newCombination = determinize(trans,postVars);

                        // Jump as much forward  in the liveness guarantee list as possible ("stuttering avoidance")
                        unsigned int nextLivenessGuarantee = currentLivenessGuarantee;
                        bool firstTry = true;
                        while (((nextLivenessGuarantee != currentLivenessGuarantee) || firstTry) && !((livenessGuarantees[nextLivenessGuarantee] & newCombination).isFalse())) {
                            nextLivenessGuarantee = (nextLivenessGuarantee + 1) % livenessGuarantees.size();
                            firstTry = false;
                        }

                        currentLivenessGuarantee = nextLivenessGuarantee;
                        currentPosition = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);

                        // Print position
                        for (unsigned int i=0;i<variables.size();i++) {
                            if (variableTypes[i]==PreInput) {
                                if ((variables[i] & currentPosition).isFalse()) {
                                    std::cout << "0";
                                } else {
                                    std::cout << "1";
                                }
                            }
                        }
                        for (unsigned int i=0;i<variables.size();i++) {
                            if (variableTypes[i]==PreOutput) {
                                if ((variables[i] & currentPosition).isFalse()) {
                                    std::cout << "0";
                                } else {
                                    std::cout << "1";
                                }
                            }
                        }
                        std::cout << "," << currentLivenessGuarantee << std::endl; // Flushes, too.
                    }
                    std::cout.flush();
                } else if (command=="XPRINTINPUTS") {
                    std::cout << "\n"; // Get rid of the prompt
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreInput)
                            std::cout << variableNames[i] << "\n";
                    }
                    std::cout << std::endl; // Flushes
                } else if (command=="XPRINTOUTPUTS") {
                    std::cout << "\n"; // Get rid of the prompt
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreOutput)
                            std::cout << variableNames[i] << "\n";
                    }
                    std::cout << std::endl; // Flushes
                } else if (command=="XGETINIT") {
                    std::cout << "\n"; // Get rid of the prompt
                    BF initialPosition = winningPositions & initEnv & initSys;
                    initialPosition = determinize(initialPosition,preVars);
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreInput) {
                            if ((variables[i] & initialPosition).isFalse()) {
                                std::cout << "0";
                            } else {
                                std::cout << "1";
                            }
                        }
                    }
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreOutput) {
                            if ((variables[i] & initialPosition).isFalse()) {
                                std::cout << "0";
                            } else {
                                std::cout << "1";
                            }
                        }
                    }
                    std::cout << ",0" << std::endl; // Flushes, too.
                    currentPosition = initialPosition;
                } else {
                    std::cout << "Error: Did not understand command '" << command << "'" << std::endl;
                }

            }

        }

    }


};


#endif
