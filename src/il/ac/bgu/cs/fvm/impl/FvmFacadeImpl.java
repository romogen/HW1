package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.channelsystem.ParserBasedInterleavingActDef;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.ActionNotFoundException;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.impl.programgraph.ProgramGraphImpl;
import il.ac.bgu.cs.fvm.impl.transitionsystem.TransitionSystemImpl;
import il.ac.bgu.cs.fvm.ltl.*;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationFailed;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

import java.io.InputStream;
import java.util.*;
import java.util.List;
import java.util.ArrayList;


import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

/**
 * Implement the methods in this class. You may add additional classes as you
 * want, as long as they live in the {@code impl} package, or one of its
 * sub-packages.
 */
public class FvmFacadeImpl implements FvmFacade {

    @Override
    public <S, A, P> TransitionSystem<S, A, P> createTransitionSystem() {
        return new TransitionSystemImpl<S, A, P>();
    }

    @Override
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if(ts.getInitialStates().size() > 1)
            return false;

        Set<Pair<S, A>> statesActionsPair = new HashSet<Pair<S, A>>();

        Iterator<Transition<S, A>> transitionIterator = ts.getTransitions().iterator();
        while(transitionIterator.hasNext()){
            Transition<S, A> currTransition = transitionIterator.next();
            Pair<S, A> currPair = new Pair<S, A>(currTransition.getFrom(), currTransition.getAction());
            if(statesActionsPair.contains(currPair))
                return false;
            statesActionsPair.add(currPair);
        }

        return true;
    }

//    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
//        Set<A> actions = ts.getActions();
//
//        Iterator<S> statesIterator = ts.getStates().iterator();
//        while(statesIterator.hasNext()){
//
//            Iterator<A> actionsIterator = actions.iterator();
//            while(actionsIterator.hasNext()){
//                if(post(ts, statesIterator.next(), actionsIterator.next()).size() > 1)
//                    return false;
//            }
//        }
//
//        return true;
//    }

    @Override
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if(ts.getInitialStates().size() > 1)
            return false;

        Iterator<S> transitionIterator = ts.getStates().iterator();
        while(transitionIterator.hasNext()){
            S currS = transitionIterator.next();
            Set<S> postS = post(ts, currS);
            Iterator<S> postIterator1 = postS.iterator(), postIterator2 = postS.iterator();
            while (postIterator1.hasNext()){
                S curr1 = postIterator1.next();
                while (postIterator2.hasNext()){
                    S curr2 = postIterator2.next();
                    if(curr1.equals(curr2))
                        continue;

                    if(ts.getLabel(curr1).equals(ts.getLabel(curr2)))
                        return false;
                }
            }
        }

        return true;
    }

    /*        if(ts.getInitialStates().size() > 1)
            return false;

        // check if it is empty tag and if there are more with empty tags. (it's not determenistic than)
        Iterator<Transition<S, A>> transitionIterator = ts.getTransitions().iterator();
        while(transitionIterator.hasNext()){
            Transition<S, A> currTransition = transitionIterator.next();
            Set<P> fromLabel = ts.getLabel(currTransition.getFrom()), toLabel = ts.getLabel(currTransition.getTo());
            fromLabel.retainAll(toLabel);
            if(fromLabel.size() > 1)
                return false;
        }

        return true;
*/
    @Override
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isMaximalExecutionFragment(ts, e) &&
                isInitialExecutionFragment(ts, e);
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        if(e.isEmpty())
            return true;
        if(!ts.getStates().contains(e.head()))
            throw new StateNotFoundException(e.head());


        S fromState = e.head();
        if(!ts.getStates().contains(fromState))
            throw new StateNotFoundException(fromState);

        AlternatingSequence<A, S> remainingSequence = e.tail();
        while(!remainingSequence.isEmpty()){
            A transitionAction = remainingSequence.head();
            S toState = remainingSequence.tail().head();
            remainingSequence = remainingSequence.tail().tail();

            if(!ts.getActions().contains(transitionAction))
                throw new ActionNotFoundException(transitionAction);
            if(!ts.getStates().contains(toState))
                throw new StateNotFoundException(toState);

            if(!ts.getTransitions().contains(new Transition<S, A>(fromState, transitionAction, toState)))
                return false;

            fromState = toState;
        }

        return true;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) &&
                ts.getInitialStates().contains(e.head());
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) &&
                isStateTerminal(ts, e.last());
    }

    @Override
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        return post(ts, s).isEmpty();
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> postSet = new HashSet<>();

        Iterator<? extends Transition<S, ?>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(currentTransition.getFrom().equals(s))
                postSet.add(currentTransition.getTo());
        }

        return postSet;
    }

    @Override
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        if(!ts.getStates().containsAll(c))
            throw new StateNotFoundException(c);

        Set<S> postSet = new HashSet<>();

        Iterator<? extends Transition<S, ?>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(c.contains(currentTransition.getFrom()))
                postSet.add(currentTransition.getTo());
        }

        return postSet;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> postSet = new HashSet<>();

        Iterator<Transition<S, A>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(currentTransition.getFrom().equals(s) && currentTransition.getAction().equals(a))
                postSet.add(currentTransition.getTo());
        }

        return postSet;
    }

    @Override
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        if(!ts.getStates().containsAll(c))
            throw new StateNotFoundException(c);

        Set<S> postSet = new HashSet<>();

        Iterator<Transition<S, A>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(c.contains(currentTransition.getFrom()) && currentTransition.getAction().equals(a))
                postSet.add(currentTransition.getTo());
        }

        return postSet;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> postSet = new HashSet<>();

        Iterator<? extends Transition<S, ?>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(currentTransition.getTo().equals(s))
                postSet.add(currentTransition.getFrom());
        }

        return postSet;
    }

    @Override
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        if(!ts.getStates().containsAll(c))
            throw new StateNotFoundException(c);

        Set<S> postSet = new HashSet<>();

        Iterator<? extends Transition<S, ?>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(c.contains(currentTransition.getTo()))
                postSet.add(currentTransition.getFrom());
        }

        return postSet;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if(!ts.getStates().contains(s))
            throw new StateNotFoundException(s);

        Set<S> postSet = new HashSet<>();

        Iterator<Transition<S, A>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(currentTransition.getTo().equals(s) && currentTransition.getAction().equals(a))
                postSet.add(currentTransition.getFrom());
        }

        return postSet;
    }

    @Override
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        if(!ts.getStates().containsAll(c))
            throw new StateNotFoundException(c);

        Set<S> postSet = new HashSet<>();

        Iterator<Transition<S, A>> transitionIterator = ts.getTransitions().iterator();
        while (transitionIterator.hasNext()){
            Transition<S, ?> currentTransition = transitionIterator.next();
            if(c.contains(currentTransition.getTo()) && currentTransition.getAction().equals(a))
                postSet.add(currentTransition.getFrom());
        }

        return postSet;
    }

    @Override
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        Set<S> closeReach = new HashSet<S>(), openReach = ts.getInitialStates();
        while(!openReach.isEmpty()){
            Set<S> newOpenReach = new HashSet<S>();
            Iterator<S> currOpenReachIterator = openReach.iterator();
            while(currOpenReachIterator.hasNext()){
                S currState = currOpenReachIterator.next();
                Iterator<S> currPostIterator = post(ts, currState).iterator();
                while(currPostIterator.hasNext()){
                    S currPostState = currPostIterator.next();
                    if(!closeReach.contains(currPostState) && !openReach.contains(currPostState))
                        newOpenReach.add(currPostState);
                }
            }
            closeReach.addAll(openReach);
            openReach = newOpenReach;
        }

        return closeReach;
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, new HashSet<A>());
    }

    @Override
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1, TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {
        TransitionSystem<Pair<S1, S2>, A, P> interleavedTS = new TransitionSystemImpl<Pair<S1, S2>, A, P>();

        // add aps to interleavedTS
        interleavedTS.addAllAtomicPropositions(ts1.getAtomicPropositions());
        interleavedTS.addAllAtomicPropositions(ts2.getAtomicPropositions());

        // create <Pair<S1, S2>> for interleavedTS
        Iterator<S1> s1Iterator = ts1.getStates().iterator();
        while(s1Iterator.hasNext()){
            S1 currS1 = s1Iterator.next();

            Iterator<S2> s2Iterator = ts2.getStates().iterator();
            while (s2Iterator.hasNext()){
                S2 currS2 = s2Iterator.next();
                Pair<S1, S2> stateToAdd = new Pair<S1, S2>(currS1, currS2);
                interleavedTS.addState(stateToAdd);

                //add all labels to new state
                Iterator<P> currS1Labels = ts1.getLabel(currS1).iterator(),
                        currS2Labels = ts2.getLabel(currS2).iterator();
                while(currS1Labels.hasNext())
                    interleavedTS.addToLabel(stateToAdd, currS1Labels.next());
                while(currS2Labels.hasNext())
                    interleavedTS.addToLabel(stateToAdd, currS2Labels.next());
            }
        }

        // add initial states to interleavedTS
        Iterator<S1> s1Initials = ts1.getInitialStates().iterator();
        while (s1Initials.hasNext()){
            S1 currS1Initial = s1Initials.next();

            Iterator<S2> s2Initials = ts2.getInitialStates().iterator();
            while (s2Initials.hasNext()){
                S2 currS2Initial = s2Initials.next();

                interleavedTS.setInitial(new Pair<S1, S2>(currS1Initial, currS2Initial), true);
            }
        }

        // add actions to interleavedTS
        interleavedTS.addAllActions(ts1.getActions());
        interleavedTS.addAllActions(ts2.getActions());

        // go over all the transitions in handShakingActions.
        Iterator<Transition<S1, A>> t1Iterator = ts1.getTransitions().iterator();
        while(t1Iterator.hasNext()){
            Transition<S1, A> currentT1 = t1Iterator.next();

            Iterator<Transition<S2, A>> t2Iterator = ts2.getTransitions().iterator();
            while(t2Iterator.hasNext()){
                Transition<S2, A> currentT2 = t2Iterator.next();
                if(currentT1.getAction() == currentT2.getAction() &&
                        handShakingActions.contains(currentT1.getAction())){
                    interleavedTS.addTransition(new Transition<Pair<S1, S2>, A>(
                            new Pair<S1, S2>(currentT1.getFrom(), currentT2.getFrom()),
                            currentT1.getAction(),
                            new Pair<S1, S2>(currentT1.getTo(), currentT2.getTo())
                    ));
                }
            }
        }

        //go over all ts1 transition and add no handshaking transitions.
        t1Iterator = ts1.getTransitions().iterator();
        while(t1Iterator.hasNext()){
            Transition<S1, A> currentT1 = t1Iterator.next();
            if(!handShakingActions.contains(currentT1.getAction())){
                Iterator<S2> s2Iterator = ts2.getStates().iterator();
                while(s2Iterator.hasNext()){
                    S2 currS2 = s2Iterator.next();
                    interleavedTS.addTransition(new Transition<Pair<S1,S2>, A>(
                            new Pair<S1, S2>(currentT1.getFrom(), currS2),
                            currentT1.getAction(),
                            new Pair<S1, S2>(currentT1.getTo(), currS2)
                    ));
                }
            }
        }

        //go over all ts2 transition and add no handshaking transitions.
        Iterator<Transition<S2, A>> t2Iterator = ts2.getTransitions().iterator();
        while(t2Iterator.hasNext()){
            Transition<S2, A> currentT2 = t2Iterator.next();
            if(!handShakingActions.contains(currentT2.getAction())){
                s1Iterator = ts1.getStates().iterator();
                while(s1Iterator.hasNext()){
                    S1 currS1 = s1Iterator.next();
                    interleavedTS.addTransition(new Transition<Pair<S1,S2>, A>(
                            new Pair<S1, S2>(currS1, currentT2.getFrom()),
                            currentT2.getAction(),
                            new Pair<S1, S2>(currS1, currentT2.getTo())
                    ));
                }
            }
        }

        //filter out all unreachable states
        Set<Pair<S1, S2>> reachable = reach(interleavedTS), nonReachable = interleavedTS.getStates();
        nonReachable.removeAll(reachable);

        Iterator<Pair<S1, S2>> nonReachableIterator = nonReachable.iterator();
        while(nonReachableIterator.hasNext()){
            Pair<S1, S2> currState = nonReachableIterator.next();
            interleavedTS.setInitial(currState, false);

            // remove all state transactions
            Iterator<Transition<Pair<S1, S2>, A>> interleaveTransitions = interleavedTS.getTransitions().iterator();
            while(interleaveTransitions.hasNext()){
                Transition<Pair<S1, S2>, A> currT = interleaveTransitions.next();
                if(currT.getFrom().equals(currState) || currT.getTo().equals(currState))
                    interleavedTS.removeTransition(currT);
            }

            // remove all state labels
            Iterator<P> labels = interleavedTS.getLabel(currState).iterator();
            while(labels.hasNext()){
                P currL =labels.next();
                interleavedTS.removeLabel(currState, currL);
            }

            //remove the state itself
            interleavedTS.removeState(currState);
        }

        return interleavedTS;
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraphImpl<>();
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> interleavedPG = new ProgramGraphImpl<Pair<L1, L2>, A>();

        // create locations
        for(L1 loc1 :
                pg1.getLocations()){
            for (L2 loc2 :
                    pg2.getLocations()) {
                interleavedPG.addLocation(new Pair<>(loc1, loc2));
            }
        }

        // create initials
        for (L1 init1 :
                pg1.getInitialLocations()) {
            for (L2 init2 :
                    pg2.getInitialLocations()) {
                interleavedPG.setInitial(new Pair<>(init1, init2), true);
            }
        }

        // create initializations
        for (List<String> init1 :
                pg1.getInitalizations()) {
            for (List<String> init2 :
                    pg2.getInitalizations()) {
                List<String> unionList = new ArrayList<>();
                unionList.addAll(init1);
                unionList.addAll(init2);
                interleavedPG.addInitalization(unionList);
            }
        }

        // create transitions
        for (PGTransition<L1, A> t1 :
                pg1.getTransitions()) {
            for (L2 loc2 :
                    pg2.getLocations()) {
                interleavedPG.addTransition(new PGTransition<>(
                        new Pair<>(t1.getFrom(), loc2),
                        t1.getCondition(),
                        t1.getAction(),
                        new Pair<>(t1.getTo(), loc2)
                ));
            }
        }
        for (PGTransition<L2, A> t2 :
                pg2.getTransitions()) {
            for (L1 loc1 :
                    pg1.getLocations()) {
                interleavedPG.addTransition(new PGTransition<>(
                        new Pair<>(loc1, t2.getFrom()),
                        t2.getCondition(),
                        t2.getAction(),
                        new Pair<>(loc1, t2.getTo())
                ));
            }
        }

        return interleavedPG;
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ans = new TransitionSystemImpl<>();
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> closeState = new HashSet<Pair<Map<String, Boolean>, Map<String, Boolean>>>(),
                openState = new HashSet<Pair<Map<String, Boolean>, Map<String, Boolean>>>();

        // initialize a map with zero for all registers.
        Map<String, Boolean> zeroRegisterMap = new HashMap<String, Boolean>();
        for (String rName : c.getRegisterNames()){
            zeroRegisterMap.put(rName, false);
        }

        // fill openState with initial states
        Set<String> inputNames = c.getInputPortNames();
        List<String> inputNamesList = new ArrayList<String>(inputNames);
        int numOfDifferentInputs = (int)Math.pow(2, inputNames.size());
        for(int n = 0 ; n < numOfDifferentInputs ; n++){
            Map<String, Boolean> inputsMap = new HashMap<String, Boolean>();


            // set inputsArray values by the number binaries
            String binaryN = Integer.toBinaryString(n);

            for(int i=0 ; i < inputNamesList.size() ; i++){
                boolean boolAns;
                if(i < binaryN.length())
                    boolAns = (binaryN.charAt(binaryN.length()-i-1) == '1');
                else
                    boolAns = false;
                inputsMap.put(inputNamesList.get(i), boolAns);
            }

            // add permutation (inputsMap) as action to ans
            ans.addAction(inputsMap);

            Pair<Map<String, Boolean>, Map<String, Boolean>> newState = new Pair<Map<String, Boolean>, Map<String, Boolean>>(inputsMap, zeroRegisterMap);
            openState.add(newState);
            ans.addState(newState);
            ans.setInitial(newState, true);

        }

        // expand all nodes iterative until no new nodes are left to expand
        Set<Map<String, Boolean>> actions = ans.getActions();
        while(!openState.isEmpty()){
            HashSet<Pair<Map<String, Boolean>, Map<String, Boolean>>> newOpenState = new HashSet<Pair<Map<String, Boolean>, Map<String, Boolean>>>();
            for (Pair<Map<String, Boolean>, Map<String, Boolean>> currOpenState:
                    openState) {
                for (Map<String, Boolean> currAction :
                        actions) {
                    Pair<Map<String, Boolean>, Map<String, Boolean>> toState = new Pair<>(currAction, c.updateRegisters(currOpenState.getFirst(), currOpenState.getSecond()));
                    if(!openState.contains(toState) && !closeState.contains(toState)) {
                        newOpenState.add(toState);
                        ans.addState(toState);
                    }
                    ans.addTransition(new Transition<>(currOpenState, currAction, toState));
                }
                closeState.add(currOpenState);
            }
            openState = newOpenState;
        }

        //add all possible labels as labels to ans
        for(String input:c.getInputPortNames())
            ans.addAtomicProposition(input);
        for(String register:c.getRegisterNames())
            ans.addAtomicProposition(register);
        for(String output:c.getOutputPortNames())
            ans.addAtomicProposition(output);

        // add labels to all states
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state :
                closeState) {
            Map<String, Boolean> inputMap = state.getFirst(),
                    registerMap = state.getSecond();
            Map<String, Boolean> outputMap = c.computeOutputs(inputMap, registerMap);

            // add all true entries' labels as labels for current state
            for ( Map.Entry<String, Boolean> inputEntry :
                    inputMap.entrySet()) {
                if(inputEntry.getValue())
                    ans.addToLabel(state, inputEntry.getKey());
            }
            for ( Map.Entry<String, Boolean> registerEntry :
                    registerMap.entrySet()) {
                if(registerEntry.getValue())
                    ans.addToLabel(state, registerEntry.getKey());
            }
            for ( Map.Entry<String, Boolean> outputEntry :
                    outputMap.entrySet()) {
                if(outputEntry.getValue())
                    ans.addToLabel(state, outputEntry.getKey());
            }
        }

        return ans;
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<L, Map<String, Object>>, A, String> ansTransitionSystem = new TransitionSystemImpl<>();
        Set<Pair<L, Map<String, Object>>> openState = new HashSet<>(),
                closeState = new HashSet<>();

        // build initials for openState
        if(!pg.getInitalizations().isEmpty()) {
            for (List<String> init :
                    pg.getInitalizations()) {

                // get the variables values after the effect of initial actions.
                Map<String, Object> currValues = new HashMap<>();
                for (String currAct :
                        init) {
                    currValues = ActionDef.effect(actionDefs, currValues, currAct);
                }

                buildInitialStatePGtoTS((ProgramGraph<L, A>) pg, (TransitionSystem<Pair<L, Map<String, Object>>, A, String>) ansTransitionSystem, (Set<Pair<L, Map<String, Object>>>) openState, currValues);
            }
        }
        else{
            Map<String, Object> currValues = new HashMap<>();
            buildInitialStatePGtoTS((ProgramGraph<L,A>) pg, (TransitionSystem<Pair<L,Map<String,Object>>,A,String>) ansTransitionSystem, (Set<Pair<L,Map<String,Object>>>) openState, currValues);
        }

        // expand iteratively every state in openState until no states to expand
        while(!openState.isEmpty()){
            Set<Pair<L, Map<String, Object>>> newOpenState = new HashSet<>();

            for (Pair<L, Map<String, Object>> currState:
                    openState) {

                // handle every transition the from state is currState
                Set<PGTransition<L, A>> pgTransitions = pg.getTransitions();
                for (PGTransition<L, A> currTransition:
                        pgTransitions) {
                    if(currTransition.getFrom().equals(currState.getFirst()) &&
                            ConditionDef.evaluate(conditionDefs, currState.getSecond(), currTransition.getCondition())){

                        ansTransitionSystem.addAction(currTransition.getAction());
                        Pair<L, Map<String, Object>> newState = new Pair<>(currTransition.getTo(),ActionDef.effect(actionDefs, currState.getSecond(), currTransition.getAction()));

                        // first time we see this state
                        if(!openState.contains(newState) && !closeState.contains(newState)){
                            newOpenState.add(newState);
                            ansTransitionSystem.addState(newState);
                            // add labels to new state
                            ansTransitionSystem.addAtomicProposition(newState.getFirst().toString());
                            ansTransitionSystem.addToLabel(newState, newState.getFirst().toString());
                            for(String currVar
                                    : newState.getSecond().keySet())
                            {
                                ansTransitionSystem.addAtomicProposition(currVar+" = "+newState.getSecond().get(currVar));
                                ansTransitionSystem.addToLabel(newState, currVar+" = "+newState.getSecond().get(currVar));
                            }
                        }

                        ansTransitionSystem.addTransition(new Transition<>(currState, currTransition.getAction(), newState));
                    }
                }
                closeState.add(currState);
            }
            openState = newOpenState;
        }

        return ansTransitionSystem;
    }

    private <L, A> void buildInitialStatePGtoTS(ProgramGraph<L, A> pg, TransitionSystem<Pair<L, Map<String, Object>>, A, String> ansTransitionSystem, Set<Pair<L, Map<String, Object>>> openState, Map<String, Object> currValues) {
        for (L loc :
                pg.getInitialLocations()) {
            Pair<L, Map<String, Object>> currState = new Pair<>(loc, currValues);

            // add the state to openState
            openState.add(currState);

            // add state to intials
            ansTransitionSystem.addState(currState);
            ansTransitionSystem.setInitial(currState, true);

            //add state labels
            ansTransitionSystem.addAtomicProposition(loc.toString());
            ansTransitionSystem.addToLabel(currState, loc.toString());

            // add variables values as labels.
            for (String currVar :
                    currValues.keySet()) {
                ansTransitionSystem.addAtomicProposition(currVar + " = " + currValues.get(currVar));
                ansTransitionSystem.addToLabel(currState, currVar + " = " + currValues.get(currVar));
            }
        }
    }

    private <L, A> void buildInitialStateCStoTS(ProgramGraph<L, A> pg, TransitionSystem<Pair<L, Map<String, Object>>, A, String> ansTransitionSystem, Set<Pair<L, Map<String, Object>>> openState, Map<String, Object> currValues) {
        for (L loc :
                pg.getInitialLocations()) {
            Pair<L, Map<String, Object>> currState = new Pair<>(loc, currValues);

            // add the state to openState
            openState.add(currState);

            // add state to intials
            ansTransitionSystem.addState(currState);
            ansTransitionSystem.setInitial(currState, true);
        }
    }

    private <L, A> ProgramGraph<List<L>, A> adaptFirstCS(ProgramGraph<L, A> firstPg){
        ProgramGraph<List<L>, A> ansPG = new ProgramGraphImpl<>();
        // add locations
        for (L currLoc :
                firstPg.getLocations()) {
            List<L> newLoc = new ArrayList<L>();
            newLoc.add(currLoc);
            ansPG.addLocation(newLoc);
        }

        //add initials
        for (L initLoc :
                firstPg.getInitialLocations()) {
            List<L> newLoc = new ArrayList<>();
            newLoc.add(initLoc);
            ansPG.setInitial(newLoc, true);
        }

        //add initializations
        for (List<String> initialization:
                firstPg.getInitalizations()){
            ansPG.addInitalization(initialization);
        }

        //add transitions
        for (PGTransition<L, A> currTrans :
                firstPg.getTransitions()) {
            List<L> newFrom = new ArrayList<>();
            newFrom.add(currTrans.getFrom());
            List<L> newTo = new ArrayList<>();
            newTo.add(currTrans.getTo());

            PGTransition<List<L>, A> newTrans = new PGTransition<>(newFrom, currTrans.getCondition(),
                    currTrans.getAction(), newTo);

            ansPG.addTransition(newTrans);
        }

        ansPG.setName(firstPg.getName());

        return ansPG;

    }

    private <L, A> ProgramGraph<List<L>, A> listInterleave(ProgramGraph<List<L>, A> pg1, ProgramGraph<L, A> pg2){
        ProgramGraph<List<L>, A> interleavedPG = new ProgramGraphImpl<List<L>, A>();

        // create locations
        for(List<L> loc1 :
                pg1.getLocations()){
            for (L loc2 :
                    pg2.getLocations()) {
                List<L> newL = new ArrayList<>();
                newL.addAll(loc1);
                newL.add(loc2);
                interleavedPG.addLocation(newL);
            }
        }

        // create initials
        for (List<L> init1 :
                pg1.getInitialLocations()) {
            for (L init2 :
                    pg2.getInitialLocations()) {
                List<L> newL = new ArrayList<>();
                newL.addAll(init1);
                newL.add(init2);
                interleavedPG.setInitial(newL, true);
            }
        }

        if(pg1.getInitalizations().size() > 0) {
            for (List<String> init1 :
                    pg1.getInitalizations()) {
                for (List<String> init2 :
                        pg2.getInitalizations()) {
                    List<String> init = new ArrayList<>();
                    init.addAll(init1);
                    init.addAll(init2);
                    interleavedPG.addInitalization(init);
                }
            }
        } else {
            for (List<String> init2 :
                    pg2.getInitalizations()) {
                interleavedPG.addInitalization(init2);
            }
        }

        ParserBasedInterleavingActDef parserAD = new ParserBasedInterleavingActDef();

        //create transitions
        for (PGTransition<List<L>, A> t1 :
                pg1.getTransitions()) {
            if(parserAD.isOneSidedAction(t1.getAction().toString())){
                if(t1.getAction().toString().charAt(t1.getAction().toString().length() - 1) == '?'){
                    String act1 = t1.getAction().toString();
                    for (PGTransition<L, A> t2 :
                            pg2.getTransitions()) {
                        String act2 = t2.getAction().toString();
                        if(parserAD.isOneSidedAction(act2) &&
                                act1.substring(0, act1.length() - 1).equals(act2.substring(0, act2.length() - 1)) &&
                                act2.charAt(act2.length() - 1) == '!'){

                            List<L> newFrom = new ArrayList<>();
                            newFrom.addAll(t1.getFrom());
                            newFrom.add(t2.getFrom());

                            List<L> newTo = new ArrayList<>();
                            newTo.addAll(t1.getTo());
                            newTo.add(t2.getTo());

                            //String newAct = act1 + "|" + act2;
                            String newAct = t1.getAction().toString() + "|" + t2.getAction().toString();

                            interleavedPG.addTransition(new PGTransition<>(
                                    newFrom,
                                    t1.getCondition(),
                                    (A) newAct,
                                    newTo
                            ));
                        }
                    }
                }
                else{ //type: C!5
                    String act1 = t1.getAction().toString();
                    for (PGTransition<L, A> t2 :
                            pg2.getTransitions()) {
                        String act2 = t2.getAction().toString();
                        if(parserAD.isOneSidedAction(act2) &&
                                act1.substring(0, act1.length() - 1).equals(act2.substring(0, act2.length() - 1)) &&
                                act2.charAt(act2.length() - 1) == '?'){

                            List<L> newFrom = new ArrayList<>();
                            newFrom.addAll(t1.getFrom());
                            newFrom.add(t2.getFrom());

                            List<L> newTo = new ArrayList<>();
                            newTo.addAll(t1.getTo());
                            newTo.add(t2.getTo());

                            String newAct = t1.getAction().toString() + "|" + t2.getAction().toString();

                            interleavedPG.addTransition(new PGTransition<>(
                                    newFrom,
                                    t1.getCondition(),
                                    (A) newAct,
                                    newTo
                            ));
                        }
                    }
                }
            }
            else{
                for (L loc2 :
                        pg2.getLocations()) {
                    List<L> fromList = new ArrayList<>();
                    fromList.addAll(t1.getFrom());
                    fromList.add(loc2);
                    List<L> toList = new ArrayList<>();
                    toList.addAll(t1.getTo());
                    toList.add(loc2);

                    interleavedPG.addTransition(new PGTransition<>(
                            fromList,
                            t1.getCondition(),
                            t1.getAction(),
                            toList
                    ));
                }
            }
        }

        for (PGTransition<L, A> t2 :
                pg2.getTransitions()) {
            if(!parserAD.isOneSidedAction((String)t2.getAction())){
                for (List<L> loc1 :
                        pg1.getLocations()) {
                    List<L> fromList = new ArrayList<>();
                    fromList.addAll(loc1);
                    fromList.add(t2.getFrom());
                    List<L> toList = new ArrayList<>();
                    toList.addAll(loc1);
                    toList.add(t2.getTo());
                    interleavedPG.addTransition(new PGTransition<>(
                            fromList,
                            t2.getCondition(),
                            t2.getAction(),
                            toList
                    ));
                }
            }
        }

        return interleavedPG;
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {

        if(cs.getProgramGraphs().size() == 0)
            return new TransitionSystemImpl<>();
        List<ProgramGraph<L, A>> PGs = cs.getProgramGraphs();

        //first change the first PG into a PG of List<L> states' type
        ProgramGraph<List<L>, A> currPG = adaptFirstCS(PGs.get(0));

        // i = 1 to skip first
        // interleave all PGs into 1 PG and then make a TS out of it
        for(int i = 1; i < PGs.size() ; i++)
            currPG = listInterleave(currPG, PGs.get(i));

        Set<ActionDef> acList = new LinkedHashSet<>();
        acList.add(new ParserBasedInterleavingActDef());
        acList.add(new ParserBasedActDef());

        Set<ConditionDef> cdList = new HashSet<>();
        cdList.add(new ParserBasedCondDef());

        return transitionSystemFromProgramGraphOfCS(currPG,acList,cdList); // what to add in actiondDefs, conditionDefs ?! :(

    }

    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String>
    transitionSystemFromProgramGraphOfCS(ProgramGraph<List<L>, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> ansTransitionSystem = new TransitionSystemImpl<>();
        Set<Pair<List<L>, Map<String, Object>>> openState = new HashSet<>(),
                closeState = new HashSet<>();

        // build initials for openState
        if(!pg.getInitalizations().isEmpty()) {
            for (List<String> init :
                    pg.getInitalizations()) {

                // get the variables values after the effect of initial actions.
                Map<String, Object> currValues = new HashMap<>();
                for (String currAct :
                        init) {
                    currValues = ActionDef.effect(actionDefs, currValues, currAct);
                }

                buildInitialStateCStoTS((ProgramGraph<List<L>, A>) pg, (TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String>) ansTransitionSystem, (Set<Pair<List<L>, Map<String, Object>>>) openState, currValues);
            }
        }
        else{
            Map<String, Object> currValues = new HashMap<>();
            buildInitialStateCStoTS((ProgramGraph<List<L>,A>) pg, (TransitionSystem<Pair<List<L>,Map<String,Object>>,A,String>) ansTransitionSystem, (Set<Pair<List<L>,Map<String,Object>>>) openState, currValues);
        }

        // expand iteratively every state in openState until no states to expand
        while(!openState.isEmpty()){
            Set<Pair<List<L>, Map<String, Object>>> newOpenState = new HashSet<>();

            for (Pair<List<L>, Map<String, Object>> currState:
                    openState) {

                // handle every transition the from state is currState
                Set<PGTransition<List<L>, A>> pgTransitions = pg.getTransitions();
                for (PGTransition<List<L>, A> currTransition:
                        pgTransitions) {
                    if(currTransition.getFrom().equals(currState.getFirst()) &&
                            ConditionDef.evaluate(conditionDefs, currState.getSecond(), currTransition.getCondition())){

                        ansTransitionSystem.addAction(currTransition.getAction());
                        if(ActionDef.effect(actionDefs, currState.getSecond(), currTransition.getAction()) == null)
                            continue;
                        Pair<List<L>, Map<String, Object>> newState = new Pair<>(currTransition.getTo(), ActionDef.effect(actionDefs, currState.getSecond(), currTransition.getAction()));

                        // first time we see this state
                        if(!openState.contains(newState) && !closeState.contains(newState)){
                            newOpenState.add(newState);
                            ansTransitionSystem.addState(newState);
                        }

                        ansTransitionSystem.addTransition(new Transition<>(currState, currTransition.getAction(), newState));
                    }
                }
                closeState.add(currState);
            }
            openState = newOpenState;
        }

        //add labels to all states
        for (Pair<List<L>, Map<String, Object>> currState :
                ansTransitionSystem.getStates()) {

            // add all L type states as labels
            for (L currL:
                    currState.getFirst()) {
                ansTransitionSystem.addAtomicProposition(currL.toString());
                ansTransitionSystem.addToLabel(currState, currL.toString());
            }

            // add all variables values as labels
            for (Map.Entry<String, Object> ent :
                    currState.getSecond().entrySet()) {
                String newLabel = ent.getKey() + " = " + ent.getValue().toString();
                ansTransitionSystem.addAtomicProposition(newLabel);
                ansTransitionSystem.addToLabel(currState, newLabel);
            }
        }


        return ansTransitionSystem;
    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<Sts, Saut>, A, Saut> ansTS = new TransitionSystemImpl<>();
        Set<Pair<Sts, Saut>> openSet = new HashSet<>(), closeSet = new HashSet<>();

        //add initial states
        for (Sts currTsState :
                ts.getInitialStates()) {
            for (Saut currAutInitial :
                    aut.getInitialStates()) {
                for (Saut currAutNext:
                        aut.nextStates(currAutInitial, ts.getLabel(currTsState))) {
                    Pair<Sts, Saut> newState = new Pair<>(currTsState, currAutNext);
                    ansTS.addState(newState);
                    ansTS.setInitial(newState, true);
                    openSet.add(newState);
                }
            }
        }

        //add actions
        ansTS.addAllActions(ts.getActions());

        // expand all reachable ansTS states and transitions
        while (openSet.size() > 0){
            Set<Pair<Sts, Saut>> newOpenSet = new HashSet<>();
            for (Pair<Sts, Saut> currState :
                    openSet) {
                for (Transition<Sts, A> currTrans :
                        ts.getTransitions()) {
                    if(currState.getFirst().equals(currTrans.getFrom())){
                        Set<Saut> nexts = aut.nextStates(currState.getSecond(), ts.getLabel(currTrans.getTo()));
                        if(nexts != null){
                            for (Saut nextAutoS :
                                    nexts) {
                                Pair<Sts, Saut> newState = new Pair<>(currTrans.getTo(), nextAutoS);
                                Transition<Pair<Sts, Saut>, A> newTrans = new Transition<>(
                                        currState,
                                        currTrans.getAction(),
                                        newState);
                                if(!openSet.contains(newState) && !closeSet.contains(newState)){
                                    ansTS.addState(newState);
                                    newOpenSet.add(newState);
                                }
                                ansTS.addTransition(newTrans);
                            }
                        }
                    }
                }
            }
            closeSet.addAll(openSet);
            openSet = newOpenSet;
        }

        //add labels to states.
        for (Pair<Sts, Saut> currState :
                ansTS.getStates()) {
            ansTS.addAtomicProposition(currState.getSecond());
            ansTS.addToLabel(currState, currState.getSecond());
        }

        return ansTS;
    }

    @Override
    //implement
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        return programGraphFromNP(NanoPromelaFileReader.pareseNanoPromelaFile(filename));
    }

    @Override
    //implement
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        return programGraphFromNP(NanoPromelaFileReader.pareseNanoPromelaString(nanopromela));
    }

    @Override
    //implement
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        return programGraphFromNP(NanoPromelaFileReader.parseNanoPromelaStream(inputStream));
    }

    private ProgramGraph<String , String> programGraphFromNP(StmtContext sc){
        ProgramGraph<String, String> new_graph = (new FvmFacadeImpl()).createProgramGraph();
        Set<List<StmtContext>> states = new HashSet<>();
        ArrayList<StmtContext> list_sc =  new ArrayList<>();
        Set<Temp_Transition> transitions = new HashSet<>();
        list_sc.add(sc);
        //new_graph.addInitalization(getNameOfState(list_sc));

        states.add(list_sc);
        Set<List<StmtContext>> copy_states =  new HashSet<>(states);
        while (!copy_states.isEmpty()) {
            Set<List<StmtContext>> new_states = new HashSet<>();
            for (List<StmtContext> list : copy_states) {
                Set<Temp_Transition> new_transions = create_transions(list);
                transitions.addAll(new_transions);
                for (Temp_Transition trans : new_transions) {
                    if (!states.contains(trans.getDest_stmt())){
                        states.add(trans.getDest_stmt());
                        new_states.add(trans.getDest_stmt());
                    }
                }
            }
            copy_states = new_states;
        }
        for(List<StmtContext> stmt : states) {
            List<StmtContext> copy_stmt = new ArrayList<>(stmt);
            new_graph.addLocation(getNameOfState(copy_stmt));
        }
        List<String> name_init = new ArrayList<>();
        name_init.add(getNameOfState(list_sc));
        //new_graph.addInitalization(name_init);
        list_sc.add(sc);
        new_graph.setInitial(getNameOfState(list_sc),true);
        for (Temp_Transition trans : transitions) {
            String source = getNameOfState(trans.getSource_stmt());
            String dest = getNameOfState(trans.getDest_stmt());
            new_graph.addTransition(new PGTransition<>(source, trans.getCondition(), trans.getAction(), dest));
        }

        return new_graph;
    }
    private String getNameOfState(List<StmtContext> list_stmt){
        if(list_stmt.isEmpty())
            return "";
        String ans = list_stmt.get(0).getText();
        list_stmt.remove(0);
        for(StmtContext stmt : list_stmt){
            ans = ans + ';' + stmt.getText();
        }
        return ans;
    }

    private Set<Temp_Transition> create_transions(List<StmtContext> stmt) {
        if (stmt.isEmpty()){
            HashSet<Temp_Transition> ans = new HashSet<>();
            return ans;
        }
        if (stmt.get(0).assstmt() != null || stmt.get(0).chanreadstmt() != null || stmt.get(0).chanwritestmt() != null || stmt.get(0).atomicstmt() != null || stmt.get(0).skipstmt() != null) {
            List<StmtContext> dest = new ArrayList<StmtContext>(stmt);
            dest.remove(0);
            HashSet<Temp_Transition> ans = new HashSet<>();
            List<StmtContext> copy_stmt = new ArrayList<>(stmt);
            ans.add(new Temp_Transition(copy_stmt ,  dest ,"" , stmt.get(0).getText()));
            return ans;
        }
        else {
            if (stmt.get(0).ifstmt() != null) {
                HashSet<Temp_Transition> ans = new HashSet<>();
                for (OptionContext option : stmt.get(0).ifstmt().option()) {
                    Set<Temp_Transition> optiontTrans = create_transions(Arrays.asList(option.stmt()));
                    for (Temp_Transition trans : optiontTrans) {
                        String conditions = "(" + option.boolexpr().getText() + ")" + ((!trans.getCondition().isEmpty()) ? " && (" + trans.getCondition() + ")" : "");
                        List<StmtContext> dests = new ArrayList<StmtContext>(trans.getDest_stmt());
                        dests.addAll(stmt.subList(1, stmt.size()));
                        List<StmtContext> copy_stmt = new ArrayList<>(stmt);
                        ans.add(new Temp_Transition(copy_stmt, dests ,conditions, trans.getAction()));

                    }
                }

                return ans;
            } else if (stmt.get(0).dostmt() != null) {
                HashSet<Temp_Transition> ans = new HashSet<>();
                for (OptionContext option : stmt.get(0).dostmt().option()) {
                    Set<Temp_Transition> optionTrans = create_transions(Arrays.asList(option.stmt()));
                    for (Temp_Transition trans : optionTrans) {
                        String conditions = "(" + option.boolexpr().getText() + ")" + ((!trans.getCondition().isEmpty()) ? " && (" + trans.getCondition() + ")" : "");
                        List<StmtContext> dests = new ArrayList<>(trans.getDest_stmt());
                        dests.addAll(stmt);
                        List<StmtContext> copy_stmt = new ArrayList<>(stmt);
                        ans.add(new Temp_Transition(copy_stmt,  dests,conditions, trans.getAction()));
                    }
                }
                List<StmtContext> locations = new ArrayList<>(stmt);
                locations.remove(0);
                String bools = "";
                String or = "";
                for (OptionContext option : stmt.get(0).dostmt().option()) {
                    if (!option.boolexpr().getText().isEmpty()) {
                        bools += (or + "(" + option.boolexpr().getText() + ")");
                        or = "||";
                    }
                }
                List<StmtContext> copy_stmt = new ArrayList<>(stmt);
                ans.add(new Temp_Transition(copy_stmt, locations , "!(" + bools + ")", "" ));
                return ans;
            } else {
                HashSet<Temp_Transition> ans = new HashSet<>();
                Set<Temp_Transition> transitions = create_transions(Arrays.asList(stmt.get(0).stmt(0)));
                for (Temp_Transition trans : transitions) {
                    List<StmtContext> dests = new ArrayList<>(trans.getDest_stmt());
                    List<StmtContext> statem = stmt.get(0).stmt();
                    dests.addAll(statem.subList(1, statem.size()));
                    List<StmtContext> copy_stmt = new ArrayList<>(stmt);
                    ans.add(new Temp_Transition(copy_stmt, dests ,trans.getCondition(), trans.getAction() ));
                }
                return ans;
            }
        }
    }

    public <S, A, P> boolean cycle_check(TransitionSystem<S, A, P> ts, S s, Stack<S> statesStack){
        Set<S> visited = new HashSet<>();
        boolean cycle_found = false;
        statesStack.push(s);
        visited.add(s);

        do{
            S currS = statesStack.peek();
            Set<S> currSPost = post(ts, currS);
            if(currSPost.contains(s)){
                cycle_found = true;
                //statesStack.push(s);
            }
            else{
                currSPost.removeAll(visited);
                if(!currSPost.isEmpty()){
                    S currS2 = currSPost.iterator().next();
                    statesStack.push(currS2);
                    visited.add(currS2);
                }
                else{
                    statesStack.pop();
                }
            }
        } while (!statesStack.isEmpty() && !cycle_found);
        return cycle_found;
    }

    public <S, Saut> List<S> getList(Stack<Pair<S, Saut>> statesStack){
        List<S> ans = new ArrayList<>();
        for (Pair<S, Saut> currS:
                statesStack) {
            ans.add(currS.getFirst());
        }
        return ans;
    }

    public <S, A, P, Saut> List<S> getPrefList(TransitionSystem<Pair<S, Saut>, A, Saut> ts, Pair<S, Saut> s){
        for(Pair<S, Saut> currInit:
                ts.getInitialStates()){
            boolean path_found = false;
            Stack<Pair<S, Saut>> sStack = new Stack<>();
            Set<Pair<S, Saut>> visited = new HashSet<>();
            visited.add(currInit);
            sStack.push(currInit);
            do {
                Pair<S, Saut> currS = sStack.peek();
                Set<Pair<S, Saut>> currSPost = post(ts, currS);
                if(currSPost.contains(s)){
                    path_found = true;
                    //sStack.push(s);
                }
                else{
                    currSPost.removeAll(visited);
                    if(!currSPost.isEmpty()){
                        Pair<S, Saut> currS2 = currSPost.iterator().next();
                        sStack.push(currS2);
                        visited.add(currS2);
                    }
                    else{
                        sStack.pop();
                    }
                }
            } while(!sStack.isEmpty() && !path_found);
            if(path_found)
                return getList(sStack);
/*            Stack<Pair<S, Saut>> sStack = new Stack<>();
            Set<Pair<S, Saut>> visited = new HashSet<>();
            visited.add(s);
            visited.add(currInit);
            sStack.push(currInit);
            do {
                Pair<S, Saut> currS = sStack.peek();
                Set<Pair<S, Saut>> currSPost = post(ts, currS);
                if(visited.containsAll(currSPost)){
                    sStack.pop();
                    if(currS.equals(s))
                        return getList(sStack);
                }
                else{
                    Pair<S, Saut> currS2 =
                }

            } while(!sStack.isEmpty());*/
        }
        return null;
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        TransitionSystem<Pair<S, Saut>, A, Saut> productTS = product(ts, aut);
        Set<Saut> accepting = aut.getAcceptingStates();
        Set<Pair<S,Saut>> notPhiStates = new HashSet<>();

        for (Pair<S, Saut> currS :
                productTS.getStates()) {
            Stack<Pair<S,Saut>> statesStack = new Stack<>();
            if(accepting.contains(currS.getSecond()) && cycle_check(productTS, currS, statesStack)){
                VerificationFailed<S> ansVer = new VerificationFailed<>();
                ansVer.setPrefix(getPrefList(productTS, currS));
                ansVer.setCycle(getList(statesStack));
                return ansVer;
            }
        }
        return new VerificationSucceeded<S>();
    }
    //////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        Set<Set<LTL<L>>> states = new HashSet<>();
        List<LTL<L>> sub = new LinkedList<>();
        GenerateSub(ltl, sub);
        GenerateStates(sub, states);
        MultiColorAutomaton<Set<LTL<L>>, L> Gnba = generateGnba(states, sub);
        accpetStates(Gnba, getUntil(sub));
        initStates(Gnba, ltl);
        return GNBA2NBA(Gnba);
    }

    private <L> void GenerateSub(LTL<L> ltl, List<LTL<L>> sub) {
        if (ltl instanceof And) {
            GenerateSub(((And<L>) ltl).getLeft(), sub);
            GenerateSub(((And<L>) ltl).getRight(), sub);
            if (!sub.contains(ltl))
                sub.add(ltl);
        } else if (ltl instanceof Until) {
            GenerateSub(((Until<L>) ltl).getLeft(), sub);
            GenerateSub(((Until<L>) ltl).getRight(), sub);
            if (!sub.contains(ltl))
                sub.add(ltl);
        } else if (ltl instanceof Not) {
            GenerateSub(((Not<L>) ltl).getInner(), sub);
        } else if (ltl instanceof Next) {
            GenerateSub(((Next<L>) ltl).getInner(), sub);
            if (!sub.contains(ltl))
                sub.add(ltl);
        } else if (ltl instanceof TRUE || ltl instanceof AP) {

            if (!sub.contains(ltl))
                sub.add(ltl);
        }
    }

    private <L> void GenerateStates(List<LTL<L>> sub, Set<Set<LTL<L>>> states) {
        Set<LTL<L>> trueStates = new HashSet<>();
        if (sub.contains(LTL.true_())) {
            trueStates.add(LTL.true_());
        }
        states.add(trueStates);
        states = getOtherStates(sub, states);

    }

    private <L> Set<Set<LTL<L>>> getOtherStates(List<LTL<L>> sub, Set<Set<LTL<L>>> states) {
        Set<Set<LTL<L>>> other_states = new HashSet<>(states);
        for (LTL<L> ltl : sub) {
            other_states = new HashSet<>(states);
            if (ltl instanceof AP || ltl instanceof Next) {
                for (Set<LTL<L>> os : other_states) {
                    Set<LTL<L>> copy_states = new HashSet<>(os);
                    os.add(ltl);
                    copy_states.add(LTL.not(ltl));
                    states.add(copy_states);
                }
            } else if (ltl instanceof And) {
                for (Set<LTL<L>> os : other_states) {
                    if (os.contains(((And<L>) ltl).getRight()) && os.contains(((And<L>) ltl).getLeft()))
                        os.add(ltl);
                    else
                        os.add(LTL.not(ltl));
                }
            } else if(ltl instanceof  Until){
                for (Set<LTL<L>> os : other_states) {
                    if (os.contains(((Until<L>) ltl).getRight()))
                        os.add(ltl);
                    else if (os.contains(((Until<L>) ltl).getLeft())) {
                        Set<LTL<L>> copy_states = new HashSet<>(os);
                        os.add(ltl);
                        copy_states.add(LTL.not(ltl));
                        states.add(copy_states);
                    } else
                        os.add(LTL.not(ltl));
                }

            }
        }
        return other_states;
    }

    private <L> MultiColorAutomaton<Set<LTL<L>>, L> generateGnba(Set<Set<LTL<L>>> states, List<LTL<L>> sub) {
        MultiColorAutomaton<Set<LTL<L>>, L> auto = new MultiColorAutomaton<>();
        Set<Next<L>> nexts = new HashSet<>();
        Set<Until<L>> untils = new HashSet<>();
        for (LTL<L> ltl : sub) {
            if (ltl instanceof Next)
                nexts.add((Next<L>) ltl);
            else if (ltl instanceof Until)
                untils.add((Until<L>) ltl);
        }
        for (Set<LTL<L>> state : states) {
            for (Set<LTL<L>> inner_states : states) {
                boolean flag = true;
                for (Next<L> nx : nexts) {
                    if (state.contains(nx)) {
                        if (!inner_states.contains(nx.getInner())) {
                            flag = false;
                            break;
                        }
                    } else if (inner_states.contains(nx.getInner())) {
                        flag = false;
                        break;
                    }
                }
                if (flag) {
                    for (Until<L> until : untils) {
                        if (state.contains(until.getRight()) || (state.contains(until.getLeft()) && inner_states.contains(until))) {
                            if (!state.contains(until)) {
                                flag = false;
                                break;
                            }
                        }
                        else if (state.contains(until)) {
                            flag = false;
                            break;
                        }
                    }
                }
                if (flag) {
                    Set<L> ap = new HashSet<>();
                    for (LTL<L> ltl : state) {
                        if (ltl instanceof AP)
                            ap.add(((AP<L>) ltl).getName());
                        auto.addTransition(state, ap, inner_states);
                    }
                }
            }
        }
        return auto;
    }


    private <L> void initStates(MultiColorAutomaton<Set<LTL<L>>, L> aut, LTL<L> ltl) {
        for (Set<LTL<L>> state : aut.getTransitions().keySet()) {
            if (state.contains(ltl))
                aut.setInitial(state);
        }
    }

    private <L> List<LTL<L>> getUntil(List<LTL<L>> sub) {
        List<LTL<L>> untils = new ArrayList<>();
        for (LTL<L> ltl : sub) {
            if (ltl instanceof Until)
                untils.add(ltl);
        }
        return untils;
    }

    private <L> void accpetStates(MultiColorAutomaton<Set<LTL<L>>, L> aut, List<LTL<L>> list_until) {
        for (Set<LTL<L>> state : aut.getTransitions().keySet()) {
            if (list_until.size() != 0) {
                for (LTL<L> until : list_until) {
                    if (!state.contains(until) || state.contains(((Until<L>) until).getRight()))
                        aut.setAccepting(state, list_until.indexOf(until));
                }
            } else
                aut.setAccepting(state, 0);
        }
    }


    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        return sec_GNBA2NBA(mulAut);
    }
    private <L , T>  Automaton<Pair<T, Integer>, L>sec_GNBA2NBA(MultiColorAutomaton<T, L> mulAut){
        Automaton<Pair<T, Integer>, L> auto = new Automaton<>();
        List<Integer> colors = new ArrayList<>(mulAut.getColors());
        for (Integer c : colors) {
            int next = 0;
            if (c != colors.get(colors.size() - 1))
                next = colors.get(colors.indexOf(c) + 1);
            else
                next = colors.get(0);
            for (Map.Entry<T, Map<Set<L>, Set<T>>> state : mulAut.getTransitions().entrySet()) {
                Pair<T, Integer> a = new Pair<>(state.getKey(), c);
                if (colors.indexOf(c) == 0) {
                    if (mulAut.getInitialStates().contains(state.getKey()))
                        auto.setInitial(a);
                    if (mulAut.getAcceptingStates(c).contains(state.getKey()))
                        auto.setAccepting(a);
                }
                for (Map.Entry<Set<L>, Set<T>> act : state.getValue().entrySet()) {
                    for (T inner_state : act.getValue()) {
                        Pair<T, Integer> b = null;
                        if (!mulAut.getAcceptingStates(c).contains(state.getKey()))
                            b = new Pair<>(inner_state, c);
                        else
                            b = new Pair<>(inner_state, next);
                        auto.addTransition(a, act.getKey(), b);
                    }
                }
            }
        }
        return auto;
    }

}


