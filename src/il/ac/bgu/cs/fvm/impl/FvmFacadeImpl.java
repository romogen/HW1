package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.impl.programgraph.ProgramGraphImpl;
import il.ac.bgu.cs.fvm.impl.transitionsystem.TransitionSystemImpl;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import java.io.InputStream;
import java.util.*;

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

        Iterator<Transition<S, A>> transitionIterator = ts.getTransitions().iterator();
        while(transitionIterator.hasNext()){
            Transition<S, A> currTransition = transitionIterator.next();
            Set<P> fromLabel = ts.getLabel(currTransition.getFrom()), toLabel = ts.getLabel(currTransition.getTo());
            fromLabel.retainAll(toLabel);
            if(fromLabel.size() > 1)
                return false;
        }

        return true;
    }

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
            return false;


        S fromState = e.head();
        AlternatingSequence<A, S> remainingSequence = e.tail();
        while(!remainingSequence.isEmpty()){
            A transitionAction = remainingSequence.head();
            S toState = remainingSequence.tail().head();
            remainingSequence = remainingSequence.tail().tail();

            if(!ts.getTransitions().contains(new Transition<S, A>(fromState, transitionAction, toState)))
                return false;

            fromState = toState;
        }

        return true;
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head());
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
                    pg1.getInitalizations()) {
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

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {

    }

    @Override
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement product
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromelaString
    }

    @Override
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement programGraphFromNanoPromela
    }

    @Override
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts, Automaton<Saut, P> aut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement verifyAnOmegaRegularProperty
    }

    @Override
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement LTL2NBA
    }

    @Override
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement GNBA2NBA
    }
   
}
