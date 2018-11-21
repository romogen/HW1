package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.automata.MultiColorAutomaton;
import il.ac.bgu.cs.fvm.channelsystem.ChannelSystem;
import il.ac.bgu.cs.fvm.circuits.Circuit;
import il.ac.bgu.cs.fvm.exceptions.StateNotFoundException;
import il.ac.bgu.cs.fvm.impl.transitionsystem.TransitionSystemImpl;
import il.ac.bgu.cs.fvm.ltl.LTL;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
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
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isExecution
    }

    @Override
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isExecutionFragment
    }

    @Override
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isInitialExecutionFragment
    }

    @Override
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement isMaximalExecutionFragment
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
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement createProgramGraph
    }

    @Override
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement interleave
    }

    @Override
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> transitionSystemFromCircuit(Circuit c) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromCircuit
    }

    @Override
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromProgramGraph
    }

    @Override
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(ChannelSystem<L, A> cs) {
        throw new UnsupportedOperationException("Not supported yet."); // TODO: Implement transitionSystemFromChannelSystem
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
