package il.ac.bgu.cs.fvm.impl.transitionsystem;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.*;

public class TransitionSystemImpl<STATE,ACTION,ATOMIC_PROPOSITION> implements TransitionSystem<STATE,ACTION,ATOMIC_PROPOSITION>{

    private String name;

    private Set<ACTION> actions;
    private Set<STATE> states;
    private Set<ATOMIC_PROPOSITION> aps;
    private Set<Transition<STATE, ACTION>> transitions;
    private Map<STATE, Set<ATOMIC_PROPOSITION>> labels;

    private Set<STATE> initials;

    public TransitionSystemImpl(){
        name = null;

        actions = new HashSet<ACTION>();
        states = new HashSet<STATE>();
        aps = new HashSet<ATOMIC_PROPOSITION>();
        transitions = new HashSet<Transition<STATE, ACTION>>();
        labels = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();

        initials = new HashSet<STATE>();
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(ACTION anAction) {
        actions.add(anAction);
    }

    @Override
    public void setInitial(STATE aState, boolean isInitial) throws StateNotFoundException {
        if(!states.contains(aState))
            throw new StateNotFoundException(aState);

        if(isInitial)
            initials.add(aState);
        else if(initials.contains(aState))
            initials.remove(aState);
    }

    @Override
    public void addState(STATE state) {
        states.add(state);
        labels.put(state, new HashSet<ATOMIC_PROPOSITION>());
    }

    @Override
    public void addTransition(Transition<STATE, ACTION> t) throws FVMException {
        if(!states.contains(t.getFrom()) || !states.contains(t.getTo()))
            throw new InvalidTransitionException(t);
        if(!actions.contains(t.getAction()))
            throw new InvalidTransitionException(t);
        transitions.add(t);
    }

    @Override
    public Set<ACTION> getActions() {
        Set<ACTION> actionsCopy = new HashSet<ACTION>();
        actionsCopy.addAll(actions);
        return actionsCopy;
    }

    @Override
    public void addAtomicProposition(ATOMIC_PROPOSITION p) {
        aps.add(p);
    }

    @Override
    public Set<ATOMIC_PROPOSITION> getAtomicPropositions() {
        Set<ATOMIC_PROPOSITION> apsCopy = new HashSet<ATOMIC_PROPOSITION>();
        apsCopy.addAll(aps);
        return apsCopy;
    }

    @Override
    public void addToLabel(STATE s, ATOMIC_PROPOSITION l) throws FVMException {
        if(!states.contains(s) || !aps.contains(l))
            throw new InvalidLablingPairException(s, l);

        labels.get(s).add(l);

    }

    @Override
    public Set<ATOMIC_PROPOSITION> getLabel(STATE s) {
        if(!states.contains(s))
            throw new StateNotFoundException(s);

        Set<ATOMIC_PROPOSITION> labelCopy = new HashSet<ATOMIC_PROPOSITION>();
        labelCopy.addAll(labels.get(s));
        return labelCopy;
    }

    @Override
    public Set<STATE> getInitialStates() {
        Set<STATE> initialCopy = new HashSet<STATE>();
        initialCopy.addAll(initials);
        return initialCopy;
    }

    @Override
    public Map<STATE, Set<ATOMIC_PROPOSITION>> getLabelingFunction() {
        Map<STATE, Set<ATOMIC_PROPOSITION>> labelsCopy = new HashMap<STATE, Set<ATOMIC_PROPOSITION>>();

        Iterator<STATE> statesIterator = states.iterator();
        while(statesIterator.hasNext()){
            STATE currState = statesIterator.next();
            Set<ATOMIC_PROPOSITION> stateLabels = labels.get(currState);

            Set<ATOMIC_PROPOSITION> stateLabelsCopy = new HashSet<ATOMIC_PROPOSITION>();
            stateLabelsCopy.addAll(stateLabels);

            labelsCopy.put(currState, stateLabelsCopy);
        }

        return labelsCopy;
    }

    @Override
    public Set<STATE> getStates() {
        Set<STATE> statesCopy = new HashSet<STATE>();
        statesCopy.addAll(states);
        return statesCopy;
    }

    @Override
    public Set<Transition<STATE, ACTION>> getTransitions() {
        Set<Transition<STATE, ACTION>> transitionsCopy = new HashSet<Transition<STATE, ACTION>>();
        transitionsCopy.addAll(transitions);
        return transitionsCopy;
    }

    @Override
    public void removeAction(ACTION action) throws FVMException {
        Iterator<Transition<STATE, ACTION>> transitionIterator = transitions.iterator();
        while(transitionIterator.hasNext())
            if(transitionIterator.next().getAction().equals(action))
                throw new DeletionOfAttachedActionException(action, TransitionSystemPart.TRANSITIONS);

        actions.remove(action);
    }

    @Override
    public void removeAtomicProposition(ATOMIC_PROPOSITION p) throws FVMException {
        Iterator<STATE> stateIterator = states.iterator();
        while(stateIterator.hasNext()){
            if(labels.get(stateIterator.next()).contains(p))
                throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.LABELING_FUNCTION);
        }

        aps.remove(p);
    }

    @Override
    public void removeLabel(STATE s, ATOMIC_PROPOSITION l) {
        if(!states.contains(s))
            return;
        labels.get(s).remove(l);
    }

    @Override
    public void removeState(STATE state) throws FVMException {
        if(!states.contains(state))
            return;

        Iterator<Transition<STATE, ACTION>> transitionIterator = transitions.iterator();
        while(transitionIterator.hasNext()){
            Transition<STATE, ACTION> currTransition = transitionIterator.next();
            if(currTransition.getFrom().equals(state) || currTransition.getTo().equals(state))
                throw new DeletionOfAttachedStateException(state, TransitionSystemPart.TRANSITIONS);
        }

        if(!labels.get(state).isEmpty())
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.LABELING_FUNCTION);

        if(initials.contains(state))
            throw new DeletionOfAttachedStateException(state, TransitionSystemPart.INITIAL_STATES);

        states.remove(state);
    }

    @Override
    public void removeTransition(Transition<STATE, ACTION> t) {
        transitions.remove(t);
    }

//    /**
//     * Creates a new transition system.
//     *
//     * @param s State to add label to.
//     * @param ap the ATOMIC_PROPOSITION to add to s labels.
//     */
//    private void addAPToExistingLabel(STATE s, ATOMIC_PROPOSITION ap){
//        Set<ATOMIC_PROPOSITION> currLabel = labels.get(s);
//        currLabel.add(ap);
//    }
}
