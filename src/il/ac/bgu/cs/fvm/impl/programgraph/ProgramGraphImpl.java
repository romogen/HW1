package il.ac.bgu.cs.fvm.impl.programgraph;

import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.*;

public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {

    Set<L> locs;
    Set<L> initials;
    Set<List<String>> initializations;
    Set<PGTransition<L, A>> transitions;

    String name;

    // effect map ?

    public ProgramGraphImpl() {
        locs = new HashSet<L>();
        initials = new HashSet<L>();
        initializations = new HashSet<List<String>>();
        transitions = new HashSet<PGTransition<L, A>>();
    }
    @Override
    public void addInitalization(List<String> init) {
        // is init suppose to be checked to contain all variables ? not specified in interface
        initializations.add(init);
    }

    @Override
    public void setInitial(L location, boolean isInitial) {
        if(!locs.contains(location))
            throw new IllegalArgumentException();

        if(isInitial)
            initials.add(location);
        else
            initials.remove(location);
    }

        @Override
    public void addLocation(L l) {
        locs.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        // is transition needs to be checked as valid ? not specified in interface
        transitions.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        HashSet<List<String>> initializationsCopy = new HashSet<List<String>>();
        initializationsCopy.addAll(initializations);
        return initializationsCopy;
    }

    @Override
    public Set<L> getInitialLocations() {
        Set<L> initialsCopy = new HashSet<>();
        initialsCopy.addAll(initials);
        return initialsCopy;
    }

    @Override
    public Set<L> getLocations() {
        Set<L> locsCopy = new HashSet<>();
        locsCopy.addAll(locs);
        return locsCopy;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        Set<PGTransition<L, A>> transitionsCopy = new HashSet<>();
        transitionsCopy.addAll(transitions);
        return transitionsCopy;
    }

    @Override
    public void removeLocation(L l) {
        locs.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        transitions.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }
}
