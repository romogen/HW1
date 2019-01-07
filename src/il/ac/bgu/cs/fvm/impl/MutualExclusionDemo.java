package il.ac.bgu.cs.fvm.impl;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.examples.PetersonProgramGraphBuilder;
import il.ac.bgu.cs.fvm.programgraph.ActionDef;
import il.ac.bgu.cs.fvm.programgraph.ConditionDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;


public class MutualExclusionDemo {

    private static FvmFacade fvm = FvmFacade.createInstance();

    /**
     * auto Rom Ogen and Avishay Kitron
     * In this class we show how can we use in our method to verify mutual exclusion and starvation.
     * we used in one of the test that joined to this project
     */
    //create an instance of our fvm

    public static void main(String[] args) {
        peterson_mutex_and_starvation();
    }


    public static void peterson_mutex_and_starvation() {
        /**
         * In this class we verify mutual exclusion and starvation on peterson algorithm.
         */
        System.out.println("---------------------------Begging of the tests Rom Ogen & Avishay Kitron------------------------");
        //create two program graphs and interleave them.
        ProgramGraph<String, String> pg1 = PetersonProgramGraphBuilder.build(1);
        ProgramGraph<String, String> pg2 = PetersonProgramGraphBuilder.build(2);

        ProgramGraph<Pair<String, String>, String> pg = fvm.interleave(pg1, pg2);

        //check if pg created successfully:
        if(pg == null)
            System.out.println("Error occurred during created program graphs.");
        //create set og actions and conditions.
        Set<ActionDef> ad = set(new ParserBasedActDef());
        Set<ConditionDef> cd = set(new ParserBasedCondDef());

        TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts;
        ts = fvm.transitionSystemFromProgramGraph(pg, ad, cd);
        //check if ts created successfully:
        if(ts == null)
            System.out.println("Error occurred during created transition system.");

        //add labels to transition system
        addLabels(ts);
        System.out.println("labels added successfully.");

        // Test mutual exclusion
        {
            System.out.println("Start testing mutual exclusion");
            Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());
            //create automaton to verify mutual exclusion
            Automaton<String, String> aut = eventuallyPhiAut(a -> a.contains("crit1") && a.contains("crit2") , all);
            //verify the result
            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvm.verifyAnOmegaRegularProperty(ts, aut);
            String ans= vr instanceof VerificationSucceeded ? "succeeded" : "failed\n" + vr.toString();
            System.out.println("The result of verification mutual exclusion is: " + ans);
        }

        // Test a liveness property - that after every state that satisfies
        // wait1 we must eventually have a state that satisfies crit1
        {
            System.out.println("Start testing starvation");
            Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());
            //create automaton to verify starvation
            Automaton<String, String> aut = eventuallyPhi1AndThenAlwaysPhi2Aut(a -> a.contains("wait1"), a -> !a.contains("crit1") , all);
            //verify the result
            VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> vr = fvm.verifyAnOmegaRegularProperty(ts, aut);
            String ans= vr instanceof VerificationSucceeded ? "succeeded" : "failed\n" + vr.toString();
            System.out.println("The result of verification starvation is: " + ans);
        }
        System.out.println("-----------------------The tests are finished--------------------------");


    }

    // Add labels to ts for formulating mutual exclusion properties.
    private static void addLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        ts.getStates().stream().forEach(st -> ts.getAtomicPropositions().stream().forEach(ap -> ts.removeLabel(st, ap)));

        Set<String> aps = new HashSet<>(ts.getAtomicPropositions());
        aps.stream().forEach(ap -> ts.removeAtomicProposition(ap));

        seq("wait1", "wait2", "crit1", "crit2", "crit1_enabled").stream().forEach(s -> ts.addAtomicPropositions(s));

        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1"));
        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "wait1"));

        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2"));
        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "wait2"));

        Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
        ts.getStates().stream().filter(s -> fvm.post(ts, s).stream().anyMatch(_crit1)).forEach(s -> ts.addToLabel(s, "crit1_enabled"));
    }

    // An automaton for Eventually(phi1 /\ Next(Always(not phi2)))
    private static Automaton<String, String> eventuallyPhi1AndThenAlwaysPhi2Aut(Predicate<Set<String>> phi1, Predicate<Set<String>> phi2 , Set<Set<String>> all) {

        Automaton<String, String> aut = new Automaton<>();

        all.stream().forEach(l -> aut.addTransition("q0", l, "q0"));
        all.stream().filter(phi1).forEach(l -> aut.addTransition("q0", l, "q1"));
        all.stream().filter(phi2).forEach(l -> aut.addTransition("q1", l, "q1"));

        aut.setInitial("q0");
        aut.setAccepting("q1");
        return aut;
    }

    // An automaton for Eventually(phi))
    private static Automaton<String, String> eventuallyPhiAut(Predicate<Set<String>> phi , Set<Set<String>> all) {
        Automaton<String, String> aut = new Automaton<>();

        all.stream().filter(phi.negate()).forEach(l -> aut.addTransition("q0", l, "q0"));
        all.stream().filter(phi).forEach(l -> aut.addTransition("q0", l, "q1"));
        all.stream().forEach(l -> aut.addTransition("q1", l, "q1"));

        aut.setInitial("q0");
        aut.setAccepting("q1");
        return aut;
    }


}
