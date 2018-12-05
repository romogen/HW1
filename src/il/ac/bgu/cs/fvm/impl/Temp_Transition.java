package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.fvm.nanopromela.NanoPromelaParser.StmtContext;

import java.util.List;

public class Temp_Transition {

    private List<NanoPromelaParser.StmtContext> source_stmt;
    private List<NanoPromelaParser.StmtContext> dest_stmt;
    private String condition;
    private String action;

    public Temp_Transition(List<StmtContext> source_stmt, List<StmtContext> dest_stmt, String condition, String action) {
        this.source_stmt = source_stmt;
        this.dest_stmt = dest_stmt;
        this.condition = condition;
        this.action = action;
    }

    public List<StmtContext> getSource_stmt() {
        return source_stmt;
    }

    public void setSource_stmt(List<StmtContext> source_stmt) {
        this.source_stmt = source_stmt;
    }

    public List<StmtContext> getDest_stmt() {
        return dest_stmt;
    }

    public void setDest_stmt(List<StmtContext> dest_stmt) {
        this.dest_stmt = dest_stmt;
    }

    public String getCondition() {
        return condition;
    }

    public void setCondition(String condition) {
        this.condition = condition;
    }

    public String getAction() {
        return action;
    }

    public void setAction(String action) {
        this.action = action;
    }
}
