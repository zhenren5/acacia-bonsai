#pragma once
#include <memory>
#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>
#include <algorithm>

#include <signal.h>
#include <sys/wait.h>

#include "common_aoutput.hh"
#include "common_finput.hh"
#include "common_setup.hh"
#include "common_sys.hh"

#include <boost/algorithm/string.hpp>

#include <spot/twa/formula2bdd.hh>
#include <spot/misc/bddlt.hh>
#include <spot/misc/escape.hh>
#include <spot/misc/timer.hh>
#include <spot/tl/formula.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/aiger.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/parity.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/totgba.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/twaalgos/split.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twa/bdddict.hh>

const unsigned int NULL_VALUE = std::numeric_limits<unsigned>::max();

std::string join(std::vector<std::string> const &strings, std::string delim)
{
    if (strings.empty())
    {
        return std::string();
    }
    return std::accumulate(strings.begin() + 1, strings.end(), strings[0],
                           [&delim](std::string x, std::string y)
                           {
                               return x + delim + y;
                           });
}

void transform_ucb(spot::twa_graph_ptr &aut)
{
    unsigned new_ini = aut->num_states();
    unsigned old_ini = aut->get_init_state_number();
    aut->new_state();
    for (auto &e : aut->out(old_ini))
    {
        aut->new_edge(new_ini, e.dst, e.cond, e.acc);
    }
    aut->set_init_state(new_ini);
}
/*
      given a trace and a set of inputs or outputs separeted by comma ',',
      split it and push each input or output in the vector trace
      */
void example_parse(std::vector<std::vector<std::string>> &trace, std::string &ios)
{
    size_t pos = 0;
    std::vector<std::string> io;
    std::string token;
    while ((pos = ios.find(',')) != std::string::npos)
    {
        token = ios.substr(0, pos);
        token.erase(remove_if(token.begin(), token.end(), isspace), token.end());
        io.push_back(token);
        ios.erase(0, pos + 1);
    }
    ios.erase(remove_if(ios.begin(), ios.end(), isspace), ios.end());
    io.push_back(ios);
    trace.push_back(io);
}

void get_trace(std::vector<std::vector<std::string>> &trace, const std::string &example, std::vector<std::vector<std::string>> *infinite_trace = NULL)
{
    std::string move;
    std::stringstream ex(example);
    bool infinite = false;
    while (std::getline(ex, move, '#'))
    { // for pair {inputs}{ouputs}
        if (move[0] == '*')
        {
            infinite = true;
        }
        unsigned input_begin = move.find('{');
        unsigned input_end = move.find('}');
        std::string strNew = move.substr(input_begin + 1, input_end - input_begin - 1);
        if (infinite)
        {
            if (!infinite_trace)
            {
                std::cout << "the trace format is wrong" << std::endl;
                exit(-1);
            }
            example_parse(*infinite_trace, strNew);
        }
        else
            example_parse(trace, strNew);
        strNew = move.substr(input_end + 2, move.length() - input_end - 3);
        if (infinite && infinite_trace)
            example_parse(*infinite_trace, strNew);
        else
            example_parse(trace, strNew);
    }
}

void conjuction_examples(spot::formula &f, std::vector<std::string> &negative_aps_)
{
    std::vector<std::vector<std::string>> trace;
    for (const std::string &example : negative_aps_)
    {
        trace.clear();
        get_trace(trace, example);
        std::string formula_str = "";
        for (unsigned int i = 0; i < trace.size() - 1; i++)
        { // the last is different
            if (i % 2 == 0)
            {
                formula_str += "(";
                formula_str += std::string(i / 2, 'X'); // add NEXT operator
                formula_str += "(";
            }
            else
            {
                formula_str += " & ";
            }
            formula_str += join(trace[i], " & ");
            if (i == trace.size() - 2)
            {
                formula_str += "))";
            }
            else if (i % 2 != 0)
            {
                formula_str += ")) & ";
            }
        }
        formula_str = "(" + formula_str + ") -> "+std::string((trace.size() - 1) / 2, 'X')+"!("  + join(trace[trace.size() - 1], " & ") + ")";
        spot::formula formula = spot::parse_formula(formula_str);
        std::cout << "before formula: " << formula << '\n';
        std::cout << "f: " << f << '\n';
        f = spot::formula::And(std::vector<spot::formula>{f, formula});
        std::cout << "after formula: " << f << '\n';
    }
}

unsigned add_edge(spot::twa_graph_ptr &aut, unsigned root, bdd exist_cond, unsigned dest = NULL_VALUE)
{
    bool exist = false;
    for (auto &e : aut->out(root))
    { // avoid repetition prefix
        if (e.cond == exist_cond && dest == NULL_VALUE)
        {
            root = e.dst;
            exist = true;
            break;
        }
    }
    if (!exist || dest != NULL_VALUE) // if destination is specified we go to the dest
    {
        if (dest == NULL_VALUE)
            dest = aut->new_state();

        aut->new_edge(root, dest, exist_cond);
        root = dest;
    }
    return root;
}

bdd conjunction(spot::twa_graph_ptr &aut, std::vector<std::string> io)
{
    bdd res = bddtrue;
    bdd b;
    for (unsigned int j = 0; j < io.size(); j++)
    {
        spot::formula formula = spot::parse_formula(io[j]);
        b = formula_to_bdd(formula, aut->get_dict(), aut);
        res = res & b;
    }
    return res;
}

// trace=[[i1,i2,...],[o1,o2,o3,...],[i,...],[o,....]]
unsigned add_branch(spot::twa_graph_ptr &aut, unsigned init, std::vector<std::vector<std::string>> &trace, bool negative = true, bool loop = false)
{
    unsigned sink;
    if (!negative)
    {
        // sink state
        sink = aut->new_state();
        aut->new_acc_edge(sink, sink, bddtrue);
    }

    unsigned root = init;
    bool exist = false;
    bdd res;
    bool init_loop = false;
    bdd add_bdd;
    bdd add_sink;
    bdd sink_bdd;

    // unsigned end = loop ? trace.size() - 3:trace.size() - 1; //loop trace will end one state before to loop back
    for (int i = 0; i < trace.size(); i += 2)
    {
        std::cout << trace.size() << std::endl;
        std::vector<std::string> in = trace[i];
        std::vector<std::string> out = trace[i + 1];

        bdd in_cond = conjunction(aut, in);
        bdd out_cond = conjunction(aut, out);
        res = in_cond & out_cond;

        bdd diff_out_cond = !out_cond;
        if (!negative)
        { // in no negative examples we need to reject unwilling pathes
            // if same condition but different out
            sink_bdd = in_cond & diff_out_cond;
            add_edge(aut, root, in_cond & diff_out_cond, sink);
        }
        if (init == aut->get_init_state_number())
        { // if
            // Do not add loop on init state because it can make the trace incorrect
            // so we add an additional input/output path
            if (i == 0)
            {
                init_loop = true;
                add_bdd = res;
                add_sink = sink_bdd;
            }
            else if (i == 2)
            { // loop on the second state
                init = root;
            }
        }
        // follow the example trace
        if (loop && i == trace.size() - 2)
        { // if we're on the last state of the loop we go back to the starting state
            if (init_loop)
            { // if we want to create a loop on initial state
                // it's forbidden because it can make the trace incorrect so we add an additional input/output path
                unsigned new_state = aut->new_state();
                root = add_edge(aut, root, res, new_state);
                res = add_bdd;
                add_edge(aut, root, add_sink, sink);
                init = i == 0 ? root : init;
            }

            add_edge(aut, root, res, init);
            std::cout << "add edge to loop" << res << " to iinit" << sink << std::endl;
        }
        else
        {
            unsigned dst = loop ? aut->new_state() : NULL_VALUE;
            root = add_edge(aut, root, res, dst);
            std::cout << "add edge normal" << res << std::endl;
        }
    }
    if (negative) // last state will loop on itself
        aut->new_acc_edge(root, root, bddtrue);

    return root;
}

void add_negative_branches(spot::twa_graph_ptr &aut, std::vector<std::string> &negative_aps_)
{
    std::vector<std::vector<std::string>> trace;
    unsigned ini = aut->get_init_state_number();
    for (const std::string &example : negative_aps_)
    {
        // std::stringstream ex(example);
        trace.clear();
        get_trace(trace, example);
        add_branch(aut, ini, trace);
    }
}
void print_trace(const std::vector<std::vector<std::string>> &trace)
{
    for (auto &vec : trace)
    {
        for (auto &str : vec)
        {
            std::cout << str << " ";
        }
        std::cout << std::endl;
    }
}

// infinite trace: {ui}{uo}#*{vi}{vo}

void add_infinite_traces(spot::twa_graph_ptr &aut, std::vector<std::string> &infinite_aps_)
{
    std::vector<std::vector<std::string>> trace;
    std::vector<std::vector<std::string>> infinite_trace;
    unsigned ini;
    for (const std::string &example : infinite_aps_)
    {
        // std::stringstream ex(example);
        trace.clear();
        infinite_trace.clear();
        ini = aut->get_init_state_number();
        get_trace(trace, example, &infinite_trace);

        ini = add_branch(aut, ini, trace, false, false);
        add_branch(aut, ini, infinite_trace, false, true);
    }
}
