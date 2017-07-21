
/******************************************
Copyright (c) 2014, Tomas Balyo, Karlsruhe Institute of Technology.
Copyright (c) 2014, Armin Biere, Johannes Kepler University.
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
***********************************************/

/**
 * Return the name and the version of the incremental SAT
 * solving library.
 */

#include "Solver.h"
#include "SolverTypes.h"
#include <vector>
#include <complex>
#include <cassert>
#include <iostream>

#if defined _WIN32
    #define DLL_PUBLIC __declspec(dllexport)
#else
    #define DLL_PUBLIC __attribute__ ((visibility ("default")))
    #define DLL_LOCAL  __attribute__ ((visibility ("hidden")))
#endif

using std::vector;

using namespace Minisat;
using namespace std;

struct MySolver {
    ~MySolver()
    {
        delete solver;
    }

    MySolver()
    {
        solver = new Solver;
    }

    vec<Lit> clause;
    vec<Lit> assumptions;
    Solver* solver;
};

extern "C" {

DLL_PUBLIC const char * ipasir_signature ()
{
    return "MiniCARD 1.2, based on MiniSAT 2.2.0";
}

/**
 * Construct a new solver and return a pointer to it.
 * Use the returned pointer as the first parameter in each
 * of the following functions.
 *
 * Required state: N/A
 * State after: INPUT
 */
DLL_PUBLIC void * ipasir_init ()
{
    MySolver *s = new MySolver;
    printf("Pointer in C: %p\n",  s);
    return (void*)s;
}

/**
 * Release the solver, i.e., all its resoruces and
 * allocated memory (destructor). The solver pointer
 * cannot be used for any purposes after this call.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: undefined
 */
DLL_PUBLIC void ipasir_release (void * solver)
{
    MySolver* s = (MySolver*)solver;
    delete s;
}

/**
 * Add the given literal into the currently added clause
 * or finalize the clause with a 0.  Clauses added this way
 * cannot be removed. The addition of removable clauses
 * can be simulated using activation literals and assumptions.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 *
 * Literals are encoded as (non-zero) integers as in the
 * DIMACS formats.  They have to be smaller or equal to
 * INT_MAX and strictly larger than INT_MIN (to avoid
 * negation overflow).  This applies to all the literal
 * arguments in API functions.
 */
DLL_PUBLIC void ipasir_add (void * solver, int lit_or_zero)
{
    printf("ES GEHT LOS!! %d\n", lit_or_zero);
    MySolver* s = (MySolver*)solver;
    printf("Stelle w %d\n", s->solver->okay());

    if (lit_or_zero == 0) {
        printf("AddingClause: ");
        for( int i = 0; i < s->clause.size(); i++)
            cout << toString(s->clause[i]) << " = " << s->solver->value(s->clause[i]).toString() << endl;
        printf("\n");
        printf("Stelle s %d\n", s->solver->okay());

        s->solver->addClause(s->clause);
        printf("clause added: \n");
        for( int i = 0; i < s->clause.size(); i++)
            cout << toString(s->clause[i]) << " = " << s->solver->value(s->clause[i]).toString() << endl;
        printf("Stelle t %d\n", s->solver->okay());
        s->clause.clear();
    } else {
        while (std::abs(lit_or_zero) > s->solver->nVars()) {
            s->solver->newVar();
            cout << "newVar" << s->solver->value(s->solver->nVars()-1).toString() << endl;
        }
        Lit lit = mkLit(std::abs(lit_or_zero)-1, lit_or_zero < 0);
        cout << "created " << toString(lit) << " = " << s->solver->value(lit).toString() << endl;
       	/*
	if (lit.x >= s->solver->nVars()) {
            const uint32_t toadd = lit.x - s->solver->nVars() + 1;
            s->solver->new_vars(toadd);
        }
	*/
        s->clause.push(lit);
    }
    printf("Stelle x %d\n", s->solver->okay());
}

/**
 * Add an assumption for the next SAT search (the next call
 * of ipasir_solve). After calling ipasir_solve all the
 * previously added assumptions are cleared.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT
 */
DLL_PUBLIC void ipasir_assume (void * solver, int lit)
{
    MySolver* s = (MySolver*)solver;
    Lit lit_cms = mkLit(std::abs(lit)-1, lit < 0);
    s->assumptions.push(lit_cms);
}

/**
 * Solve the formula with specified clauses under the specified assumptions.
 * If the formula is satisfiable the function returns 10 and the state of the solver is changed to SAT.
 * If the formula is unsatisfiable the function returns 20 and the state of the solver is changed to UNSAT.
 * If the search is interrupted (see ipasir_set_terminate) the function returns 0 and the state of the solver remains INPUT.
 * This function can be called in any defined state of the solver.
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
DLL_PUBLIC int ipasir_solve (void * solver)
{
    MySolver* s = (MySolver*)solver;
    printf("Stelle y %d\n", s->solver->okay() );
    if(!s->solver->simplify()){
        printf("Not simple\n");
        return 20;
    }
    lbool ret = s->solver->solveLimited(s->assumptions);
    s->assumptions.clear();

    printf("Anzahl: %d\n", s->solver->nVars());
    for (int i = 0; i < s->solver->nVars(); i++) {
        if (s->solver->model[i] != l_Undef)
            printf("%s%s%d", (i==0)?"":" ", (s->solver->model[i]==l_True)?"":"-", i+1);
    }
    printf("\n");

    if (ret == l_True) {
        return 10;
    }
    else if (ret == l_False) {
        return 20;
    }
    else {
        return 0;
    }
}

/**
 * Get the truth value of the given literal in the found satisfying
 * assignment. Return 'lit' if True, '-lit' if False, and 0 if not important.
 * This function can only be used if ipasir_solve has returned 10
 * and no 'ipasir_add' nor 'ipasir_assume' has been called
 * since then, i.e., the state of the solver is SAT.
 *
 * Required state: SAT
 * State after: SAT
 */
DLL_PUBLIC int ipasir_val (void * solver, int lit)
{
    MySolver* s = (MySolver*)solver;

    const int a = std::abs(lit)-1;
    const bool flip = lit < 0;

    return (s->solver->model[a] == l_True) ^ flip;
}

/**
 * Check if the given assumption literal was used to prove the
 * unsatisfiability of the formula under the assumptions
 * used for the last SAT search. Return 1 if so, 0 otherwise.
 * This function can only be used if ipasir_solve has returned 20 and
 * no ipasir_add or ipasir_assume has been called since then, i.e.,
 * the state of the solver is UNSAT.
 *
 * Required state: UNSAT
 * State after: UNSAT
 */
DLL_PUBLIC int ipasir_failed (void * solver, int lit)
{
    MySolver* s = (MySolver*)solver;
    const vec<Lit>& confl = s->solver->conflict;
    const Lit tofind = mkLit(std::abs(lit)-1, lit < 0);

    for( int i = 0; i < confl.size(); i++) {
	Lit lit = confl[i];
        if (lit == tofind) {
            return true;
        }
    }
    return false;
}

/**
 * Set a callback function used to indicate a termination requirement to the
 * solver. The solver will periodically call this function and check its return
 * value during the search. The ipasir_set_terminate function can be called in any
 * state of the solver, the state remains unchanged after the call.
 * The callback function is of the form "int terminate(void * state)"
 *   - it returns a non-zero value if the solver should terminate.
 *   - the solver calls the callback function with the parameter "state"
 *     having the value passed in the ipasir_set_terminate function (2nd parameter).
 *
 * Required state: INPUT or SAT or UNSAT
 * State after: INPUT or SAT or UNSAT
 */
DLL_PUBLIC void ipasir_set_terminate (void * /*solver*/, void * /*state*/, int (*terminate)(void * state))
{
    //this is complicated.
}

}

DLL_PUBLIC void ipasir_set_learn (void * solver, void * state, int max_length, void (*learn)(void * state, int * clause))
{
    //this is complicated
}
