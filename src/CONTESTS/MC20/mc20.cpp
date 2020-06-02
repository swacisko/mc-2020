//
// Created by sylwester on 5/19/20.
//

#include <datastructures/InfInt.h>
#include <graphs/treewidth/TreewidthDP.h>
#include "CONTESTS/MC20/mc20.h"
#include "graphs/components/ConnectedComponents.h"
#include "graphs/GraphInducer.h"
#include "graphs/treewidth/pace.h"
#include "graphs/treewidth/TreewidthDecomposition.h"
#include "graphs/GraphUtils.h"
#include "combinatorics/GrayCode.h"

typedef InfInt big_integer;

string to_string(big_integer g){ return g.toString(); }

namespace MC20{

    // CAUTION! variables are numbered from 1  to vars, but graph is of size vars, not vars+1. REMEMBER TO ADD/SUBTRACT 1 !!

    vector< unordered_set<int> > clauses; // clauses[i] is the set of variables (e.g. {4, -6} )
    vector< unordered_set<int> > inClauses; // inClauses[i] is a set of clauses that contain variable i (perhaps begated)
    vector< vector< pair<int,int> > > inClausesSign; // inClausesSign[i] is a vector of pairs (clause, sign_of_i_in_that_clause)


    int cls; // number of clauses
    int vars; // number of variables
    big_integer result;



    bool falsifiesClause(VI &ass, int c) {
        const bool debug = false;

        if (debug) cerr << "checking falsifiablity of a clause " << clauses[c] << endl;

        int falsy = 0;
        for (int v : clauses[c]) {
            if (v > 0 && ass[v] == 1) return false;
            else if (v < 0 && ass[-v] == 0) return false;
            else if (ass[abs(v)] != -1) falsy++;
        }


        return falsy == clauses[c].size(); // if all literals are falsy, then clause is falsified
    }

    bool falsifiesAnyClause(VI &ass, VI &cls) {
        for (int c : cls) {
            if (falsifiesClause(ass, c)) return true;
        }
        return false;
    }

    big_integer bruteForce() {
        const bool debug = false;
        big_integer res = 0;

        VI cl(cls);
        iota(ALL(cl), 0);
        VI ass(vars + 1, -1);
        for (LL i = 0; i < (1ll << vars); i++) {
            for (LL j = 0; j < vars; j++) {
                if ((i & (1ll << j)) != 0) ass[j + 1] = 1;
                else ass[j + 1] = 0;
            }

            if (falsifiesAnyClause(ass, cl) == false) res++;

        }

        return res;
    }

    void read() {
        string s;
        inClauses.clear();
        inClausesSign.clear();
        clauses.clear();
//        V.clear();
//        comps.clear();
        int lineNumber = 0;
        int clausesRead = 0;

        while (true) {
            getline(cin, s);

//            DEBUG(s);

            if (s[0] == 'c') {}
            else if (s[0] == 'p') {
//                s = s.substr( 4,s.size()-4 );
                stringstream str(s);
                string nothingBox;
                str >> nothingBox >> nothingBox >> vars >> cls;

                inClauses = vector<unordered_set<int> >(vars + 1);

//                DEBUG(cls);
//                DEBUG(vars);

            } else {
                stringstream str(s);
                int a;
                clauses.push_back(unordered_set<int>());

                while (str >> a) {
//                    DEBUG(a);
                    if (a == 0) break;
                    else {
                        clauses.back().insert(a);
                        inClauses[abs(a)].insert((int) clauses.size() - 1);
                    }
                }

                clausesRead++;
                if (clausesRead == cls) return;
            }
        }


    }


    class Primal {
    public:
        Primal( vector< unordered_set<int> >& clauses, vector< unordered_set<int> >& inClauses, int cls, int vars ){
            this->clauses = clauses;
            this->inClauses = inClauses;
            varSetValue = VB(vars + 1, false);
            this->vars = vars;
            this->cls = cls;
            result = 1;
        }
        VVI V; // primal graph
        VVI comps;
        vector< unordered_set<int> > clauses; // clauses[i] is the set of variables (e.g. {4, -6} )
        vector< unordered_set<int> > inClauses; // inClauses[i] is a set of clauses that contain variable i (perhaps begated)
        vector< vector< pair<int,int> > > inClausesSign; // inClausesSign[i] is a vector of pairs (clause, sign_of_i_in_that_clause)

        VB varSetValue;

        int cls; // number of clauses
        int vars; // number of variables
        big_integer result;

        void preprocess(){
            bool changesDone = true;
            while(changesDone){
                if(result == 0) break;

                changesDone = false;

                for( int i=0; i<cls; i++ ) { // this needs to be done just once, not in every iteration

                    { // test new try
                        for (int d : clauses[i]) {
                            if (clauses[i].count(-d)) {
//                                cerr << "Clearing clause " << i << ": " << clauses[i] << " due to variables : " << d << " and " << -d << endl;
                                for( int d : clauses[i] ) inClauses[ abs(d) ].erase(i);
                                clauses[i].clear();
                                break;
                            }
                        }
                    }
                }

                for( int i=0; i<cls; i++ ){

                    if(result == 0) break;

                    unordered_set<PII, pairhash> clausesToClear;

                    if( clauses[i].size() == 1 ){
                        int d = abs(*clauses[i].begin());
                        bool assSign = ( *clauses[i].begin() > 0 );

                        VI temp( ALL(inClauses[d]) );
                        for( int c : temp ){
                            if( clauses[c].count( d * ( assSign ? 1 : -1 ) )  ){
                                clausesToClear.insert( PII(c,d) );
                                varSetValue[d] = true;
                            }else{
                                if( clauses[c].count( d * (assSign ? -1 : 1) ) && clauses[c].size() == 1 ){
                                    cerr << "nullifying result" << endl;
                                    result = 0;
                                    return;
                                }

                                clauses[c].erase( d * ( assSign ? -1 : 1 ) ); // removing -d from that clause if possible, since it assigns false
                                inClauses[d].erase(c);
                            }
                        }

                    }

                    if( !clausesToClear.empty() ){

                        changesDone = true;
                        for(PII c : clausesToClear){
                            for( int x : clauses[c.first] ){
                                inClauses[ abs(x) ].erase(c.first);
                            }
                            clauses[c.first].clear();
                            inClauses[c.second].erase(c.first);
                        }

                    }


                }

            }

            int power = 0;
            for( int i=1;i<=vars;i++ ) if( inClauses[i].empty() && varSetValue[i] == false ) power++;
            if( power > 0 ) result *= StandardUtils::binaryPower( big_integer(2), power );

            if( result == 0 ) return;

            inClausesSign = vector<vector<pair<int, int> > >(vars + 1);
            for (int i = 1; i < vars + 1; i++) {
                for (int c : inClauses[i]) {
                    if (clauses[c].count(i) > 0 && clauses[c].count(-i) == 0) inClausesSign[i].push_back({c, 1});
                    else if (clauses[c].count(i) == 0 && clauses[c].count(-i) > 0) inClausesSign[i].push_back({c, 0});
                    else if (clauses[c].count(i) > 0 && clauses[c].count(-i) > 0) inClausesSign[i].push_back({c, -1});
                }
            }

        }

        void createGraph() {
            const bool debug = false;
            if (debug) {
                DEBUG(clauses);
                DEBUG(inClauses);
            }


            if (debug) { // testing
                for (int i = 0; i < cls; i++) {
                    if (clauses[i].size() == 2) {
                        VI cl(ALL(clauses[i]));
                        if (cl[0] == -cl[1]) {
                            cerr << "found useless clause " << clauses[i] << endl;
                        }
                    }
                }

                for (int i = 0; i < cls; i++) {
                    if (clauses[i].size() == 1) {
                        int soloVar = *clauses[i].begin();
                        soloVar = abs(soloVar);
                        if (inClauses[soloVar].size() > 1) {
                            cerr << "found solo variable " << soloVar << " in clause " << clauses[i]
                                 << " that appears in clauses:" << endl;
                            for (int d : inClauses[soloVar]) cerr << "\t" << clauses[d] << endl;
                        }
                    }
                }
            }


            V = VVI(vars);

            for (int i = 0; i < cls; i++) {
                for (int a : clauses[i]) {
                    for (int b : clauses[i]) {
                        a = abs(a);
                        b = abs(b);
                        if (a > b) {
                            V[a - 1].push_back(b - 1);
                            V[b - 1].push_back(a - 1);
                        }
                    }
                }
            }


            for (VI &v : V) {
                sort(ALL(v));
                v.resize(unique(ALL(v)) - v.begin());
            }

            if (debug) {
                DEBUG(V);
                cerr << "clauses:" << endl;
                for (int i = 0; i < cls; i++) DEBUG(clauses[i]);
                cerr << "inClauses:" << endl;
                for (int i = 0; i < vars + 1; i++) DEBUG(inClauses[i]);
            }

            comps = ConnectedComponents::getConnectedComponents(V);
            if (debug)DEBUG(comps);
            for (int i = (int) comps.size() - 1; i >= 0; i--) {
                if (comps[i].size() == 1) {
                    int isolated = comps[i][0] + 1;
                    swap(comps[i], comps.back());
                    comps.pop_back();
                }
            }
            if (debug) {
                DEBUG(comps);
                DEBUG(clauses);
                DEBUG(inClauses);
            }
        }

        big_integer getBranchedResultForComponent( InducedGraph& g, TreewidthDecomposition& decomp, int depth ){
            const bool debug = false;

            VVI tree = decomp.getStructure();
            VVI bags = decomp.getBags();
            for( VI& b : bags ) for(int& d : b) d = 1 + g.nodes[d];

            if(debug){
                DEBUG(bags.size());

            }

            VI branchingNodes;

            VVI inBags(vars + 1);

            for (int i = 0; i < bags.size(); i++){
                for (int b : bags[i]) inBags[b].push_back(i);
            }

            VI squares(vars+1,0);

            {// squares of bags sizes

                for (int i = 0; i < inBags.size(); i++) for (int b : inBags[i]) squares[i] += bags[b].size() *
                                                                                              bags[b].size();
                auto comp = [&squares](int a, int b) {
                    if (squares[a] != squares[b]) return squares[a] > squares[b];
                    else return a < b;
                };
                set<int, decltype(comp)> presVars(comp);
                for (int i = 0; i < bags.size(); i++) {
                    presVars.insert(ALL(bags[i]));
                }

                for (int i = 0; i < depth; i++) {
                    branchingNodes.push_back(*presVars.begin());
                    presVars.erase(presVars.begin());

                    int b = branchingNodes.back();
                    if (debug) {
                        cerr << "Adding to branching nodes node " << b << " that has sum of bags-size-square equals "
                             << squares[b] << endl << "\tand occurs in bags of sizes: ";
                        for (auto B : inBags[b]) cerr << bags[B].size() << " ";
                        cerr << endl;

                        for( auto c : inClauses[b] ) cerr << "\t" << clauses[c] << endl;
                        cerr << endl;
                    }
                }

            }



            if(debug){
                DEBUG(branchingNodes);
            }

            auto gClauses = clauses; gClauses.clear();
            vector< unordered_set<int> > gInClauses(vars+1);

            {
                unordered_set<int> allClauses;
                unordered_set<int> allVars;
                for( int v : g.nodes ){
                    allClauses.insert( ALL(inClauses[v+1]) );
                    assert( !inClauses[v+1].empty() );
                }

                if(debug){
                    DEBUG(allClauses.size());
                    DEBUG(g.nodes.size());
                }

                for( int c : allClauses ){
                    gClauses.push_back( clauses[c] );
                    for( int d : clauses[c] ){
                        gInClauses[ abs(d) ].insert( (int)gClauses.size()-1 );
                        allVars.insert( abs(d) );
                    }
                }

                assert( GraphUtils::isConnected( g.V ) );

                if(allVars.size() != g.nodes.size()){
                    DEBUG(allVars.size());
                    DEBUG(g.nodes.size());
                    assert( allVars.size() == g.nodes.size() );
                }

                if(debug){
                    DEBUG(gClauses.size());
                    DEBUG(gInClauses.size());
                }
            }


            big_integer res = 0;
            for( int A = 0; A < (1<<depth); A++ ){

                // now copy initial state

                VB sat( depth,false );
                for( int i=0; (1<<i) <= A; i++ ){
                    if( A & (1<<i) ){
                        sat[i] = true;
                    }
                }

                auto newClauses = gClauses;
                auto newInClauses = gInClauses;
                for( int i=0; i<depth; i++ ){
                    newClauses.push_back( { sat[i] ? branchingNodes[i] : -branchingNodes[i] } );
                    newInClauses[ branchingNodes[i] ].insert( (int)newClauses.size()-1 );
                }

                if(debug){
                    ENDL(2);
                    cerr << "Starting new Primal, A = " << A << " / " << (1<<depth) << endl;
                }


                Primal prim( newClauses, newInClauses, newClauses.size(), vars );
                prim.preprocess();
                prim.createGraph();

                {
                    DEBUG(prim.V.size());
                    {
                        auto cmpgv = prim.comps;
                        cerr << endl << "sizes (>2) of comps of prim.V: "; for(auto c : cmpgv) if(c.size() > 2) cerr << c.size() << " ";
                        cerr << endl;
                    }
                }

                if( prim.result != 0 ) {
                    auto satRes = prim.getResult();
                    assert(satRes >= 0);
                    if(debug) DEBUG(satRes);
                    res += satRes;
                }
            }

            return res;
        }


        big_integer getResultForComponent(VI cmp, int tw_iters = 20) {
            const bool debug = false;


            InducedGraph g = GraphInducer::induce(V, cmp);

            TREEWIDTH trw;
            volatile sig_atomic_t tle = 0;
            TreewidthDecomposition decomp = trw.main(g.V, tw_iters, tle); // just for test, better make it 100 for
            assert(decomp.isCorrect());

            VVI tree = decomp.getStructure();
            VVI bags = decomp.getBags();


            int tw = max_element(ALL(bags), [](VI &b1, VI &b2) { return b1.size() < b2.size(); })->size();
            cerr << "treewidth: " << tw << endl;

            int THR = 26;
            if( tw > THR ){
                return -1; // try to find value using DualDecompotition

//                return getBranchedResultForComponent(g,decomp, min(tw - THR,3));
//                return getBranchedResultForComponent(g,decomp, tw - THR);
            }


            NiceTreewidthDecomposition niceDecomp(g.V, tree, bags);
            assert(niceDecomp.isCorrect());
            tree = niceDecomp.getStructure();
            bags = niceDecomp.getBags();

            for (VI &bag : bags)
                for (int &b : bag)
                    b = g.nodes[b] + 1; // this +1 here is because bags represent variables that are numbered from 1 to vars instead of from 0 to vars-1

            for (int &d : niceDecomp.introduces) if (d != -1) d = g.nodes[d] + 1;
            for (int &d : niceDecomp.forgets) if (d != -1) d = g.nodes[d] + 1;


            if (debug) {
                DEBUG(cmp);
                GraphUtils::writeGraphHumanReadable(tree);
                DEBUG(bags);
                DEBUG(niceDecomp.introduces);
                DEBUG(niceDecomp.forgets);
                DEBUG(niceDecomp.sons);
            }

            for (VI &b : bags) sort(ALL(b));

            int root = niceDecomp.getRoot();


            int T = tree.size();

            vector<vector<big_integer> > DP(T);

            auto value = [&tree, &bags, &niceDecomp, &DP](int num, LL mask) {
                if (!DP[num].empty()) return DP[num][mask];
                else return big_integer(1);
            };


            auto updateJoinNode = [&tree, &bags, &niceDecomp, &DP](int num) {
                if (debug)cerr << "updating join node, num = " << num << "  bag = " << bags[num] << endl;
                int s1 = niceDecomp.sons[num][0];
                int s2 = niceDecomp.sons[num][1];


                int B = bags[num].size();
                DP[num] = vector<big_integer>(1ll << B, 0);

                for (LL i = 0; i < (1ll << B); i++)
                    DP[num][i] += DP[s1][i] * DP[s2][i]; // we do not have to remap, since bags are identical

                if (debug) {
                    cerr << "DP[num]: ";
                    for (int i = 0; i < (1 << B); i++) cerr << to_string(DP[num][i]) << "  ";
                    ENDL(2);
                }
            };

            auto updateForgetNode = [&tree, &bags, &niceDecomp, &DP](int num) {
                if (debug)
                    cerr << "updating forget node, num = " << num << "   bag = " << bags[num] << "  forgets: "
                         << niceDecomp.forgets[num] << endl;

                int B = bags[num].size();
                int p = niceDecomp.forgets[num];
                int son = niceDecomp.sons[num][0];


                unordered_map<int, int> ind2;
                VI sonBag = bags[son];
                for (int i = 0; i < sonBag.size(); i++) ind2[sonBag[i]] = i;

                VI ind(B, -1);
                for (int i = 0; i < B; i++) ind[i] = ind2[bags[num][i]];

                int ind2P = ind2[p];

                assert(B + 1 == sonBag.size());

                if (debug)DEBUG(son);
                if (debug)DEBUG(ind2[p]);

                DP[num] = vector<big_integer>(1ll << B, 0);

                for (LL i = 0; i < (1ll << B); i++) {
                    LL mask = i;

                    int mappedMask = 0;
                    for (LL j = 0; (1ll << j) <= mask; j++) {
                        if (mask & (1ll << j)) mappedMask |= (1ll << ind[j]);
                    }

//                DEBUG(mask);
//                DEBUG(mappedMask);
//                DEBUG( (mappedMask | (1<<ind2[p])) );
                    DP[num][i] += DP[son][mappedMask] + DP[son][mappedMask | (1ll << ind2P)];
                }
                if (debug) {
                    cerr << "DP[num]: ";
                    for (int i = 0; i < (1 << B); i++) cerr << to_string(DP[num][i]) << "  ";
                    ENDL(2);
                }
            };


            auto getValueForSon = [&tree, &bags, &niceDecomp, &value](int num, int son,
                                                                      LL mask, /*unordered_map<int,int>& ind*/VI &ind) {
                LL mappedMask = 0;
                for (LL i = 0; (1ll << i) <= mask; i++) {
                    if (mask & (1ll << i)) {
                        if (ind[i] != -1) mappedMask |= (1ll << ind[i]);
                    }
                }

                return value(son, mappedMask);
            };

            auto updateIntroduceNode = [=,&tree, &bags, &niceDecomp, &DP, &getValueForSon](int num) {
                if (debug)
                    cerr << "updating introduce node, num = " << num << "    bag = " << bags[num] << "    introduces: "
                         << niceDecomp.introduces[num] << endl;

                int B = bags[num].size();
                int son = niceDecomp.sons[num][0];

                unordered_map<int, int> ind2;
                VI sonBag = bags[son];
                for (int i = 0; i < sonBag.size(); i++) ind2[sonBag[i]] = i;

                VI ind(B, -1);
                for (int i = 0; i < B; i++) if (ind2.count(bags[num][i])) ind[i] = ind2[bags[num][i]];

                if (debug)DEBUG(son);
                if (debug)DEBUG(ind);


                DP[num] = vector<big_integer>(1ll << B, 0);


                { // test using gray codes
//                VI falsyLiteralsInClause(cls.size(),0);
                    VI falsyLiteralsInClause(cls, 0);
                    int falsifiedClauses = 0;

                    auto fun = [=,&bags, &falsyLiteralsInClause, &DP, &getValueForSon, &num, &son, &ind, &falsifiedClauses, &B](
                            LL mask, int bit) {


                        if (mask == 0) {
                            if (debug) cerr << "Initial mask: " << mask << " bit = " << bit << endl;

                            for (int b : bags[num]) {
//                            for( int c : inClauses[b] ){
                                for (PII c : inClausesSign[b]) {
                                    if (c.second == -1) continue;

//                                if( clauses[c].count(b) ){
                                    if (c.second == 1) {
                                        falsyLiteralsInClause[c.first]++;
                                        if (falsyLiteralsInClause[c.first] == clauses[c.first].size()) {
                                            falsifiedClauses++;
                                            if (debug)
                                                cerr << "\tclause " << clauses[c.first] << " BECOMES falsified" << endl;
                                        }
                                    }
                                }
                            }
                        } else {

                            int b = bags[num][bit];
                            bool added = ((mask & (1ll << bit)) != 0); // true if bit was added, false otherwise

                            if (debug) {
                                cerr << "mask: ";
                                StandardUtils::writeInBinary(mask, B);
                                cerr << ", bit: " << bit << "(bag " << bags[num][bit] << ") "
                                     << (added ? " added" : " removed") << endl;
                            }

                            for (pair<int, int> c : inClausesSign[b]) {
                                if (c.second == -1) continue; // if there is b and ~b in clause c

                                if ((added && c.second == 0) || (!added && c.second == 1)) {
                                    falsyLiteralsInClause[c.first]++;
                                    if (falsyLiteralsInClause[c.first] == clauses[c.first].size()) {
                                        falsifiedClauses++;
                                        if (debug)
                                            cerr << "\tclause " << clauses[c.first] << " BECOMES falsified" << endl;
                                    }
                                }

                                if ((added && c.second == 1) || (!added && c.second == 0)) {
                                    if (falsyLiteralsInClause[c.first] == clauses[c.first].size()) {
                                        falsifiedClauses--;
                                        if (debug)
                                            cerr << "\tclause " << clauses[c.first] << " NO LONGER falsified" << endl;
                                    }
                                    falsyLiteralsInClause[c.first]--;
                                }

                            }

                        }

                        if (falsifiedClauses > 0) {
                            DP[num][mask] = 0;
                        } else {
                            DP[num][mask] = getValueForSon(num, son, mask, ind);
                        }
                    };

                    GrayCode::allSubsets(B, fun);
                }


                if (debug) {
                    cerr << "DP[num]: ";
                    for (int i = 0; i < (1 << B); i++) cerr << to_string(DP[num][i]) << "  ";
                    ENDL(2);
                }
            };


            function<void(int num, int par)> dp =
                    [&tree, &bags, &niceDecomp, &dp, &updateForgetNode, &updateIntroduceNode, &updateJoinNode, &DP](
                            int num, int par) {

                        if (debug) cerr << "\rdp, num = " << num << "  par = " << par << endl;

                        for (int d : tree[num]) {
                            if (d != par) dp(d, num);
                        }

                        if (niceDecomp.introduces[num] != -1) updateIntroduceNode(num);
                        else if (niceDecomp.forgets[num] != -1) updateForgetNode(num);
                        else if (niceDecomp.sons[num].size() == 2) updateJoinNode(num);
                        else {
                            if (debug)cerr << num << " is a leaf node!, sons[num] = " << niceDecomp.sons[num] << endl;
                        } // in a leaf, do nothing

                        if (!niceDecomp.sons[num].empty()) {
                            for (int s : niceDecomp.sons[num]) vector<big_integer>().swap(DP[s]); // clearing space
                        }

                    };

            dp(root, root);
            auto res = DP[root][0];

            return res;
        }



        big_integer getResult(){
            big_integer res = result;

            sort(ALL(comps), [](VI &v1, VI &v2) { return v1.size() < v2.size(); });

            {
                cerr << "Component sizes: ";
                for (VI cmp : comps) cerr << cmp.size() << " ";
                cerr << endl;
            }

            for (VI &cmp : comps) {
                auto compResult = getResultForComponent(cmp);

                if( compResult == -1 ) return -1;

                res *= compResult;
                if (compResult == big_integer(0)) break;
            }

            return res;
        }
    };


    namespace Dual{
        VVI V; // primal graph
        VVI comps;


        void createGraph() {
            const bool debug = false;
            if (debug) {
                DEBUG(clauses);
                DEBUG(inClauses);
            }

            V = VVI(cls);

            for( int i=0; i<cls; i++ ){
                unordered_set<int> zb;
                for( int d : clauses[i] ){
                    d = abs(d);
                    for( int c : inClauses[d] ){
                        if( c != i ) zb.insert(c);
                    }
                }
                V[i] = VI(ALL(zb));
            }

            if(debug) DEBUG(V);

            comps = ConnectedComponents::getConnectedComponents(V);

            for (int i = (int) comps.size() - 1; i >= 0; i--) {
                if (comps[i].size() == 1) {
                    swap(comps[i], comps.back());
                    comps.pop_back();
                }
            }

            if(debug) cerr << "Dual graph created" << endl;
        }


        big_integer getResultForComponent(VI cmp){
            const bool debug = false;

            sort(ALL(cmp));

            InducedGraph g = GraphInducer::induce( V,cmp );

            TREEWIDTH trw;
            volatile sig_atomic_t tle = 0;
            TreewidthDecomposition decomp = trw.main(g.V, 50, tle); // just for test, better make it 100 for

            assert(decomp.isCorrect());

            VVI tree = decomp.getStructure();
            VVI bags = decomp.getBags();


            NiceTreewidthDecomposition niceDecomp(g.V, tree, bags);
            assert(niceDecomp.isCorrect());
            tree = niceDecomp.getStructure();
            bags = niceDecomp.getBags();


            for (VI &bag : niceDecomp.getBags()) for (int &b : bag) b = g.nodes[b];
            for (int &d : niceDecomp.introduces) if (d != -1) d = g.nodes[d];
            for (int &d : niceDecomp.forgets) if (d != -1) d = g.nodes[d];

            int tw = max_element(ALL(bags), [](VI &b1, VI &b2) { return b1.size() < b2.size(); })->size();
            cerr << "treewidth: " << tw << endl;
            if(tw > 26) return -1;

            if (debug) {
                DEBUG(cmp);
                GraphUtils::writeGraphHumanReadable(tree);
                DEBUG(bags);
                DEBUG(niceDecomp.introduces);
                DEBUG(niceDecomp.forgets);
                DEBUG(niceDecomp.sons);
            }

            struct DualDP : public TreewidthDP{
                DualDP(VVI& V) : TreewidthDP(V){}
                DualDP(NiceTreewidthDecomposition & decomp) : TreewidthDP(decomp){}
                typedef vector<big_integer> VBI;
                typedef vector<VBI> VVBI;

                void processLeafNode(int num) override {
                    DP[num][0] = 1;
                }

                void processIntroduceNodeMask(int num, bitmask mask, bitmask mappedMask, int bitChanged) override {
                    int son = decomp->sons[num][0];
                    int C = decomp->introduces[num];// introduced clause

                    if(debug){
                        cerr << endl << "introduce" << endl;
                        DEBUG(num);
                        DEBUG(son);
                        DEBUG(mask);
                        DEBUG(mappedMask);
                        DEBUG(bitChanged);
                        DEBUG(AVars);
                        DEBUG(ALiterals);
                        DEBUG(A);
                        DEBUG(bagVars);
                        DEBUG(sonVars);
                    }

                    updateAVars(num,bitChanged, mask);
                    if( bitChanged != -1 ){
                        if( (mask & (1ll<<bitChanged)) != 0 )  A.insert( bags[num][bitChanged] );
                        else A.erase( bags[num][bitChanged] );
                    }

                    if(debug){
                        ENDL(1);
                        DEBUG(AVars);
                        DEBUG(ALiterals);
                        DEBUG(A);
                        DEBUG(bagVars);
                        DEBUG(sonVars);
                    }

                    bool isUnfalsifiable = false; // #TEST probably this is the right one

                    for (PII p : ALiterals) {
                        if (ALiterals.count(-p.first)) { // if literals in A have d and -d, then some clause is set to true, so A is not falsifiable
                            isUnfalsifiable = true;
                            break;
                        }
                    }


                    if(debug){
                        DEBUG(AVars);
                        DEBUG(ALiterals);
                        DEBUG(isUnfalsifiable);
                    }


                    if( isUnfalsifiable ){ // if i UN_falsifiable
                        DP[num][mask] = 0;
                        if( debug ) DEBUG(DP[son][mappedMask]);
                        if(debug) DEBUG( DP[num][mask] );
                    }else{



                        bool belongs = A.count(C);

                        if(debug){ DEBUG(A); DEBUG(C);DEBUG(belongs); }

                        if(!belongs){
                            int power = 0;
                            unordered_set<int> varC;
                            for( int v : clauses[C] ) varC.insert( abs(v) );
                            for( int v : varC ) if( sonVars.count(v) == 0 ) power++;

                            if(debug){
                                DEBUG(sonVars);
                                DEBUG(varC);
                                DEBUG(power);
                            }

                            big_integer factor = 1;
                            if(power > 0) factor = StandardUtils::binaryPower( big_integer(2), power );

                            if( debug ) DEBUG(DP[son][mappedMask]);

                            DP[num][mask] = DP[son][mappedMask] * factor;

                            if( debug ) DEBUG(DP[num][mask]);

                        }else{
                            int power = 0;
                            unordered_set<int> varC;
                            for( int v : clauses[C] ) varC.insert( abs(v) );

                            if(debug){
                                cerr << "AVars with C: " << endl;
                                DEBUG(AVars);
//                                DEBUG(ALiterals);
                            }

//                            updateAVars(num,bitChanged, mask ^ ( 1ll << bitChanged )); // need AVars of A \ C, so need to unmark C from AVars

                            auto AVarsNoC = AVars;
                            for( int v : clauses[C] ){
                                AVarsNoC[ abs(v) ]--;
                                if( AVarsNoC[ abs(v) ] == 0 ) AVarsNoC.erase( abs(v) );
                            }

                            if(debug){
                                cerr << "AVars without C: " << endl;
                                DEBUG(AVarsNoC);
//                                DEBUG(ALiterals);
                            }

                            for( int v : varC ){
                                if( sonVars.count(v) > 0 && AVarsNoC.count(v) == 0 ) power++;
                            }
//                            updateAVars(num,bitChanged, mask); // and add C back to AVar

                            big_integer divisor = 1;
                            if(power > 0) divisor = StandardUtils::binaryPower( big_integer(2), power );


                            if(debug){
                                DEBUG(power);
                                DEBUG(divisor);
                                DEBUG(sonVars);
                                DEBUG(varC);
                                if( DP[son][mappedMask] % divisor != 0 ){
                                    DEBUG(DP[son][mappedMask]);
                                    DEBUG(divisor);
                                    assert(DP[son][mappedMask] % divisor == 0);
                                }
                            }

                            if( debug ) DEBUG(DP[son][mappedMask]);
                            DP[num][mask] = DP[son][mappedMask] / divisor;
                            if( debug ) DEBUG(DP[num][mask]);

                        }

                    }

                }

               big_integer countModels(int num){
                    big_integer cnt = 0;
                    int B = bags[num].size();
                    for( int A = 0; A < (1ll<<B); A++ ){
                        cnt += DP[num][A] * ( __builtin_popcount(A) % 2 == 0 ? 1 : -1 );
                    }
                    return cnt;
                }

                void processForgetNodeMask(int num, bitmask mask, bitmask mappedMask, int bitChanged) override {
                    int son = decomp->sons[num][0];
                    int C = decomp->forgets[num];// forgot clause

                    if(debug){
                        cerr << endl << "forget:" << endl;
                        DEBUG(num);
                        DEBUG(son);
                        DEBUG(forgetNodeIndex);
                        DEBUG(bitChanged);
                        DEBUG(mask);
                        DEBUG(mappedMask);
                        DEBUG( ( mappedMask | ( 1ll << forgetNodeIndex )) );

                        DEBUG( DP[son][mappedMask]);
                        DEBUG(DP[son][ mappedMask | ( 1ll << forgetNodeIndex ) ]);
                    }
                    DP[num][mask] = DP[son][mappedMask] - DP[son][ mappedMask | ( 1ll << forgetNodeIndex ) ];

                }

                void processJoinNodeMask(int num, bitmask mask, bitmask mappedMask, int bitChanged) override {

                    if(debug){
                        cerr << endl << "join" << endl;
                        DEBUG(num);
                        DEBUG(mask);
                        DEBUG(mappedMask);
                        DEBUG(bitChanged);
                    };


                    int s1 = decomp->sons[num][0];
                    int s2 = decomp->sons[num][1];

                    int power = 0;
                    updateAVars(num,bitChanged, mask);

                    for( int v : bagVars ) if( AVars.count(v) == 0 ) power++;

                    big_integer divisor = 1;
                    if(power > 0) divisor = StandardUtils::binaryPower( big_integer(2), power );

                    if(debug){
                        DEBUG(power);
                        DEBUG(divisor);
                    }

                    DP[num][mask] = DP[s1][mappedMask] * DP[s2][mappedMask];
                    DP[num][mask] /= divisor;
                }


                void updateIntroduceNode(int num) override {
                    initIntroduceNode(num);

                    enumerateSubsets( num, introduceEnumerationType,
                                      [=]( int num, bitmask mask, bitmask mappedMask, int bitChanged ){
                                          processIntroduceNodeMask(num, mask, mappedMask,bitChanged);
                                      } );

                    if(debug)DEBUG(countModels(num));
                }

                void updateForgetNode(int num) override {
                    initForgetNode(num);
                    enumerateSubsets( num, introduceEnumerationType,
                                      [=]( int num, bitmask mask, bitmask mappedMask, int bitChanged ){
                                          processForgetNodeMask(num, mask, mappedMask,bitChanged);
                                      } );
                    if(debug)DEBUG(countModels(num));
                }


                void updateJoinNode(int num) override {
                    initJoinNode(num);
                    enumerateSubsets( num, introduceEnumerationType,
                                      [=]( int num, bitmask mask, bitmask mappedMask, int bitChanged ){
                                          processJoinNodeMask(num, mask, mappedMask,bitChanged);
                                      } );
                    if(debug)DEBUG(countModels(num));
                }

                VVBI DP;
                unordered_set<int> bagVars;
                unordered_set<int> sonVars;

                unordered_map<int,int> AVars;
                unordered_set<int> A;

                unordered_map<int,int> ALiterals; // AVars but with signs

                void initializeDPTable() override { DP = VVBI(T); }
                void initializeDPTable(int num) override { DP[num] = VBI( 1ll << (int)bags[num].size(), 0 ); }
                void clearDPSpace(int son) override { VBI().swap( DP[son] ); }

                // update AVars and ALiterals
                void updateAVars(int num, int bitChanged, bitmask mask){
                    const bool debug = true;
                    if( bitChanged != -1 ){
                        int c = bags[num][bitChanged];
                        bool bitAdded = ( mask & (1ll << bitChanged) ) != 0;

                        if(bitAdded){
                            for( int v : clauses[c] ){
                                AVars[ abs(v) ]++;
                                ALiterals[v]++;
                            }
                        }
                        else{
                            for( int v : clauses[c] ){
                                AVars[ abs(v) ]--;
                                if( AVars[ abs(v) ] == 0 ) AVars.erase(abs(v));

                                ALiterals[v]--;
                                if(ALiterals[v] == 0) ALiterals.erase(v);
                            }
                        }

                    }
                }

                void createBagVars(int num){
                    bagVars.clear();
                    for( int c : bags[num] ){
                        for( int v : clauses[c] ) bagVars.insert( abs(v) );
                    }
                }

                void initIntroduceNode(int num) override {
                    createBagVars(num);
                    sonVars.clear();
                    int son = decomp->sons[num][0];
                    for( int c : bags[son] ){
                        for( int v : clauses[c] ) sonVars.insert( abs(v) );
                    }
                    A.clear();
                    AVars.clear();
                    ALiterals.clear();
                }

                void initForgetNode(int num) override {

                }

                void initJoinNode(int num) override {
                    AVars.clear();
                    createBagVars(num);
                }
            };



            DualDP runner(niceDecomp);


            runner.runDP();

            big_integer res = runner.countModels( runner.getDecomposition()->root );

            if(debug) DEBUG(res);


            return res;

        }

        big_integer getResult(){
            big_integer res = result;

            sort(ALL(comps), [](VI &v1, VI &v2) { return v1.size() < v2.size(); });


            {
                cerr << "Component sizes: ";
                for (VI cmp : comps) cerr << cmp.size() << " ";
                cerr << endl;
            }

            for (VI &cmp : comps) {
                auto compResult = getResultForComponent(cmp);
                if(compResult == -1) return -1;
                res *= compResult;
                if (compResult == big_integer(0)) break;
            }

            return res;
        }
    }

    void run(){
        bool multipleTests = false;
        bool generate = false;
        bool bruteForceTest = false;

        int REPS = 1;

        if(!generate && multipleTests){
            cin >> REPS;
            cin.ignore();
        }else if(generate){
//            generateTestCases(REPS);
            cerr << "Not supported" << endl;
            return;
        }

        for(int r=0; r<REPS; r++) {


            read();


            DEBUG(vars);
            DEBUG(cls);




            big_integer bfres = 0;
            if (bruteForceTest) {
                bfres = bruteForce();
                cerr << "bfres: " << to_string(bfres) << endl;

                cout << "s mc " << to_string(bfres) << endl;
                continue;
            }


            cerr << "Creating primal graph" << endl;
            Primal prim( clauses, inClauses, cls, vars );
            prim.preprocess();
            prim.createGraph();
            auto res = prim.getResult();

            big_integer result = 0;
            if( res >= 0 ) result = res;
            else{
                cerr << "Creating dual graph" << endl;
                Dual::createGraph();
                auto res = Dual::getResult();
                /*if( res != -1 ) */result = res;
            }

            DEBUG("s mc " + to_string(result));
            cout << "s mc " << to_string(result) << endl;

        }


        return;
    }

}


/*

 p cnf 6 6
 1 2 0
 2 3 0
 3 4 0
 4 5 0
 5 1 0
 6 -6 0


 p cnf 4 4
 1 2 0
 2 3 0
 3 4 0
 4 1 0


 p cnf 4 4
 1 -2 0
 2 -3 0
 3 -4 0
 4 -1 0



p cnf 5 7
3 -5 0
5 -5 0
-1 -4 0
1 -5 -3 0
1 -3 5 -4 0
-5 4 3 -3 -4 0
5 -3 -1 1 4 -5 0



p cnf 5 6
-1 0
1 0
-4 -2 0
-3 -5 0
2 5 3 0
2 -2 4 0


p cnf 5 7
4 0
5 4 0
2 -4 0
-2 5 0
3 -5 -1 0
1 -4 3 0
4 2 5 0


 */