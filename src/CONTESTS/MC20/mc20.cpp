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
#include "utils/RandomNumberGenerators.h"
#include "combinatorics/GrayCode.h"
typedef InfInt big_integer;

string to_string(big_integer g){ return g.toString(); }

struct Triple{
    static UniformIntGenerator gen;
    Triple(){
        a = gen.rand();
        b = gen.rand();
        c = gen.rand();

        LL D = 1'000'000'001ll;
        a += c + D;
        b += c+D;
    }
    LL a,b,c;
    friend ostream& operator<<(ostream& str, Triple& t);
};

ostream& operator<<(ostream& str, Triple& t){
    str << "(" << t.a << "," << t.b << "," << t.c << ")";
    return str;
}
UniformIntGenerator Triple::gen( 0ll, 1ll << 60 );

const int MAX_REC_DEPTH_LOG = 5;

namespace MC20{

    // CAUTION! variables are numbered from 1  to vars, but graph is of size vars, not vars+1. REMEMBER TO ADD/SUBTRACT 1 !!

    vector< unordered_set<int> > clauses; // clauses[i] is the set of variables (e.g. {4, -6} )
    vector< unordered_set<int> > inClauses; // inClauses[i] is a set of clauses that contain variable i (perhaps begated)
    vector< vector< pair<int,int> > > inClausesSign; // inClausesSign[i] is a vector of pairs (clause, sign_of_i_in_that_clause)

    VB varSetValue;

    int cls; // number of clauses
    int vars; // number of variables
    big_integer result;

    //***********************************

    vector<Triple> varHashes;

    LL getClauseHash(unordered_set<int>& clause){
        LL hash = 0;
        LL mod = 0;
        for( int d : clause ){
            if(d>0) hash ^= varHashes[d].a;
            else hash ^= varHashes[-d].b;

            mod ^= varHashes[ abs(d) ].c;
        }
        return hash % ( mod + 1'000'000'000ll );
    }

    LL getClausesHash( vector<unordered_set<int>> & cl ){
        LL hash = 0;
        for( auto c : cl ) if( !cl.empty() ) hash ^= getClauseHash( c );
        return hash;
    }

    unordered_map<LL,big_integer> statesMap;
    deque<LL> statesQueue;
    const int MAX_STATES = 1'000'000;

    big_integer extractStateValue( vector<unordered_set<int>>& cl ){
        LL hash = getClausesHash(cl);
        auto it = statesMap.find(hash);
        if( it == statesMap.end() ) return -1;
        else return it->second;
    }

    void addToStates( vector<unordered_set<int>> &cl, big_integer res ){
//            return;
        LL hash = getClausesHash(cl);

//            cerr << "adding hash: " << hash << endl;

        if( statesQueue.size() > MAX_STATES ){
            LL toRemove = statesQueue.front();
            statesQueue.pop_front();
            statesMap.erase(toRemove);
        }

        statesMap[hash] = res;
        statesQueue.push_back(hash);
    }


    //***********************************



    // true if ass satisfies clause c
    bool satisfiesClause(VB &ass, int c) {
        for (int v : clauses[c]) {
            if (v > 0 && ass[v] == true) return true;
            else if (v < 0 && ass[-v] == false) return true;
        }
        return false;
    }

    // true if ass satisfies all clauses
    bool satisfiesAllClauses(VB &ass) {
        for (int c = 0; c < cls; c++) {
            if (!satisfiesClause(ass, c)) return false;
        }
        return true;
    }

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
        Primal( vector< unordered_set<int> >& clauses, vector< unordered_set<int> >& inClauses, int cls, int vars, int recDepth ){
            this->clauses = clauses;
            this->inClauses = inClauses;
//            inClauses = vector<unordered_set<int>>(vars+1); for( int i=0; i<cls; i++ ) for( int v : clauses[i] ) inClauses[abs(v)].insert(i);
            varSetValue = VB(vars + 1, false);
            this->vars = vars;
            this->cls = cls;
            result = 1;
            this->recDepth = recDepth;
        }
        int recDepth;
        VVI V; // primal graph
        VVI comps;
        vector< unordered_set<int> > clauses; // clauses[i] is the set of variables (e.g. {4, -6} )
        vector< unordered_set<int> > inClauses; // inClauses[i] is a set of clauses that contain variable i (perhaps begated)
        vector< vector< pair<int,int> > > inClausesSign; // inClausesSign[i] is a vector of pairs (clause, sign_of_i_in_that_clause)

        void logSpacing(){ for( int i=0; i<recDepth; i++ ) cerr << "  "; }

        VB varSetValue;

        int cls; // number of clauses
        int vars; // number of variables
        big_integer result;


        // returns variables sorted  in such a way, that the treewidth after branching on first variable is minimal (maximal treewidth from two choices v and ~v)
        VI getVarsReducingTreewidth( InducedGraph & g, TreewidthDecomposition & decomp ){
            const bool debug = false;

            logSpacing(); cerr << "checking vars-reducing" << endl;

            vector< pair<PII,int> > trwAfter;

            int T = decomp.getStructure().size();
            VVI bags = decomp.getBags();
            VVI inBags(vars+1);

            if(debug){
                DEBUG(*decomp.getV());
                DEBUG(T);
                DEBUG(g.V.size());
                DEBUG(g.V);
                DEBUG(*g.par);
                DEBUG(bags.size());
                DEBUG(decomp.getStructure());
                DEBUG(bags);
            }

//            for(VI& b : bags) for(  int& d : b) d = 1 + g.nodes[d]; // #TEST
//            DEBUG(bags);

            for( int i=0; i<T; i++ ) for( int b : bags[i] ){
//                inBags[ 1 + g.nodes[b] ].push_back(i);
//                inBags[1+b].push_back(i);
                inBags[b].push_back(i);
            }

//            DEBUG(inBags);

            VI bagsSizes(T,0);
            for(int i=0; i<T; i++) bagsSizes[i] = bags[i].size();

            unordered_set<int> temp;
            for (int v : g.nodes) {
                for (int c : inClauses[v + 1]) temp.insert(c);
            }
            vector<unordered_set<int>> cmpClauses;
            for (int c : temp) cmpClauses.push_back(clauses[c]);

//            DEBUG(cmpClauses);

            vector<unordered_set<int>> cmpInClauses(vars+1);
            for(int i=0; i<cmpClauses.size(); i++) for( int d : cmpClauses[i] ) cmpInClauses[abs(d)].insert(i);

            auto testVar = [=,&g, &decomp, &bagsSizes, &cmpClauses, &cmpInClauses, &inBags](int v){
                auto newClauses = cmpClauses;
                auto newInClauses = cmpInClauses;
                newClauses.push_back( {v} );
                newInClauses[ v ].insert( newClauses.size()-1 );

//                DEBUG(newClauses);
//                DEBUG(newInClauses);

                Primal prim(newClauses, newInClauses, newClauses.size(),vars,recDepth+1);
                prim.preprocess();

                VI remVars;
                VI newBagsSizes = bagsSizes;
                for(int i=1; i<=vars; i++){
                    if( prim.inClauses[i].empty() && !newInClauses[i].empty() ){ // variable i was set
//                        cerr << "\tvariable " << i << "was set" << endl;
                        for(int b : inBags[i]){
                            newBagsSizes[b]--;
//                            cerr << "\tremoving variable " << i << " from bag " << b << endl;
                        }
                    }else if( !newInClauses[i].empty() ){
                        remVars.push_back(i);
                    }
                }

                int res = 0;
                if(prim.result>0) for(int b : newBagsSizes) res = max(res,b);
                else if(debug) cerr << "\tprim.result == 0" << endl;

                if(res == 0) return PII(-1,0);

                if(debug)cerr << "treewidth after setting " << v << " to true: " << res << endl;


//                if( !remVars.empty() && prim.result > 0 ){ // #TEST
////                    DEBUG(remVars);
//                    for(int& d : remVars) d--;
//                    prim.createGraph();
//                    InducedGraph gRes = GraphInducer::induce( *g.par, remVars );
////                    DEBUG(gRes.V);
//                    TreewidthDecomposition indDec = getInducedDecomposition( gRes,decomp );
////                    DEBUG(newBagsSizes);
////                    for( VI b : indDec.getBags() ) cerr << b.size() << " ";
////                    cerr << endl;
////                    DEBUG(indDec.getWidth());
//                    assert( indDec.getWidth() == res );
//
//                }

                newClauses.back() = {-v};


                prim = Primal(newClauses, newInClauses, newClauses.size(),vars,recDepth+1);
                prim.preprocess();

                remVars.clear();
                newBagsSizes = bagsSizes;
                for(int i=1; i<=vars; i++){
                    if( prim.inClauses[i].empty() && !newInClauses[i].empty() ){ // variable i was set
                        for(int b : inBags[i]) newBagsSizes[b]--;
                    }else if( !newInClauses[i].empty() ){
                        remVars.push_back(i);
                    }
                }



                int res2 = 0;
                if(prim.result>0) for(int b : newBagsSizes) res2 = max(res2,b);
                else if(debug) cerr << "\tprim.result == 0" << endl;

//                if( !remVars.empty() && prim.result > 0 ){ // #TEST
////                    DEBUG(remVars);
//                    for(int& d : remVars) d--;
//                    prim.createGraph();
//                    InducedGraph gRes = GraphInducer::induce( *g.par, remVars );
//                    TreewidthDecomposition indDec = getInducedDecomposition( gRes,decomp );
////                    DEBUG(newBagsSizes);
////                    for( VI b : indDec.getBags() ) cerr << b.size() << " ";
////                    cerr << endl;
////                    DEBUG(indDec.getWidth());
//                    assert( indDec.getWidth() == res2 );
//                }

                if(debug){
                    cerr << "treewidth after setting " << v << " to false: " << res2 << endl;
                    ENDL(1);
                }

//                return max(res,res2);
                return PII(res2,res);
            };


//            DEBUG(g.nodes);
//            DEBUG(inClauses);
//            DEBUG(clauses);

            unordered_set<int> nodesToCheck;
            {
                for (int v : g.nodes) { // adding variables that are in binary clauses
                    for (int c : inClauses[v + 1]) {
                        if (clauses[c].size() == 2) {
                            nodesToCheck.insert(v);
                            break;
                        }
                    }
                }
            }

            { // adding variables that are in largest bags
                int width = decomp.getWidth();
                for( VI& b : bags ) if( b.size() == width ){
                    for(int d : b) nodesToCheck.insert(d-1);
                }
            }

            { // adding variables that have greatest degree in g.V
                int D = max_element( ALL(g.V), []( VI &a, VI &b ){ return a.size() < b.size(); } )->size();
                for(int i=0; i<g.V.size(); i++) if( g.V[i].size() == D ){
                    for( int b : inBags[ 1 + g.nodes[i] ] ) for( int d : bags[b] )   nodesToCheck.insert( d-1 );
                }

            }


//            for( int v : g.nodes ){
            for( int v : nodesToCheck ){
                v++;
                if(debug)cerr << "Testing branching on variable " << v << endl;
                PII trw = testVar(v);

                if( trw.first == 0 || trw.second == 0 ) {
                    logSpacing(); cerr << "trivial branching, returning trw: " << trw << endl;
                    return {v}; // if one assignment is trivial, then do not check other variables, just branch!
                }
                if(debug)cerr << "trw(" << v << ") = " << trw << endl;
                trwAfter.push_back( {trw,v} );
            }

//            exit(1);

            VI sq(vars+1,0);
            for( auto p : trwAfter ){
                for( int b : inBags[p.second] ) sq[p.second] += bags[b].size() * bags[b].size();
            }

            sort( ALL(trwAfter), [&sq]( auto p, auto q ){
                if( p.first.first*p.first.first + p.first.second*p.first.second != q.first.first*q.first.first + q.first.second*q.first.second ){
                    return p.first.first*p.first.first + p.first.second*p.first.second < q.first.first*q.first.first + q.first.second*q.first.second;
                }else return sq[p.second] > sq[q.second];
            } );

            logSpacing(); DEBUG(trwAfter[0]);
            if(debug)DEBUG(trwAfter);

            VI res;
            for(auto p : trwAfter) res.push_back(p.second);

//            exit(1);

            return res;
        }


        void preprocess(){

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

            bool changesDone = true;
            while(changesDone){
                if(result == 0) break;

                changesDone = false;
//                cerr << endl << " NEXT PREPROCESSING ITERATION!" << endl << endl;


                /*for( int i=0; i<cls; i++ ) { // this needs to be done just once, not in every iteration
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
                }*/


//                for( int i=0; i<cls; i++ ){

                VI modified(cls,0);
                VB valid(cls,true);
                iota(ALL(modified),0);
                for( int j=0; j<modified.size(); j++ ){ // #TEST
                    int i = modified[j];
                    if(!valid[i]) continue;
                    valid[i] = false;

                    if(result == 0) break;

//                    DEBUG(clauses);
//                    DEBUG(inClauses);
//                    DEBUG(varSetValue);
//                    ENDL(2);


                    unordered_set<PII, pairhash> clausesToClear;

                    if( clauses[i].size() == 1 ){
                        int d = abs(*clauses[i].begin());
                        bool assSign = ( *clauses[i].begin() > 0 );


//                        cerr << "d = " << d << "    clauses[i]: " << clauses[i] << "   inClauses[d]: " << inClauses[d] << endl;

                        VI temp( ALL(inClauses[d]) );
                        for( int c : temp ){
//                            DEBUG(c);
                            if( clauses[c].count( d * ( assSign ? 1 : -1 ) )  ){
                                clausesToClear.insert( PII(c,d) );
                                varSetValue[d] = true;
                            }else{
                                if( clauses[c].count( d * (assSign ? -1 : 1) ) && clauses[c].size() == 1 ){
//                                    cerr << "nullifying result" << endl;
                                    result = 0;
//                                cout << "s mc 0" << endl;
                                    return;
                                }

//                                cerr << "Removing (" << d * ( assSign ? -1 : 1 )<< ") from clause " << c << endl;
                                clauses[c].erase( d * ( assSign ? -1 : 1 ) ); // removing -d from that clause if possible, since it assigns false

//                                bool add = inClauses[d].size() > 0;
                                inClauses[d].erase(c);
//                                if (inClauses[d].empty() && add) result *= 2;

                                modified.push_back(c); // #TEST
                                valid[c] = true;
                            }
                        }

                    }

                    if( !clausesToClear.empty() ){
//                        DEBUG(clausesToClear);

                        changesDone = true;
                        for(PII c : clausesToClear){
//                            cerr << "Clearing clause " << c.first << ": " << clauses[c.first] << " because of variable " << c.second << endl;
                            for( int x : clauses[c.first] ){
//                                bool add = inClauses[ abs(x) ].size() > 0;
                                inClauses[ abs(x) ].erase(c.first);
//                                if (inClauses[ abs(x) ].empty()  & add ) result *= 2;
                            }
                            clauses[c.first].clear();
                            inClauses[c.second].erase(c.first);

                            modified.push_back(c.first); // #TEST
                            valid[c.first] = true;
                        }

//                        cerr << endl;
                    }


                }

                changesDone = false; // #TEST for modified vector

            }

            int power = 0;
            for( int i=1;i<=vars;i++ ) if( inClauses[i].empty() && varSetValue[i] == false ) power++;
//            cerr << "unsetVars power: " << power << endl;
            if( power > 0 ) result *= StandardUtils::binaryPower( big_integer(2), power );
//            if( power > 0 ) result <<= power;


//            cerr << "result after clearing clauses: " << to_string(result) << endl;
            if( result == 0 ) return;

            inClausesSign = vector<vector<pair<int, int> > >(vars + 1);
            for (int i = 1; i < vars + 1; i++) {
                for (int c : inClauses[i]) {
                    if (clauses[c].count(i) > 0 && clauses[c].count(-i) == 0) inClausesSign[i].push_back({c, 1});
                    else if (clauses[c].count(i) == 0 && clauses[c].count(-i) > 0) inClausesSign[i].push_back({c, 0});
                    else if (clauses[c].count(i) > 0 && clauses[c].count(-i) > 0) inClausesSign[i].push_back({c, -1});
                }
            }


            /*{
                VI clsSizeCnt(vars, 0);
                for (int i = 0; i < cls; i++) clsSizeCnt[clauses[i].size()]++;
                logSpacing();
                cerr << "After preprocessing there are clauses with sizes:  ";
                for (int i = 2; i <= 4; i++) cerr << "(" << "s:" << i << ",cnt:" << clsSizeCnt[i] << ")  ";
                cerr << " ... " << endl;
            }*/

            auto writeBinaryClauses = [=](){
                set<int> cla;
                for( int i=1; i<vars+1; i++ ){
                    bool written = false;
                    for(int c : inClauses[i]){
                        if( clauses[c].size() == 2 ){
                            cerr << "clauses[" << c << "]: " << clauses[c] << endl;
                            written = true;
                        }
                    }
                    if( written ) cerr << endl;
                }

//                { // write all binary clauses
//                    set<int> cla;
//                    for( int i=1; i<vars+1; i++ ){
//                        for(int c : inClauses[i]) cla.insert( c );
//                    }
//
//                    for(int c : cla){
//                        if( clauses[c].size() == 2 ){
//                            cerr << "clauses[" << c << "]: " << clauses[c] << endl;
//                        }
//                    }
//                }
//                exit(1);
            };

//            writeBinaryClauses();

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

                    swap(comps[i], comps.back());
                    comps.pop_back();
                }
            }
            if (debug) {
                DEBUG(comps);
                DEBUG(clauses);
                DEBUG(inClauses);
            }
//        exit(1);
        }

        big_integer getBranchedResultForComponent( InducedGraph& g, TreewidthDecomposition& decomp, int depth ){
            const bool debug = false;




            VVI tree = decomp.getStructure();
            VVI bags = decomp.getBags();
            for( VI& b : bags ) for(int& d : b) d = 1 + g.nodes[d];


//            cerr << "in getBranchedResult, bags = " << bags << endl;

            VI branchingNodes;

            VVI inBags(vars + 1);

            for (int i = 0; i < bags.size(); i++){
                for (int b : bags[i]) inBags[b].push_back(i);
            }

//            if (debug) DEBUG(inBags);

            VI squares(vars+1,0);

            bool useVarsReducing = true;
//            bool useVarsReducing = ( recDepth%2 == 0 );

            if(useVarsReducing){
                auto newDecomp = decomp;
                for( VI& bg : newDecomp.getBags() ) for( int& d : bg ) d = 1 + g.nodes[d]; // #TEST
//                for( VI& bg : decomp.getBags() ) for( int& d : bg ) d = g.nodes[d]; // #TEST
                auto varsRed = getVarsReducingTreewidth(g,newDecomp);
                depth = 1;
                branchingNodes = { varsRed[0] };
            }

            bool useSmallestClauses = true;
            bool useLargestBags = true; // #TEST;
            if(useVarsReducing) useSmallestClauses = useLargestBags = false;

            if( useLargestBags && useSmallestClauses ) depth >>= 1;

            if(useSmallestClauses){
                unordered_set<int> allVars;
                for(VI& b : bags) allVars.insert(ALL(b));
                VI sq(vars+1,0);
                int X = 4;
                VVI cntDegClause(vars+1, VI(X,0));
                for(int v : allVars){
                    for( int c : inClauses[v] ){
                        sq[v] += clauses[c].size() * clauses[c].size();
                        if( clauses[c].size() < X ) cntDegClause[v][ clauses[c].size() ]++;
                    }
                }

                VI t(ALL(allVars));
                sort( ALL(t), [&sq, &cntDegClause, &X](int a, int b){
                    for( int i=2; i<X; i++ ) if( cntDegClause[a][i] != cntDegClause[b][i] ) return cntDegClause[a][i] > cntDegClause[b][i];
                    if(sq[a] != sq[b]) return sq[a] > sq[b];
                    else return a > b;
                } );

//                bool highDegClauses = true;
//                for( int i=2; i<5; i++ ) if( cntDegClause[ t[0] ][i] > 0 ) highDegClauses = false;
//
//                if( !highDegClauses ) {
                for (int i = 0; i < depth; i++) {
                    int b = t[i];
                    branchingNodes.push_back(b);
                    if (debug) {
                        logSpacing();
                        cerr << "Adding to branching nodes node " << b
                             << " that has sum of clauses-size-square equals " << sq[b] << endl
                             << "\tand occurs in clauses: ";
                        for (auto c : inClauses[b]) {
                            logSpacing();
                            cerr << clauses[c] << endl;
                        }
                        cerr << endl;
                    }
                }
//                }

//                DEBUG(branchingNodes);
//                    exit(1);
            }

//             { // greatest degree in g.V
//                 VI nd(g.V.size());
//                 iota(ALL(nd),0);
//                 sort( ALL(nd), [=,&g](int a, int b){
//                     if( g.V[a].size() != g.V[b].size() ) return g.V[a].size() > g.V[b].size();
//                     else if(inClauses[a].size() != inClauses[b].size()) return inClauses[a].size() > inClauses[b].size();
//                     else return a > b;
//                 } );
//                 for(int i=0; i<depth; i++){
//                     int b = 1 + g.nodes[ nd[i] ];
//                     branchingNodes.push_back( b );
//                     cerr << "Adding node " << b << " with g.V degree: " << g.V[nd[i]].size() << " and inClauses.size(): " << inClauses[b].size() << endl;
//                 }
//             }



            if( useLargestBags ){// squares of bags sizes
//                logSpacing(); cerr << "HIGH DEG CLAUSES! Selecting nodes with largest bag.size square" << endl;
                if( useLargestBags && useSmallestClauses ) depth <<= 1;

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

//            if(debug) cerr << "presVars: "; for(auto it : presVars) cerr << it << " "; cerr << endl;

                unordered_set<int> inBrN( ALL(branchingNodes) );

//                DEBUG(branchingNodes);

                for (int i = 0; branchingNodes.size() < depth; i++) {
                    branchingNodes.push_back(*presVars.begin());
                    presVars.erase(presVars.begin());

                    int b = branchingNodes.back();

                    if( inBrN.count(b) ){
//                        logSpacing(); cerr << b << " already in branching nodes" << endl;
                        branchingNodes.pop_back();
                    }else inBrN.insert(b);


                    if (debug) {
                        logSpacing();
                        cerr << "Adding to branching nodes node " << b << " that has sum of bags-size-square equals "
                             << squares[b] << endl;
                        logSpacing();
                        cerr << "\tand occurs in bags of sizes: ";
                        for (auto B : inBags[b]) cerr << bags[B].size() << " ";
                        cerr << endl;
                        logSpacing();
                        for( auto c : inClauses[b] ) cerr << "\t" << clauses[c] << endl;
                        cerr << endl;
                    }
                }

//                DEBUG(branchingNodes);

            }




            if(debug){
                DEBUG(branchingNodes);
//                for( int i=0; i<=vars; i++ ){
//                    if( inBags[i].size() == 1 ){
//                        cerr << "Variable " << i << " occurse just in one bag: " << bags[ inBags[i][0] ] << endl;
//                    }
//                }
            }

            auto gClauses = clauses; gClauses.clear();
            vector< unordered_set<int> > gInClauses(vars+1);

            {
                unordered_set<int> allClauses;
                unordered_set<int> allVars;
                for( int v : g.nodes ){
                    allClauses.insert( ALL(inClauses[v+1]) );
                    assert( !inClauses[v+1].empty() );
//                    cerr << "inClauses[" << v << "]: " << inClauses[v+1] << endl;
                }

                if(debug){
                    DEBUG(allClauses.size());
                    DEBUG(g.nodes.size());
//                    DEBUG(g.nodes);
                }

                for( int c : allClauses ){
                    gClauses.push_back( clauses[c] );
//                    cerr << "Adding clauses[" << c << "]: " << clauses[c] << endl;
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
//                    DEBUG(gClauses);
//                    DEBUG(gInClauses);
                }
            }


//            {
//                auto stateValue = extractStateValue(gClauses);
//                if( stateValue != -1 ){
//                    logSpacing(); cerr << "EXTRACTING CACHED STATE VALUE 2!" << endl;
//                    addToStates( gClauses,stateValue ); // adding, to put it to the back of the queue
//                    return stateValue;
//                }
//            }

            big_integer res = 0;
            for( int A = 0; A < (1<<depth); A++ ){

                // now copy initial state

                VB sat( depth,false );
                for( int i=0; (1<<i) <= A; i++ ){
                    if( A & (1<<i) ){
                        sat[i] = true;
                    }
                }

//                for( int i=0; i<sat.size(); i++ ) cerr << "Setting variable " << branchingNodes[i] << " to " << sat[i] << endl;

                auto newClauses = gClauses;
                auto newInClauses = gInClauses;
                for( int i=0; i<depth; i++ ){
                    newClauses.push_back( { sat[i] ? branchingNodes[i] : -branchingNodes[i] } );
//                    if(debug) cerr << "Added new clause " << newClauses.back() << endl;
                    newInClauses[ branchingNodes[i] ].insert( (int)newClauses.size()-1 );
                }

                if(recDepth <= MAX_REC_DEPTH_LOG){
//                    ENDL(2);
                    logSpacing();cerr << "Starting new Primal, A = " << A << " / " << (1<<depth)-1 << endl;
                }

//                DEBUG(newClauses); DEBUG(newInClauses); DEBUG( newClauses.size() ); DEBUG(vars);

                Primal prim( newClauses, newInClauses, newClauses.size(), vars, recDepth+1 );

                for( int i=0; i<=vars; i++ ) if( newInClauses[i].empty() ) prim.varSetValue[i] = true;

//                cerr << "Preprocess" << endl;
                prim.preprocess();
//                cerr << "Creating graph" << endl;


//                auto stateValue = extractStateValue(prim.clauses);
//                if( stateValue != -1 ){
//                    logSpacing(); cerr << "EXTRACTING CACHED STATE VALUE 3!" << endl;
//                    addToStates( prim.clauses,stateValue ); // adding, to put it to the back of the queue
//                    res += stateValue;
//                }
//                else {

                if (prim.result > 0) {

                    prim.createGraph();

                    if (debug) {
                        logSpacing();
                        DEBUG(prim.V.size());
                        {
                            auto cmpgv = prim.comps;
                            ENDL(1);
                            logSpacing();
                            cerr << "sizes (>2) of comps of prim.V: ";
                            for (auto c : cmpgv) if (c.size() > 2) cerr << c.size() << " ";
                            cerr << endl;
                        }
                    }

//                    cerr << "getResult" << endl;
//                    auto satRes = prim.getResult();


//                        auto dec = decomp;
//                        for( VI& bg : dec.getBags() ) for( int& d : bg ) d = g.nodes[d];
//                        auto satRes = prim.getResult(&dec); // #TEST

                        VI remVars;
                        for( int i=0; i<prim.V.size(); i++ ) if( !prim.V[i].empty() ) remVars.push_back(i);
//                        DEBUG(remVars);
                        auto gInd = GraphInducer::induce( prim.V, remVars );
                        auto newDecomp = decomp;
                        for( VI& bg : newDecomp.getBags() ) for( int& d : bg ) d = 1 + g.nodes[d]; // #TEST
                        auto indDec = getInducedDecomposition(gInd, newDecomp);

                        for( VI& bg : indDec.getBags() ) for(int& d : bg) d = 1 + gInd.nodes[d]; // #TEST

                        auto satRes = prim.getResult(&indDec); // #TEST


//                        addToStates(prim.clauses, satRes);

                    assert(satRes >= 0);

                    /*if (satRes == 0) {
                        logSpacing();
                        cerr << "!!! satRes == 0 !!!" << endl;
                    }*/

                    if (debug) {
                        logSpacing();
                        DEBUG(satRes);
                    }
                    res += satRes;
                }else{
//                        addToStates(prim.clauses, 0);
                }

//                }
            }


//            addToStates( gClauses,res );
//            if(debug) DEBUG(res);

//            exit(1);
            return res;
        }

        TreewidthDecomposition getInducedDecomposition( InducedGraph& g, TreewidthDecomposition& decomp ){
            const bool debug = false;

            VVI tree = decomp.getStructure();
            int T = tree.size();
            VVI bags = decomp.getBags();

            unordered_set<int> treeInducer;
            for( int i=0; i<T; i++ ){
                for(int b : bags[i]){
                    b--; // #TEST decreasing to vertex id, from variable id
                    if( g.perm.find(b) != g.perm.end() ) treeInducer.insert(i);
                }
            }

            if(debug) {
                DEBUG(*g.par);
                DEBUG(*decomp.getV());
                DEBUG(tree);
                DEBUG(bags);
                DEBUG(g.V);
                DEBUG(g.nodes);
                DEBUG(g.perm);
            }


            VI inducer(ALL(treeInducer));
//            sort(ALL(inducer));
            if(debug)DEBUG(inducer);

            InducedGraph gTree = GraphInducer::induce( tree, inducer );

            if(debug) {
                DEBUG(gTree.V);
                DEBUG(gTree.perm);
                DEBUG(gTree.nodes);
            }

            VVI inducedBags( gTree.V.size() );

            VVI newBags( bags.size() );
            for( int i=0; i<T; i++ ){
                for( int b : bags[i] ){
                    b--; // #TEST decreasing to vertex id, from variable id
                    if( g.perm.find(b) != g.perm.end() ) newBags[i].push_back( g.perm[b] );
                }
            }

            if(debug)DEBUG(newBags);

            for( int i=0; i<T; i++ ){
                if( gTree.perm.find(i) != gTree.perm.end() ){
                    inducedBags[ gTree.perm[i] ] = newBags[i];
                }
            }

            if(debug)DEBUG(inducedBags);

            TreewidthDecomposition res( g.V, gTree.V, inducedBags );
            assert(res.isCorrect());
            return res;
        }

        big_integer getResultForComponent(VI cmp, int tw_iters = 8, TreewidthDecomposition* vDecomp = nullptr) {
            const bool debug = false;

//            cerr << "Considering component: " << cmp << endl;

            unordered_set<int> temp;
            for (int v : cmp) {
                for (int c : inClauses[v + 1]) temp.insert(c);
            }
            vector<unordered_set<int>> cmpClauses;
            for (int c : temp) cmpClauses.push_back(clauses[c]);
            auto stateValue = extractStateValue(cmpClauses);
            if (stateValue != -1) {
//                logSpacing();  cerr << "EXTRACTING CACHED STATE VALUE 1 !" << endl;
                return stateValue;
            }


            InducedGraph g = GraphInducer::induce(V, cmp);

            TREEWIDTH trw;
            volatile sig_atomic_t tle = 0;
//            logSpacing();

                // the lines below check for treewidth in each iteration


            TreewidthDecomposition decomp = trw.main(g.V, tw_iters, tle);
            assert(decomp.isCorrect());
            VVI tree = decomp.getStructure();
            VVI bags = decomp.getBags();
            int tw = max_element(ALL(bags), [](VI &b1, VI &b2) { return b1.size() < b2.size(); })->size();



            // the lines below do not check for treewidth in each iterations, they always take induced treewidth if possible
//            TreewidthDecomposition decomp(g.V,{},{});
//            int tw;
//            if( vDecomp == nullptr ){
//                decomp = trw.main(g.V, tw_iters, tle); // just for test, better make it 100 for
//                VVI bags = decomp.getBags();
//                tw = max_element(ALL(bags), [](VI &b1, VI &b2) { return b1.size() < b2.size(); })->size();
//            }
//            else tw = 1e7; // #TEST




            if( vDecomp != nullptr ){
                auto inducedDecomp = getInducedDecomposition(g,*vDecomp);

//                auto newDecomp = *vDecomp;
//                DEBUG(vDecomp->getBags());
//                for( VI& bg : newDecomp.getBags() ) for( int& d : bg ) d = 1 + g.nodes[d]; // #TEST
//                auto inducedDecomp = getInducedDecomposition(g,newDecomp);

                VVI bags2 = inducedDecomp.getBags();
                int tw2 = max_element(ALL(bags2), [](VI &b1, VI &b2) { return b1.size() < b2.size(); })->size();
//                logSpacing(); DEBUG(tw2);
                if( tw2 < tw ){
                    logSpacing(); cerr << "induced decomposition is better! "; cerr << "tw2 = " << tw2 << " < " << tw << " = tw" << endl;
                    decomp = inducedDecomp;
                    tw = tw2;

                }
            }

            if(recDepth <= MAX_REC_DEPTH_LOG + 1){
                logSpacing(); cerr << "treewidth: " << tw << endl;
            }

            tree = decomp.getStructure(); // #TEST
            bags = decomp.getBags(); // #TEST



            int THR = 23; // #TEST
            if( tw > THR ){
//                return -1; // try to find value using DualDecompotition
                auto res = getBranchedResultForComponent(g,decomp, 2);
                return res;
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

                assert( niceDecomp.getWidth() >= B );

                DP[num] = vector<big_integer>(1ll << B, 0);


                { // test using gray codes
                    VI falsyLiteralsInClause(cls, 0);
                    int falsifiedClauses = 0;

                    int mappedMask = 0;

                    auto fun = [=,&bags, &falsyLiteralsInClause, &DP, &getValueForSon, &num, &son, &ind, &falsifiedClauses, &B, &mappedMask](
                            LL mask, int bit) {


                        if (mask == 0) {
                            if (debug) cerr << "Initial mask: " << mask << " bit = " << bit << endl;

                            for (int b : bags[num]) {
                                for (PII c : inClausesSign[b]) {
                                    if (c.second == -1) continue;

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

                            if( ind[bit] != -1 ) mappedMask ^= (1ll << ind[bit]);

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
//                            DP[num][mask] = getValueForSon(num, son, mask, ind);
                            DP[num][mask] = value(son, mappedMask);
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

//            cerr << "Starting processing graph with treewidth: " << niceDecomp.getWidth() << endl;

            function<void(int num, int par)> dp =
                    [=,&tree, &bags, &niceDecomp, &dp, &updateForgetNode, &updateIntroduceNode, &updateJoinNode, &DP](
                            int num, int par) {


                        for (int d : tree[num]) {
                            if (d != par) dp(d, num);
                        }

                        if (debug) cerr << "\rdp, num = " << num << "  par = " << par << "  bags[num].size() = " << bags[num].size() << endl;

                        sort( ALL(bags[num]), [=](int a, int b){
                            return inClausesSign[a].size() < inClausesSign[b].size();
                        } );

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

            addToStates( cmpClauses,res ); // adding, to put it to the back of the queue

            return res;
        }



        big_integer getResult( TreewidthDecomposition* vDecomp = nullptr ){
            big_integer res = result;

            sort(ALL(comps), [](VI &v1, VI &v2) { return v1.size() < v2.size(); });

            for(auto& v : comps) sort(ALL(v));

            /* {
                 logSpacing();
                 cerr << "Component sizes: ";
                 for (VI cmp : comps) cerr << cmp.size() << " ";
                 cerr << endl;
             }*/


//            TREEWIDTH trw;volatile sig_atomic_t tle = 0;
//            TreewidthDecomposition decomp = trw.main(V, 50, tle); // just for test, better make it 100 for


            for (VI &cmp : comps) {
//                cerr << "compSize " << cmp.size() << endl;


//                ENDL(3); // #TEST
                auto compResult = getResultForComponent(cmp,8,vDecomp);

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

            TREEWIDTH trw;volatile sig_atomic_t tle = 0;
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
            if(tw > 28) return -1;

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
//                ~DualDP(){}
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


                    /* if( bags[son].empty() ){
                         cerr << "son is a leaf" << endl;
                         if( mask == 0 ){
 //                            if( debug ) DEBUG(DP[son][mappedMask]);
                             DP[num][mask] = 0; // empty set in unfalsifiable
                         }
                         else {
                             int power = 0;
                             for (int v : bagVars) if (AVars.count(v) == 0) power++;
                             if(debug) DEBUG(power);
                             big_integer res = 1;
                             if (power > 0) res = StandardUtils::binaryPower(big_integer(2), power);
                             DP[num][mask] = res;
                         }
 //                        if( debug ) DEBUG(DP[son][mappedMask]);
                         if(debug) DEBUG(DP[num][mask]);
                         return;
                     }*/


//                    bool isFalsifiable = ( mask > 0 );
                    bool isUnfalsifiable = false;

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
//                    cerr << "Counting number of models for subtree with node in " << num << endl;
                    big_integer cnt = 0;
                    int B = bags[num].size();
                    for( int A = 0; A < (1ll<<B); A++ ){
                        cnt += DP[num][A] * ( __builtin_popcount(A) % 2 == 0 ? 1 : -1 );
                    }
//                    cerr << "There are " << cnt << " models" << endl << endl;
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


//                    exit(1);

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
                    const bool debug = false;
                    if( bitChanged != -1 ){
                        int c = bags[num][bitChanged];
//                        cerr << "updating AVars and ALiterals, c = " << c << "  clauses[c]: " << clauses[c] << endl;
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

//                        if(debug){
//                            DEBUG(bitAdded);
//                            DEBUG(bagVars);
//                            DEBUG(AVars);
//                        }
                    }
                }

                void createBagVars(int num){
                    bagVars.clear();
                    for( int c : bags[num] ){
                        for( int v : clauses[c] ) bagVars.insert( abs(v) );
                    }
//                    if(debug) cerr << "in create bagVars, num = " << num << "  bags[num] = " << bags[num] << "  bagVars: " << bagVars << endl;
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
//                    createBagVars(num);
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


//            {
//                cerr << "Component sizes: ";
//                for (VI cmp : comps) cerr << cmp.size() << " ";
//                cerr << endl;
//            }



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
//        ifstream f( "track1_084.mcc2020_cnf" ); cin.rdbuf( f.rdbuf() );


        int REPS = 1;


        for(int r=0; r<REPS; r++) {
            read();

            varHashes = vector<Triple>(vars+1);


            DEBUG(vars);
            DEBUG(cls);


            big_integer bfres = 0;



            Primal prim( clauses, inClauses, cls, vars,0 );
            cerr << "First preprocessing" << endl;
            prim.preprocess();
            cerr << "Creating first primal graph" << endl;
            prim.createGraph();

//            DEBUG(prim.V);

            auto res = prim.getResult();

            big_integer result = 0;
            if( res >= 0 ) result = res;
            else{
                cerr << "Creating dual graph" << endl;
                Dual::createGraph();
                auto res = Dual::getResult();
                result = res;
            }

//            DEBUG("s mc " + to_string(result));
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



p cnf 9 12
6 1 0
6 -2 0
1 3 0
2 -3 0
2 4 0
-4 -5 0
-3 -5 0
-7 6 0
7 -8 0
8 -2 0
8 9 0
9 4 0


 p cnf 10 9
 1 2 0
 2 3 0
 4 5 0
 5 6 0
 6 4 0
 7 8 0
 8 9 0
 9 10 0
 10 7 0



p cnf 19 15
1 3 0
2 -3 0
3 16 0
16 -6 0
6 4 -5 0
5 -15 0
-16 7 3 0
7 8 12 13 0
-9 -8 0
9 -10 11 0
10 11 0
-11 -12 0
-13 14 15 0
-14 -15 0
17 18 19 0

 */