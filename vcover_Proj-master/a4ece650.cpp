// Compile with c++ a2ece650.cpp -std=c++11 -o a2ece650
#include <iostream>
#include <sstream>
#include <vector>
#include <queue>
#include <cstring>
#include <stack>
#include <minisat/core/SolverTypes.h>
#include <minisat/core/Solver.h>
#include <numeric>
#include <algorithm>
#include <set>
#include <map>
#include <pthread.h>
#include <time.h>
#define MAX 100000

using namespace std;
using namespace Minisat;

const int MAXN = 1e5 + 5;
vector<int> graph[MAXN];
int dist[MAXN];
bool visited[MAXN];
int parent[MAXN];
vector<int> min_vertex_cover;
vector<int> min_vertex_3_cnf_cover;
vector<int> vc1_output_1;
vector<int> vc1_refined_output_1;
set<int> VC2_path;
vector<int> vc2_refined_output_2;
bool gotterminated = false;
bool gotterminated3cnf = false;
vector<int> vec_V;
vector<int> vec_E;
// GLOBAL VARIABLE
int vertices_num;
vector<int> Edges;
vector<int> Vertices;
vector<double> cnfLength, threecnfLength, vc1length, vc2length, ref1length, ref2length;

// FUNCATION DECLARATION

vector<int> findMinVetexCover(vector<int>, vector<int>, int k, int);
vector<int> findMinVetexCoverFor3ncf(vector<int>, vector<int>, int k, int);
void CNF_SAT(vector<int>);
void CNF_three_SAT(vector<int>);
void APPROCX_VC_1(int, vector<int>);
void APPROCX_VC_2(int, vector<int>);
void REFINED_APPROCX_VC_1(int, vector<int>);
void REFINED_APPROX_VC2(int, vector<int>);

// Define a comparison function to compare vertices based on their degrees
bool compareVertices(int a, int b, const vector<int> &degree)
{
    return degree[a] > degree[b];
}

bool is_element_in_vector(vector<int> v, int element)
{
    vector<int>::iterator it;

    it = find(v.begin(), v.end(), element);
    if (it != v.end())
    {
        return true;
    }

    else
    {
        return false;
    }
}
// TIME DURATION FOR EACH FUNCTION

vector<double> duration_cnf_sat_total;
vector<double> duration_3_cnf_sat_total;
vector<double> duration_apx_1_total;
vector<double> duration_apx_2_total;
vector<double> duration_apx_ref_1_total;
vector<double> duration_apx_ref_2_total;

void *thread_CNF_SAT(void *arg)
{
    clock_t start, finish;
    double duration;

    start = clock();

    CNF_SAT(Vertices);
    pthread_testcancel(); // checking for cancel request

    finish = clock();

    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    // push the durations here
    duration_cnf_sat_total.push_back(duration);
    return NULL;
}

void CNF_SAT(vector<int> Vertices)
{
    // FIND MID 2 IS MID
    int high = vertices_num; // all vertcies in vertex cover
    int low = 1;             // atleast 1 verttex in vc

    vector<int> current_vertex_cover;
    vector<int> tmp;

    tmp = {-1};
    while (high >= low)
    {
        int mid; // it is also k vertex cover
        mid = (high + low) / 2;
        current_vertex_cover = findMinVetexCover(Vertices, Edges, mid, vertices_num);

        bool checkCurrVertexSize = equal(current_vertex_cover.begin(), current_vertex_cover.end(), tmp.begin());
        if (not checkCurrVertexSize)
        {
            // means vertex cover can be more less that is left
            high = mid - 1;
            min_vertex_cover.clear();
            // update minimum value of vertex cover
            min_vertex_cover = current_vertex_cover;
        }
        else
        {
            // means vertex cover is on right side
            low = mid + 1;
        }
    }
    sort(min_vertex_cover.begin(), min_vertex_cover.end());
}

void *thread_3_CNF_SAT(void *arg)
{
    clock_t start, finish;
    double duration;

    start = clock();

    CNF_three_SAT(Vertices);
    pthread_testcancel(); // checking for cancel request

    finish = clock();

    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    // push the durations here
    duration_3_cnf_sat_total.push_back(duration);
    return NULL;
}

void CNF_three_SAT(vector<int> Vertices)
{
    // FIND MID 2 IS MID
    int high = vertices_num; // all vertcies in vertex cover
    int low = 1;             // atleast 1 verttex in vc

    vector<int> current_vertex_cover;
    vector<int> tmp;

    tmp = {-1};
    while (high >= low)
    {
        int mid; // it is also k vertex cover
        mid = (high + low) / 2;
        current_vertex_cover = findMinVetexCoverFor3ncf(Vertices, Edges, mid, vertices_num);

        bool checkCurrVertexSize = equal(current_vertex_cover.begin(), current_vertex_cover.end(), tmp.begin());
        if (not checkCurrVertexSize)
        {
            // means vertex cover can be more less that is left
            high = mid - 1;
            min_vertex_3_cnf_cover.clear();
            // update minimum value of vertex cover
            min_vertex_3_cnf_cover = current_vertex_cover;
        }
        else
        {
            // means vertex cover is on right side
            low = mid + 1;
        }
    }
    sort(min_vertex_3_cnf_cover.begin(), min_vertex_3_cnf_cover.end());
}

vector<int> findMinVetexCoverFor3ncf(vector<int> intVertices, vector<int> edges, int k, int vertices_num)
{
    // intVertices [0,1,2,3,4]
    // k vertex cover
    // vertices_num 5 (V 5)

    Solver solver;
    Var prop[vertices_num][k];
    int zero = 0;

    for (int i = 0; i < vertices_num; i++)
    {
        for (int j = 0; j < k; j++)
        {
            prop[i][j] = solver.newVar();
        }
    }

    /*
    At least one vertex is the ith vertex in the vertex cover:
    ∀i ∈ [1, k], a clause (x1,i ∨ x2,i ∨ · · · ∨ xn,i)
    */

    for (int i = 0; i < k; i++)
    {
        vec<Lit> clause_1;
        for (int n = 0; n < vertices_num; n++)
        {
            clause_1.push(mkLit(prop[n][i]));
        }
        solver.addClause(clause_1);
        clause_1.clear();
    }

    /*
    –   No one vertex can appear twice in a vertex cover.
        ∀m ∈ [1, n], ∀p, q ∈ [1, k] with p < q, a clause (¬xm,p ∨ ¬xm,q)
    */
    for (int m = 0; m < vertices_num; m++)
    {
        for (int p = 0; p < k - 1; p++)
        {
            for (int q = p + 1; q < k; q++)
            {
                // ¬(xm,p ^ xm,q) --- ¬xm,p ∨ ¬xm,q) this means either - xm,p  false or ¬xm,q false) true
                solver.addClause(~mkLit(prop[m][p]), ~mkLit(prop[m][q]));
            }
        }
    }

    /*
        No more than one vertex appears in the mth position of the vertex cover.
        ∀m ∈ [1, k], ∀p, q ∈ [1, n] with p < q, a clause (¬xp,m ∨ ¬xq,m)
    */
    for (int m = 0; m < k; m++)
    {
        for (int p = 0; p < vertices_num - 1; p++)
        {
            for (int q = p + 1; q < vertices_num; q++)
            {
                solver.addClause(~mkLit(prop[p][m]), ~mkLit(prop[q][m]));
            }
        }
    }

    /*
    Every edge is incident to at least one vertex in the vertex cover.
    ∀〈i, j〉 ∈ E, a clause (xi,1 ∨ xi,2 ∨ · · · ∨ xi,k ∨ xj,1 ∨ xj,2 ∨ · · · ∨ xj,k)
    */

    // Every edge is incident to at least one vertex in the vertex cover.
    for (int i = 0; i < int(edges.size()); i = i + 2)
    {
        vec<Lit> clause_1;
        for (int j = 0; j < k; j++)
        {
            clause_1.push(mkLit(prop[edges[i]][j]));
            clause_1.push(mkLit(prop[edges[i + 1]][j]));
        }
        solver.addClause(clause_1);

        // Convert clause to 3-CNF form
        while (clause_1.size() > 3)
        {
            vec<Lit> clause_2;
            clause_2.push(clause_1[0]);
            clause_2.push(clause_1[1]);
            Lit new_var = mkLit(solver.newVar());
            clause_2.push(new_var);
            solver.addClause(clause_2);

            clause_1[0] = ~new_var;
            clause_1[1] = clause_1[2];
            clause_1[2] = clause_1.last();
            clause_1.pop();
        }

        if (clause_1.size() == 2)
        {
            vec<Lit> clause_2;
            clause_2.push(clause_1[0]);
            clause_2.push(clause_1[1]);
            Lit new_var = mkLit(solver.newVar());
            clause_2.push(new_var);
            solver.addClause(clause_2);

            vec<Lit> clause_3;
            clause_3.push(~clause_1[0]);
            clause_3.push(~clause_1[1]);
            clause_3.push(new_var);
            solver.addClause(clause_3);
        }
        clause_1.clear();
    }

    vector<int> vertex_cover_output;

    if (solver.solve())
    {
        for (int i = 0; i < vertices_num; i++)
        {
            for (int j = 0; j < k; j++)
            {
                if (toInt(solver.modelValue(prop[i][j])) == 0)
                {
                    vertex_cover_output.push_back(i);
                }
            }
        }
        return vertex_cover_output;
    }
    else
    {
        return {-1};
    }
}

void *threadAPPROX_VC_1(void *arg)
{
    clock_t start, finish;
    double duration;

    start = clock();
    APPROCX_VC_1(vertices_num, Edges);
    finish = clock();

    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    duration_apx_1_total.push_back(duration);
    return NULL;
}

void APPROCX_VC_1(int vertex_num, vector<int> edge)
{
    //[2,1,2,0,2,3,1,4,4,3]
    vector<int> count(vertex_num, 0); // initially 0 degree to each node
    vector<int> result;

    while (1)
    {
        int maxi_num = -1; // value of that node
        int maxi = 0;      // degree of each node
        for (int i = 0; i < edge.size(); i++)
        {
            // 2,1,2,0,2,3,1,4,4,3
            if (edge[i] != -1)
            {
                count[edge[i]]++; // count array [1,1,3,2,2]
                if (count[edge[i]] > maxi)
                {
                    maxi = count[edge[i]]; // 3 is max value of 2
                    maxi_num = edge[i];    // 2
                }
            }
        }
        if (maxi_num == -1)
        {
            break;
        }
        vc1_output_1.push_back(maxi_num);

        for (int i = 0; i < edge.size(); i = i + 2)
        {
            if (edge[i] == maxi_num || edge[i + 1] == maxi_num)
            {
                edge[i] = -1;
                edge[i + 1] = -1;
            }
        }
    }
    sort(vc1_output_1.begin(), vc1_output_1.end());
}

void *threadAPPROX_VC_2(void *arg)
{

    clock_t start, finish;
    double duration;

    start = clock();
    APPROCX_VC_2(vertices_num, Edges);
    finish = clock();

    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    duration_apx_2_total.push_back(duration);
    return NULL;
}

void APPROCX_VC_2(int vertex_num, vector<int> edge)
{

    map<int, bool> visited_node;
    vector<pair<int, int>> edgesVector;
    for (int i = 0; i < edge.size(); i = i + 2)
        edgesVector.push_back(std::make_pair(edge[i], edge[i + 1]));

    int i = 0;
    while (!edgesVector.empty())
    {
        if (i < edge.size())
        {
            int u = edge[i];
            int v = edge[i + 1];

            for (auto it = edgesVector.begin(); it != edgesVector.end();)
            {

                if (it->first == u || it->second == u || it->first == v || it->second == v)
                {
                    it = edgesVector.erase(it);
                    VC2_path.insert(u);
                    VC2_path.insert(v);
                }
                else
                {
                    it++;
                }
            }

            i += 2;
        }
        else
        {
            break;
        }
    }
}

void *threadAPPROX_REF_VC_1(void *arg)
{

    clock_t start, finish;
    double duration;

    start = clock();
    REFINED_APPROCX_VC_1(vertices_num, Edges);
    finish = clock();

    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    duration_apx_ref_1_total.push_back(duration); //
    return NULL;
}

void REFINED_APPROCX_VC_1(int vertex_num, vector<int> edge)
{
    vc1_refined_output_1 = vc1_output_1;
    // Calculate the degree of each vertex
    vector<int> degree(edge.size(), 0);
    for (int i = 0; i < edge.size(); i++)
    {
        degree[edge[i]]++;
    }

    // Sort vc1_refined_output_1 based on the comparison function
    sort(vc1_refined_output_1.begin(), vc1_refined_output_1.end(), [&](int a, int b)
         { return compareVertices(a, b, degree); });

    for (int i = 0; i < vc1_refined_output_1.size(); i++)
    {
        vector<int> tempEdge = edge;
        for (int k = 0; k < vc1_refined_output_1.size(); k++)
        {
            if (vc1_refined_output_1[k] == -1 || k == i)
            {
                continue;
            }
            //[2,1,2,0,2,3,1,4,4,3]
            int curr = vc1_refined_output_1[k];
            for (int j = 0; j < tempEdge.size(); j = j + 2)
            {
                if (tempEdge[j] == curr || tempEdge[j + 1] == curr)
                {
                    tempEdge[j] = -1;
                    tempEdge[j + 1] = -1;
                }
            }
        }
        int sum = accumulate(tempEdge.begin(), tempEdge.end(), 0) + tempEdge.size();
        if (!sum)
        {
            vc1_refined_output_1[i] = -1;
        }
    }
    sort(vc1_refined_output_1.begin(), vc1_refined_output_1.end());
}

void *threadAPPROX_REF_VC_2(void *arg)
{

    clock_t start, finish;
    double duration;

    start = clock();
    REFINED_APPROX_VC2(vertices_num, Edges);
    finish = clock();

    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    duration_apx_ref_2_total.push_back(duration); //
    return NULL;
}

void REFINED_APPROX_VC2(int vertex_num, vector<int> edge)
{
    vc2_refined_output_2.assign(VC2_path.begin(), VC2_path.end());

    // Calculate the degree of each vertex
    vector<int> degree(edge.size(), 0);
    for (int i = 0; i < edge.size(); i++)
    {
        degree[edge[i]]++;
    }

    // Sort vc1_refined_output_1 based on the comparison function
    sort(vc2_refined_output_2.begin(), vc2_refined_output_2.end(), [&](int a, int b)
         { return compareVertices(a, b, degree); });

    for (int i = 0; i < vc2_refined_output_2.size(); i++)
    {
        vector<int> tempEdge = edge;
        for (int k = 0; k < vc2_refined_output_2.size(); k++)
        {
            if (vc2_refined_output_2[k] == -1 || k == i)
            {
                continue;
            }
            //[2,1,2,0,2,3,1,4,4,3]
            int curr = vc2_refined_output_2[k];
            for (int j = 0; j < tempEdge.size(); j = j + 2)
            {
                if (tempEdge[j] == curr || tempEdge[j + 1] == curr)
                {
                    tempEdge[j] = -1;
                    tempEdge[j + 1] = -1;
                }
            }
        }
        int sum = accumulate(tempEdge.begin(), tempEdge.end(), 0) + tempEdge.size();
        if (!sum)
        {
            vc2_refined_output_2[i] = -1;
        }
    }
    sort(vc2_refined_output_2.begin(), vc2_refined_output_2.end());
    return;
}

void output()
{
    cout << "CNF-SAT-VC: ";
    if (gotterminated)
    {
        cout << "timeout";
        gotterminated = false;
    }
    else
    {
        for (int i = 0; i < min_vertex_cover.size(); ++i)
        {
            if (i == min_vertex_cover.size() - 1)
            {
                cout << min_vertex_cover[i] << " ";
            }
            else
            {
                cout << min_vertex_cover[i] << ",";
            }
        }
        cnfLength.push_back(min_vertex_cover.size());
    }
    cout << "\n";
    cout << "3-CNF-SAT-VC: ";
    if (gotterminated3cnf)
    {
        cout << "timeout";
        gotterminated3cnf = false;
    }
    else
    {
        for (int i = 0; i < min_vertex_3_cnf_cover.size(); ++i)
        {
            if (i == min_vertex_3_cnf_cover.size() - 1)
            {
                cout << min_vertex_3_cnf_cover[i] << " ";
            }
            else
            {
                cout << min_vertex_3_cnf_cover[i] << ",";
            }
        }
        threecnfLength.push_back(min_vertex_3_cnf_cover.size());
    }
    cout << "\n";

    cout << "APPROX-VC-1: ";
    for (int i = 0; i < vc1_output_1.size(); i++)
    {
        if (i == vc1_output_1.size() - 1)
        {
            cout << vc1_output_1[i] << " ";
        }
        else
        {
            cout << vc1_output_1[i] << ",";
        }
        vc1length.push_back(vc1_output_1.size());
    }

    cout << "\n";
    // print path
    // sort(VC2_path.begin(), VC2_path.end());
    cout << "APPROX-VC-2: ";
    if (!VC2_path.empty())
    {
        bool isFirst = true;
        for (auto it = VC2_path.begin(); it != VC2_path.end(); ++it)
        {
            if (!isFirst)
            {
                cout << ",";
            }
            cout << *it;
            isFirst = false;
        }
        vc2length.push_back(VC2_path.size());
    }

    cout << "\n";

    cout << "REFINED-APPROX-VC-1: ";
    for (int i = 0; i < vc1_refined_output_1.size(); i++)
    {
        if (vc1_refined_output_1[i] != -1)
        {
            if (i == vc1_refined_output_1.size() - 1)
            {
                cout << vc1_refined_output_1[i] << " ";
            }
            else
            {
                cout << vc1_refined_output_1[i] << ",";
            }
        }
        ref1length.push_back(vc1_refined_output_1.size());
    }
    cout << "\n";

    cout << "REFINED-APPROX-VC-2: ";
    for (int i = 0; i < vc2_refined_output_2.size(); i++)
    {
        if (vc2_refined_output_2[i] != -1)
        {
            if (i == vc2_refined_output_2.size() - 1)
            {
                cout << vc2_refined_output_2[i] << " ";
            }
            else
            {
                cout << vc2_refined_output_2[i] << ",";
            }
        }
        ref2length.push_back(vc2_refined_output_2.size());
    }
    cout << "\n";

    min_vertex_cover.clear();
    min_vertex_3_cnf_cover.clear();
    vc1_output_1.clear();
    VC2_path.clear();
    vc1_refined_output_1.clear();
    vc2_refined_output_2.clear();
}
void thread_with_timout(pthread_t thread, int timeout, bool &gotterminated)
{
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_sec += timeout;

    int ret = pthread_timedjoin_np(thread, NULL, &ts);
    // cout<<ret<<endl;
    if (ret == 0)
    {
        // Thread completed before timeout
        // cout<<"ret is 0"<<endl;
        pthread_join(thread, NULL);
    }
    else if (ret == EBUSY || ret == 110 || ret != 0)
    {
        // cout<<"ïn busy"<<endl;
        // Thread still running, wait with timeout
        ret = pthread_timedjoin_np(thread, NULL, &ts);
        if (ret == ETIMEDOUT)
        {
            // Thread timed out, kill it
            // cout<<"kill thread"<<endl;
            gotterminated = true;
            pthread_cancel(thread);
        }
    }
}
// INPUT FUNCTION PARSING

string command_part_1;
int size = -1;

string handleInput(string in)
{
    char arr[MAX];
    // string command_part_2, command_part_3;
    string out;
    // istringstream splits(in, istringstream::in);

    // splits >> command_part_1;

    strcpy(arr, in.c_str());

    if (arr[0] == 'V')
    {

        int num = 0;
        for (int i = 0; arr[i] != '\0'; ++i)
        {

            if (arr[i] >= '0' && arr[i] <= '9')

                num = num * 10 + arr[i] - '0';
        }

        for (int j = 0; j < num; ++j)
        {
            vec_V.push_back(j);
        }

        while (vec_V.empty())
        {
            break;
        }
    }

    else if (arr[0] == 'E')
    {
        int num = 0;
        for (int i = 0; arr[i] != '\0'; i++)
        {

            if (arr[i] > '0' && arr[i] <= '9')
            {
                /*cout << arr[i] << "\n";*/
                num = num * 10 + arr[i] - '0';
            }
            else
            {
                if (arr[i] == '0' && num == 0)
                {
                    Edges.push_back(0);
                }
                if (arr[i] == '0' && (num != 0))
                {
                    num = num * 10 + arr[i] - '0';
                    Edges.push_back(num);
                    num = 0;
                }
                if (arr[i] != '0' && (num != 0))
                {
                    Edges.push_back(num);
                    num = 0;
                }
            }
        }
        for (int i = 0; i < Edges.size(); i++)
        {

            if (is_element_in_vector(vec_V, Edges[i]) == false)
            {
                // cout << vec_E[i];
                cout << "Error:some vertex in  edge not exists."; // check the error of edge: not a vertex
                Edges.erase(Edges.begin() + i);
                return 0;
            }
        }
        while (Edges.empty())
        {
            break;
        }

        vertices_num = vec_V.size();

        int s;
        pthread_t thread_cnf_sat, thread_3_cnf_sat, thread_apx_vc_1, thread_apx_vc_2, thread_apx_ref_vc_1, thread_apx_ref_vc_2;

        s = pthread_create(&thread_cnf_sat, NULL, thread_CNF_SAT, NULL);
        s = pthread_create(&thread_3_cnf_sat, NULL, thread_3_CNF_SAT, NULL);
        s = pthread_create(&thread_apx_vc_1, NULL, threadAPPROX_VC_1, NULL);
        s = pthread_create(&thread_apx_vc_2, NULL, threadAPPROX_VC_2, NULL);

        /*  first calculate  thread_apx_vc_1 and thread_apx_vc_2
            as there output is used in thread_apx_ref_vc_1 thread_apx_ref_vc_2
            for removing vertices greedley
        */
        pthread_join(thread_apx_vc_1, NULL); // apx2  complete
        pthread_join(thread_apx_vc_2, NULL); // apx_ref1  complete

        s = pthread_create(&thread_apx_ref_vc_1, NULL, threadAPPROX_REF_VC_1, NULL);
        s = pthread_create(&thread_apx_ref_vc_2, NULL, threadAPPROX_REF_VC_2, NULL);

        int timeout = 2; // timeout in seconds
        thread_with_timout(thread_cnf_sat, timeout, gotterminated);
        thread_with_timout(thread_3_cnf_sat, timeout, gotterminated3cnf);

        // pthread_join(thread_cnf_sat, NULL); // CNFSAT  complete
        // pthread_join(thread_3_cnf_sat, NULL);
        pthread_join(thread_apx_ref_vc_1, NULL); // apx_ref1  complete
        pthread_join(thread_apx_ref_vc_2, NULL); // apx_ref2 complete

        // replaced actual calls using pthread join
        //  CNF_SAT(Vertices);
        //  APPROCX_VC_1(vertices_num, Edges);
        //  APPROCX_VC_2(vertices_num, Edges);
        //  REFINED_APPROCX_VC_1(vertices_num, Edges);
        //  REFINED_APPROX_VC2(vertices_num, Edges);

        // output finction to generate final answer
        output();

        // CLEAR INPUT
        Edges.clear();
        Vertices.clear();
    }
    else
    {
        cout << "Error: Invalid command" << endl;
    }

    return out;
}

vector<int> findMinVetexCover(vector<int> intVertices, vector<int> edges, int k, int vertices_num)
{
    // intVertices [0,1,2,3,4]
    // k vertex cover
    // vertices_num 5 (V 5)

    Solver solver;
    Var prop[vertices_num][k];
    int zero = 0;

    for (int i = 0; i < vertices_num; i++)
    {
        for (int j = 0; j < k; j++)
        {
            prop[i][j] = solver.newVar();
        }
    }

    /*
    At least one vertex is the ith vertex in the vertex cover:
    ∀i ∈ [1, k], a clause (x1,i ∨ x2,i ∨ · · · ∨ xn,i)
    */

    for (int i = 0; i < k; i++)
    {
        vec<Lit> clause_1;
        for (int n = 0; n < vertices_num; n++)
        {
            clause_1.push(mkLit(prop[n][i]));
        }
        solver.addClause(clause_1);
        clause_1.clear();
    }

    /*
    –   No one vertex can appear twice in a vertex cover.
        ∀m ∈ [1, n], ∀p, q ∈ [1, k] with p < q, a clause (¬xm,p ∨ ¬xm,q)
    */
    for (int m = 0; m < vertices_num; m++)
    {
        for (int p = 0; p < k - 1; p++)
        {
            for (int q = p + 1; q < k; q++)
            {
                // ¬(xm,p ^ xm,q) --- ¬xm,p ∨ ¬xm,q) this means either - xm,p  false or ¬xm,q false) true
                solver.addClause(~mkLit(prop[m][p]), ~mkLit(prop[m][q]));
            }
        }
    }

    /*
        No more than one vertex appears in the mth position of the vertex cover.
        ∀m ∈ [1, k], ∀p, q ∈ [1, n] with p < q, a clause (¬xp,m ∨ ¬xq,m)
    */
    for (int m = 0; m < k; m++)
    {
        for (int p = 0; p < vertices_num - 1; p++)
        {
            for (int q = p + 1; q < vertices_num; q++)
            {
                solver.addClause(~mkLit(prop[p][m]), ~mkLit(prop[q][m]));
            }
        }
    }

    /*
    Every edge is incident to at least one vertex in the vertex cover.
    ∀〈i, j〉 ∈ E, a clause (xi,1 ∨ xi,2 ∨ · · · ∨ xi,k ∨ xj,1 ∨ xj,2 ∨ · · · ∨ xj,k)
    */
    for (int i = 0; i < int(edges.size()); i = i + 2)
    {
        vec<Lit> clause_3;
        for (int j = 0; j < k; j++)
        {
            clause_3.push(mkLit(prop[edges[i]][j]));
            clause_3.push(mkLit(prop[edges[i + 1]][j]));
        }
        solver.addClause(clause_3);
        clause_3.clear();
    }

    vector<int> vertex_cover_output;

    if (solver.solve())
    {
        for (int i = 0; i < vertices_num; i++)
        {
            for (int j = 0; j < k; j++)
            {
                if (toInt(solver.modelValue(prop[i][j])) == 0)
                {
                    vertex_cover_output.push_back(i);
                }
            }
        }
        return vertex_cover_output;
    }
    else
    {
        return {-1};
    }
}

void *ioTHREAD(void *arg)
{
    string result;
    while (!::cin.eof())
    {
        while (!cin.eof())
        {
            string line;
            getline(cin, line);

            if (cin.eof())
            {
                break;
            }

            result = handleInput(line);
        }
/*
        // calculate sum of time at end
        float duration_cnf_sat_sum = accumulate(duration_cnf_sat_total.begin(), duration_cnf_sat_total.end(), 0.0f);
        float duration_3_cnf_sat_sum = accumulate(duration_3_cnf_sat_total.begin(), duration_3_cnf_sat_total.end(), 0.0f);
        float duration_apx_1_sum = accumulate(duration_apx_1_total.begin(), duration_apx_1_total.end(), 0.0f);
        float duration_apx_2_sum = accumulate(duration_apx_2_total.begin(), duration_apx_2_total.end(), 0.0f);
        float duration_apx_ref_1_sum = accumulate(duration_apx_ref_1_total.begin(), duration_apx_ref_1_total.end(), 0.0f);
        float duration_apx_ref_2_sum = accumulate(duration_apx_ref_2_total.begin(), duration_apx_ref_2_total.end(), 0.0f);

        // actul time for duration_apx_ref_1_sum is duration_apx_1_sum + duration_apx_ref_1_sum
        duration_apx_ref_1_sum = duration_apx_1_sum + duration_apx_ref_1_sum;
        duration_apx_ref_2_sum = duration_apx_2_sum + duration_apx_ref_2_sum;
        float vc1_std = 0.0;
        float refVc1 = 0.0;
        float vc2_std = 0.0;
        float refVC2 = 0.0;
        int length = duration_cnf_sat_total.size();
        // for (int i = 0; i < length; i++)
        // {
        //     cout << duration_cnf_sat_total[i] << endl;
        // }
        float mean = duration_cnf_sat_sum / 3;
        float standardDeviation = 0.0;
        // cout << "CNF Mean CNF SD" << endl;
        // cout << to_string(mean) << endl;

        for (int i = 0; i < 10; ++i)
        {
            standardDeviation += pow(duration_cnf_sat_total[i] - mean, 2);
        }

        // cout << to_string(sqrt(standardDeviation / 2)) << endl;

        // cout << "VC 1  Mean VC1 SD VC1 APX " << endl;
        mean = duration_apx_1_sum / 10;
        // cout << to_string(mean) << endl;
        standardDeviation = 0.0;
        for (int i = 0; i < 10; ++i)
        {
            standardDeviation += pow(duration_apx_1_total[i] - mean, 2);
        }
        // cout << to_string(sqrt(standardDeviation / 9)) << endl;

        // for (int i = 0; i < length; i++)
        // {
        //     cout << to_string(duration_apx_1_total[i]) << endl;
        // }

        float approx_sum = 0;
        standardDeviation = 0.0;
        for (int i = 0; i < length; i++)
        {
            approx_sum += (vc1length[i] / cnfLength[i]);
        }
        // cout << to_string(approx_sum / 3) << endl;

        for (int i = 0; i < length; i++)
        {

            vc1_std += pow((vc1length[i] / cnfLength[i]) - (approx_sum / 3), 2);
        }
        vc1_std = sqrt(vc1_std / 2);
        // cout << to_string(vc1_std) << endl;

        // cout << "VC 2  Mean VC2 SD VC2 APX" << endl;

        mean = duration_apx_2_sum / 10;
        // cout << to_string(mean) << endl;

        for (int i = 0; i < 10; ++i)
        {
            standardDeviation += pow(duration_apx_2_total[i] - mean, 2);
        }
        // cout << to_string(sqrt(standardDeviation / 9)) << endl;
        // for (int i = 0; i < length; i++)
        // {
        //     cout << to_string(duration_apx_2_total[i]) << endl;
        // }

        // for (int i = 0; i < length; i++)
        // {
        //     cout << vc2length[i] / cnfLength[i] << endl;
        // }
        approx_sum = 0;
        standardDeviation = 0.0;
        for (int i = 0; i < length; i++)
        {
            approx_sum += (vc2length[i] / cnfLength[i]);
        }
        // cout << to_string(approx_sum / 3) << endl;

        for (int i = 0; i < length; i++)
        {

            vc2_std += pow((vc2length[i] / cnfLength[i]) - (approx_sum / 3), 2);
        }
        vc2_std = sqrt(vc2_std / 2);

        // cout << to_string(vc2_std) << endl;

        // cout << "REF 1 Mean REF 1 SD APRRX" << endl;
        mean = duration_apx_ref_1_sum / 10;
        // cout << to_string(mean) << endl;

        for (int i = 0; i < 10; ++i)
        {
            standardDeviation += pow((duration_apx_ref_1_total[i] + duration_apx_1_total[i]) - mean, 2);
        }
        // cout << to_string(sqrt(standardDeviation / 9)) << endl;

        approx_sum = 0;
        standardDeviation = 0.0;
        for (int i = 0; i < length; i++)
        {
            approx_sum += (ref1length[i] / cnfLength[i]);
        }

        // cout << to_string(approx_sum / 3) << endl;
        for (int i = 0; i < length; i++)
        {
            refVc1 += pow((ref1length[i] / cnfLength[i]) - (approx_sum / 3), 2);
        }
        refVc1 = sqrt(refVc1 / 2);

        // cout << to_string(refVc1) << endl;
        // for (int i = 0; i < length; i++)
        // {
        //     cout << to_string(duration_apx_ref_1_total[i] + duration_apx_1_total[i]) << endl;
        // }
        // cout << "REF1 Apx " << endl;
        // for (int i = 0; i < length; i++)
        // {
        //     cout << ref1length[i] / cnfLength[i] << endl;
        // }

        // cout << "REF 2 Mean  SD APRX" << endl;
        mean = duration_apx_ref_2_sum / 10;

        // cout << to_string(mean) << endl;

        for (int i = 0; i < 10; ++i)
        {
            standardDeviation += pow((duration_apx_ref_2_total[i] + duration_apx_2_total[i]) - mean, 2);
        }
        // cout << to_string(sqrt(standardDeviation / 9)) << endl;

        approx_sum = 0;
        standardDeviation = 0.0;
        for (int i = 0; i < length; i++)
        {
            approx_sum += (ref2length[i] / cnfLength[i]);
        }

        // cout << to_string(approx_sum / 3) << endl;

        for (int i = 0; i < length; i++)
        {
            refVC2 += pow((ref2length[i] / cnfLength[i]) - (approx_sum / 3), 2);
            // cout << ref2length[i] / cnfLength[i] << endl;
        }
        // cout << refVC2;
        refVC2 = sqrt(refVc1 / 2);

        // cout << to_string(refVC2) << endl;
        // cout << "3 CNF Mean  SD " << endl;
        mean = duration_3_cnf_sat_sum / 3;
        // cout << to_string(mean) << endl;

        for (int i = 0; i < 10; ++i)
        {
            standardDeviation += pow((duration_3_cnf_sat_total[i]) - mean, 2);
        }
        // cout << to_string(sqrt(standardDeviation / 2)) << endl;

        // for (int i = 0; i < length; i++)
        // {
        //     cout << to_string(duration_apx_ref_2_total[i] + duration_apx_2_total[i]) << endl;
        // }
        // cout << "REF2 APx " << endl;
        // for (int i = 0; i < length; i++)
        // {
        //     cout << ref2length[i] / cnfLength[i] << endl;
        // }

        // code to print sum of times for each input
        // cout << to_string(duration_cnf_sat_sum) << " duration_cnf_sat_sum" << endl;
        // cout << to_string(duration_apx_1_sum) << " duration_apx_1_sum" << endl;
        // cout << to_string(duration_apx_2_sum) << " duration_apx_2_sum" << endl;
        // cout << to_string(duration_apx_ref_1_sum) << " duration_apx_ref_1_sum" << endl;
        // cout << to_string(duration_apx_ref_2_sum) << " duration_apx_ref_2_sum" << endl;
        */
    }
    return NULL;
}

int main(int argc, char **argv)
{
    int s;
    pthread_t input_output_thread; // input_output_thread_handler
    // This statement creates a new thread of execution and associates it with the threadIO function.
    s = pthread_create(&input_output_thread, NULL, ioTHREAD, NULL);
    /*
    By calling pthread_join(), the program will wait for the threadIO function to complete its execution
    before continuing to the next line of code.
    This ensures that any resources used by the thread are properly cleaned up before the program terminates.
    */
    // This statement waits for the thread with the ID threadio to terminate.
    pthread_join(input_output_thread, NULL);
    return 0;
}
