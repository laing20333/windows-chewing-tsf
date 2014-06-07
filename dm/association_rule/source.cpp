#include<iostream>
#include<cstdio>
#include<cmath>
#include<algorithm>
#include<map>
#include<set>
#include<string>
#include<vector>
#include<sstream>


using namespace std;

#define MAX_LINE_SIZE 10000001
#define HASH_BUCKET_SIZE 21

typedef set<string> ItemSet;
typedef set<set<string> > SuperItemSet;
struct key{
    double sup;
    double conf;
    string name;
};

struct rule{
    ItemSet p;
    ItemSet q;
};

struct cmp{
	bool operator()(const struct key &a, const struct key &b){
		if( abs(a.sup - b.sup) > 1e-5 ) return a.sup > b.sup;
		else if( abs(a.conf - b.conf) > 1e-5) return a.conf > b.conf;
		else return a.name < b.name;
	}
};

bool sup_cmp(const pair<ItemSet, double> &a, const pair<ItemSet, double> &b){
	return a.second > b.second;
}

int k;
int nrules = 0;
char line[MAX_LINE_SIZE];
double minsup, minconf;
double ntransactions = 0;
double total_time = 0;
map<int, SuperItemSet> frequent_itemsets;
map<ItemSet, double> support_count;
map<int, vector<ItemSet> > hash_table;
vector<pair<ItemSet, double> > support_count_order;
map<key, rule, cmp> rules;
ItemSet :: iterator endit;
clock_t st;

ItemSet read_a_transaction(FILE *fin);
SuperItemSet generate_candidates(SuperItemSet L, int k);
void count_itemsets_support(SuperItemSet candidate_itemsets, FILE *fin);
void prune_candidates(SuperItemSet &candidate_itemsets);
void generate_L1(FILE *fin);
SuperItemSet generate_C2_by_DHP();
void generate_L2(FILE *fin, SuperItemSet candidate_itemsets);
void generate_Lk(FILE *fin);
void partition(ItemSet p, ItemSet q, ItemSet :: iterator it);
void generate_rules();
void print_rules();
void print_itemset(ItemSet L);
void print_superitemset(SuperItemSet L);

ItemSet read_a_transaction(FILE *fin){
	ItemSet res;
	if(fgets(line, sizeof(line), fin) == NULL){
		return res;
	}
	stringstream ss(line);
	string tmp;
	ss >> tmp;
	while(ss >> tmp){
		if(tmp[tmp.length()-1] == ','){
			tmp.erase(tmp.end()-1);
		}
		res.insert(tmp);
	}
	return res;
}

SuperItemSet generate_candidates(SuperItemSet L, int k){
	SuperItemSet res;
	// join step
	SuperItemSet :: iterator it1;
	SuperItemSet :: iterator it2;
	for(it1 = L.begin(); it1 != L.end(); it1++){
		it2 = it1; it2++;
		for( ; it2 != L.end(); it2++){
			ItemSet s1 = *it1; ItemSet s2 = *it2;
			string last1 = *(--(*it1).end()); string last2 = *(--(*it2).end());
			s1.erase(last1); s2.erase(last2);
			if( s1 == s2 && last1 != last2){
				ItemSet candidate = *it1;
				candidate.insert(last2); 
				res.insert(candidate);
			}
		}
	}
	
	// prune step
	for(it1 = res.begin(); it1 != res.end(); it1++){
		ItemSet :: iterator it2;
		ItemSet tmp = *it1;
		for(it2 = (*it1).begin(); it2 != (*it1).end(); it2++){
			ItemSet test_tmp = tmp;
			test_tmp.erase(*it2);
			if(frequent_itemsets[k-1].find(test_tmp) == frequent_itemsets[k-1].end()){
			    res.erase(tmp);
				break;
			}
		}
	}
	return res;
}

void count_itemsets_support(SuperItemSet candidate_itemsets, FILE *fin){
 	rewind(fin);
	ItemSet transaction;
	transaction = read_a_transaction(fin);
	while(!transaction.empty()){
		// check candidate whether in the set or not
		SuperItemSet :: iterator it1;
		for(it1 = candidate_itemsets.begin(); it1 != candidate_itemsets.end(); it1++){
			bool isexist = true;
			ItemSet :: iterator it2;
			for(it2 = (*it1).begin(); it2 != (*it1).end(); it2++){
				if(transaction.find(*it2) == transaction.end() ){
					isexist = false;
					break;
				}
			}
			if(isexist) support_count[*it1]++;
		}
		transaction = read_a_transaction(fin);
	}

	return;
}

void prune_candidates(SuperItemSet &candidate_itemsets){
	SuperItemSet :: iterator it;
	for(it = candidate_itemsets.begin(); it != candidate_itemsets.end(); it++){		
		if( (support_count[*it] / ntransactions) + 1e-7 < minsup ){
			candidate_itemsets.erase(*it);
			support_count.erase(*it);
		}		
	}
	return;
}

void print_superitemset(SuperItemSet L){
	SuperItemSet :: iterator it3;
	for(it3 = L.begin(); it3 != L.end(); it3++){
		ItemSet :: iterator it4;
		for(it4 = (*it3).begin(); it4 != (*it3).end(); it4++){
			cout << *it4 << " ";
		}
		cout << support_count[*it3] << endl;
	}
	return ;
}

void print_itemset(ItemSet L){
	ItemSet :: iterator it;
	for(it = L.begin(); it != L.end(); it++){
		cout << *it << " ";
	}
	cout << endl;
}

void partition(ItemSet p, ItemSet q, ItemSet :: iterator it){
	if(it == endit){
		// decide to whether generate a rule
		if( !p.empty() && !q.empty() ){
			ItemSet all = p;
			for(ItemSet :: iterator it2 = q.begin(); it2 != q.end(); it2++){
				all.insert(*it2);
			}
			if( (support_count[all]/ support_count[p]) >= minconf){
					struct key rule_key;
					rule_key.sup = support_count[all] / ntransactions;
					rule_key.conf = (support_count[all]/ support_count[p]);
					for(ItemSet :: iterator itp = p.begin(); itp != p.end(); itp++){
						rule_key.name += (*itp);
					}
					for(ItemSet :: iterator itq = q.begin(); itq != q.end(); itq++){
                        rule_key.name += (*itq);
					}


					struct rule rule_value;					
					rule_value.p = p;
					rule_value.q = q;					
					rules[rule_key] = rule_value;
					nrules++;
			}
		}
		return;
	}
	// try to insert into p
	p.insert(*it);
	partition(p, q, ++it);
	it--; 
	p.erase(*it);

	// try to insert into q
	q.insert(*it);
	partition(p, q, ++it);
	it--;
	q.erase(*it);
}

void generate_L1(FILE *fin){
	st = clock();
	cout << "start to generate L1" << endl;
	// Count 1-itemset support
	stringstream ss;
	while(fgets(line, sizeof(line), fin) != NULL){
		ss.str(line);
		string tmp;
		ss >> tmp;
		while(ss >> tmp){
			if(tmp[tmp.length()-1] == ','){
				tmp.erase(tmp.end()-1);
			}
			ItemSet tmp_itemset; tmp_itemset.insert(tmp);
			support_count[tmp_itemset]++;
		}
		ss.clear();
		ntransactions++;
	}

	// Prune the items whose support < k
	map<ItemSet, double> :: iterator it;
	for(it = support_count.begin(); it != support_count.end(); it++){
		double support = it->second / ntransactions;
		if(support + 1e-7 >= minsup){
			frequent_itemsets[1].insert(it->first);
		}
	}
	print_superitemset(frequent_itemsets[1]);

	double duration = ( clock() - st ) / (double) CLOCKS_PER_SEC;
    cout << "Time for L1: " << duration << endl;
	cout << "L"<< "1" << " " << "size:" << frequent_itemsets[1].size() << endl;
	total_time += duration;
	return;
}

SuperItemSet generate_C2_by_DHP(FILE *fin){
	cout << "start to DHP" << endl;
	st = clock();
	SuperItemSet res;
	rewind(fin);
	ItemSet transaction = read_a_transaction(fin);
	while(!transaction.empty()){
		// generate all possible two-itemset and throw it into bucket by hashing
		for(ItemSet :: iterator it = transaction.begin(); it != transaction.end(); it++){
			ItemSet tmp; tmp.insert(*it);			
			if(frequent_itemsets[1].find(tmp) == frequent_itemsets[1].end()){
				continue;
			}
			
			ItemSet :: iterator it2 = it;
			it2++;
			for(;it2 != transaction.end(); it2++){
				ItemSet tmp2; tmp2.insert(*it2);										
				if(frequent_itemsets[1].find(tmp2) == frequent_itemsets[1].end()){
					continue;
				}								
				tmp2.clear();
				tmp2.insert(*it);
				tmp2.insert(*it2);
				int score = 0;
				int sz = (*it).size();
				for(int i=0; i< sz; i++){
					score = score + (int)((*it)[i]);
				}
				
				sz = (*it2).size();
				for(int i=0; i< sz; i++){
					score = score + (int)((*it2)[i]);
				}
				hash_table[score % HASH_BUCKET_SIZE].push_back(tmp2);
				support_count[tmp2]++;
			}
		}
		transaction = read_a_transaction(fin);
	}
	// prune itemsets in the buckets by minsup_count and whether the every single item in L1	
	int minsup_count = (minsup * ntransactions + 1e-7);
	for(int i=0; i < HASH_BUCKET_SIZE; i++){
		if(hash_table[i].size() >= minsup_count){
			SuperItemSet :: iterator it;
			for(int j=0; j < HASH_BUCKET_SIZE; j++){
				for(int m = 0; m < hash_table[j].size(); m++){
					res.insert(hash_table[j][m]);
				}
			}
		}			
	}

	cout << "DHP is done!" << endl;
	return res;
}

void generate_L2(FILE *fin, SuperItemSet candidate_itemsets){
	prune_candidates(candidate_itemsets);
	frequent_itemsets[2] = candidate_itemsets;
	prune_candidates(frequent_itemsets[2]);
	
	cout << "L2:" << frequent_itemsets[2].size() << endl;
	print_superitemset(frequent_itemsets[2]);

	double duration = ( clock() - st ) / (double) CLOCKS_PER_SEC;
    cout << "Time for L2: " << duration << endl;
	cout << "L"<< "2" << " " << "size:" << frequent_itemsets[2].size() << endl;
	total_time += duration;
	return;
}


void generate_Lk(FILE *fin){
	// generate L3 ~ LK
	for(int i=3; !frequent_itemsets[i-1].empty(); i++){
		cout << "start to generate L" << i  << endl;			
		st = clock();	

		// generate Lk
		SuperItemSet candidate_itemsets = generate_candidates(frequent_itemsets[i-1], i);
		count_itemsets_support(candidate_itemsets, fin);

		prune_candidates(candidate_itemsets);
		frequent_itemsets[i] = candidate_itemsets;
		prune_candidates(frequent_itemsets[i]);
		
		cout << "L" << i << ":" << frequent_itemsets[i].size() << endl;
		print_superitemset(frequent_itemsets[i]);
		double duration = ( clock() - st ) / (double) CLOCKS_PER_SEC;
	    cout << "Time for L" << i << ": " << duration << endl ;
		cout << "L"<< i << " " << "size:" << frequent_itemsets[i].size() << endl;
		total_time += duration;
	}
	return;
}
				

void generate_rules(){
	st = clock();
	cout << "start to generate rules" << endl;

	// sort ietmset by support count
	ItemSet p, q;
	support_count_order.clear();
	map<ItemSet, double> :: iterator it;
	for(it = support_count.begin(); it != support_count.end(); it++){
		support_count_order.push_back(make_pair(it->first, it->second));
	}
	sort(support_count_order.begin(), support_count_order.end(), sup_cmp);
	
	// gernerate association rules by greedy	
	int sz = support_count_order.size();
	for(int i=0; i<sz && nrules < k; i++){
		double prev_sup = support_count_order[i].second;
		ItemSet :: iterator it = support_count_order[i].first.begin();
		endit = support_count_order[i].first.end();
		partition(p, q, it);
		// iterate next
		while( i+1<sz && abs(prev_sup - support_count_order[i+1].second) < 1e-5){
			it = support_count_order[i+1].first.begin();
			endit = support_count_order[i+1].first.end();
			partition(p, q, it);
			i++;
		}
	}
	double duration = ( clock() - st ) / (double) CLOCKS_PER_SEC;
	cout << "Time for generate rules: " << duration << endl << endl;
	total_time += duration;

	return;
}

void print_rules(){
	cout << "start to print rules" << endl;
	map<key, rule, cmp> :: iterator itr;
	int counter = 0;
	for(itr = rules.begin(); itr != rules.end() && counter < k; itr++, counter++){
		ItemSet :: iterator itp = itr->second.p.begin();
		cout << *itp; itp++;
		for(; itp != itr->second.p.end(); itp++){
			cout << "," << *itp;
		}
		cout << "->";
		ItemSet :: iterator itq = itr->second.q.begin();
		cout << *itq; itq++;
		for(; itq != itr->second.q.end(); itq++){
			cout << "," << *itq;
		}
		cout << endl;
	}
	return;
}

int main(int argc, char **argv){

	cout << "Please enter the minimum support, confidence, top-k" << endl;
	cin >> minsup >> minconf >> k;
	cout << "Start to Apriori Algorithm" << endl;
    
	FILE* fin = fopen(argv[1], "r");

	generate_L1(fin);
	generate_L2(fin, generate_C2_by_DHP(fin));
	generate_Lk(fin);
	generate_rules();
	print_rules();
	cout << "Everything is done " << endl;
	cout << "Exec time:" << total_time << endl; 
	fclose(fin);

	return 0;
}
