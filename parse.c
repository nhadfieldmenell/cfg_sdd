#include <stdio.h>
#include <stdlib.h>
#include "sddapi.h"

/*
	Rule representation:
		rules is an array of 3-tuples
		if rules[i][0] == -1:
			rule(i) is of the form X->x
			rules[i][1] = X
			rules[i][2] = x
		else
			rule(i) is of the form X->AB
			rules[i][0] = X
			rules[i][1] = A
			rules[i][2] = B
		PUT ALL NON-TERMINAL RULES BEFORE ALL TERMINAL RULES (terminal rules have higher indexes)
			
	String is an array of integers, corresponding to the input string (each integer in string must be < terminal)
			
	  0 1 2 3 4 5
	0 X O O O O O
	1 X X O O O O
	2 X X X O O O
	3 X X X X O O
	4 X X X X X O
	5 X X X X X X
	

	# of literals = term*len + nonTerm*len*(len+1)/2
	first term*len literals:
		Terminal i corresponds to S(i/term,i%term)
	next nonTerm*len*(len+1)/2 correspond to non-terminals

	literal for T[i][j][k] = (j*(j+1)/2)*nonTerm+i*nonTerm+k + firstNon

	
	int nonTerm = 4;
	int term = 2;
	int nonRuleCount = 3;
	int termRuleCount = 2;
	int start = 3;
	int len = 4;
	
	AB
	CD
	EF
	GH
	   0    1    2    3
	0 AJKL
	1 MNOP ARST
	2 UVWX YZS8 9B12
	3 34S6 789T 1234 5B78
	  ABST
	
	
	
	int nonTerm = 7;
	int term = 2;
	int nonRuleCount = 6;
	int termRuleCount = 4;
	int start = 2;
	int len = 3;
	
	AB
	CD
	EF
	
	GHIJKLM
	NOPQRST UVWXYZ7
	8901234 5678901 2345678
	ABSTUXY
	0123456
	
	12
	23
	56
	
	7890123 10
	4567890 1234567 20
	8901234 5678901 2345678 30 40
	
	12
	23
	56
	78
	
	9012345 10
	6789012 3456789 20
	0123456 7890123 4567890 30 40 50
	1234567 8901234 5678901 2345678 60 70
	ABSTUXY
	
	
	int nonTerm = 3;
	int term = 2;
	int nonRuleCount = 3;
	int termRuleCount = 2;
	int start = 2;
	int len = 3;
	
	AB
	CD
	EF
	
	GHI
	JKL MNO
	PQR STU VWX
	
	aab
	
	A
	-A
	SSB
	
*/



SddNode* sddParsings(SddManager*m, int nonTerm, int term, int nonRules[][3], int termRules[][2], int nonRuleCount, int termRuleCount, int start, int len){
	SddNode* S[term][len];
	int i,j,k,index;
	
	for(j = 0; j < len; j++){
		for(i = 0; i < term; i++){
			S[i][j] = sdd_manager_literal(j*term+i+1,m);
			for(k = 0; k < term; k++){
				if (k != i){
					S[i][j] = sdd_conjoin(sdd_manager_literal(0-(j*term+k+1),m),S[i][j],m);
				}
			}
		}
	}
	
	int firstNon = term*len+1;
	SddNode* T[len][len][nonTerm];
	
	//set diagonal according to terminal rules
	for (index = 0;index < len; index++){
		for(k = 0; k < nonTerm; k++){
			T[index][index][k] = sdd_manager_false(m);
		}	
		for(i = 0; i < termRuleCount; i++){
			k = termRules[i][0];
			int termVal = termRules[i][1];
			T[index][index][k] = sdd_disjoin(T[index][index][k],S[termVal][index],m);
		}
		for(k = 0; k < nonTerm; k++){
			T[index][index][k] = sdd_conjoin(T[index][index][k],sdd_manager_literal((index*(index+1)/2)*nonTerm+index*nonTerm+k + firstNon,m),m);
			//printf("literalX %d\n",(index*(index+1)/2)*nonTerm+index*nonTerm+k + firstNon);
			for(j = 0; j < nonTerm; j++){
				if (j != k){
					T[index][index][k] = sdd_conjoin(T[index][index][k],sdd_manager_literal(0-((index*(index+1)/2)*nonTerm+index*nonTerm+j + firstNon),m),m);
				}
			}
		}
	}
	
	//printf("firstNon %d\n",firstNon);
	
	//*
	SddNode* empties[len][len];
	
	for (j = 1; j < len; j++){
		for (i = j-1; i >= 0; i--){
			empties[i][j] = sdd_manager_true(m);
			for(k = 0; k < nonTerm; k++){
				empties[i][j] = sdd_conjoin(empties[i][j],sdd_manager_literal(0-((j*(j+1)/2)*nonTerm+i*nonTerm+k + firstNon),m),m);
			}
		}
	}
	//*/
	
	for (j = 1; j < len; j++){
		for (i = j-1; i >= 0; i--){
			for(k = 0; k < nonTerm; k++){
				T[i][j][k] = sdd_manager_false(m);
			}
			for(index = 0; index < nonRuleCount; index++){
				int root = nonRules[index][0];
				int left = nonRules[index][1];
				int right = nonRules[index][2];
				int up;
				int east = i+1;
				for(up = i; up < j; up++){
					//printf("up,east: %d%d\n",up,east);
					SddNode* delta = sdd_conjoin(T[i][up][left],T[east][j][right],m);
					int midup, mideast, counter;
					for(midup = up+1;midup <= j;midup++){
						for(mideast = i; mideast < east;mideast++){
							if (midup != j || mideast != i){
								delta = sdd_conjoin(delta,empties[mideast][midup],m);
								/*
								for(counter = 0; counter < nonTerm; counter++){
									delta = sdd_conjoin(delta,sdd_manager_literal(0-((midup*(midup+1)/2)*nonTerm+mideast*nonTerm+counter + firstNon),m),m);
								}
								//*/
							}
						}
					}
					T[i][j][root] = sdd_disjoin(delta,T[i][j][root],m);
					east+=1;	
				}
			}
			for(k = 0; k < nonTerm; k++){
				//printf("literal: %d\n",(j*(j+1)/2)*nonTerm+i*nonTerm+k + firstNon);
				T[i][j][k] = sdd_conjoin(T[i][j][k],sdd_manager_literal((j*(j+1)/2)*nonTerm+i*nonTerm+k + firstNon,m),m);
				for(index = 0; index<nonTerm; index++){
					if (index != k){
						T[i][j][k] = sdd_conjoin(T[i][j][k],sdd_manager_literal(0-((j*(j+1)/2)*nonTerm+i*nonTerm+index + firstNon),m),m);
					}
				}
			}		
		}
	}
	
	return T[0][len-1][start];
}


int main(int argc, char** argv) {
	

	/*
	//0:A 1:B 2:S 3:T 4:U 5:X 6:Y
	int nonTerm = 7;
	int term = 2;
	int nonRuleCount = 6;
	int termRuleCount = 4;
	int start = 2;
	int len = 4;
	int nonRules[nonRuleCount][3];
	int termRules[termRuleCount][2];
	
	//S->XT
	nonRules[0][0] = 2;
	nonRules[0][1] = 5;
	nonRules[0][2] = 3;
	
	//S->UY
	nonRules[1][0] = 2;
	nonRules[1][1] = 4;
	nonRules[1][2] = 6;
	
	//X->AA
	nonRules[2][0] = 5;
	nonRules[2][1] = 0;
	nonRules[2][2] = 0;
	
	//Y->BB
	nonRules[3][0] = 6;
	nonRules[3][1] = 1;
	nonRules[3][2] = 1;
	
	//T->TB
	nonRules[4][0] = 3;
	nonRules[4][1] = 3;
	nonRules[4][2] = 1;
	
	//U->UA
	nonRules[5][0] = 4;
	nonRules[5][1] = 4;
	nonRules[5][2] = 0;
	
	//T->b
	termRules[0][0] = 3;
	termRules[0][1] = 1;
	
	//U->a
	termRules[1][0] = 4;
	termRules[1][1] = 0;
	
	//A->a
	termRules[2][0] = 0;
	termRules[2][1] = 0;

	//B->b
	termRules[3][0] = 1;
	termRules[3][1] = 1;


	//

	//2^(n-2) total models
	//pascal's triangle for parsings for a particular length
	//0:A 1:B 2:S; 0:a 1:b
		
	int nonTerm = 3;
	int term = 2;
	int nonRuleCount = 3;
	int termRuleCount = 2;
	int start = 2;
	int len = 9;
	int nonRules[nonRuleCount][3];
	int termRules[termRuleCount][2];
	
	//S->AS
	nonRules[0][0] = 2;
	nonRules[0][1] = 0;
	nonRules[0][2] = 2;
	
	//S->SB
	nonRules[1][0] = 2;
	nonRules[1][1] = 2;
	nonRules[1][2] = 1;
	
	//S->AS
	nonRules[2][0] = 2;
	nonRules[2][1] = 0;
	nonRules[2][2] = 1;
	
	//A->a
	termRules[0][0] = 0;
	termRules[0][1] = 0;
	
	//B->b
	termRules[1][0] = 1;
	termRules[1][1] = 1;

	//*/
	
	/*
	0 AB
	1 CD
	2 EF
	3 GH
	4 IJ
	5 KL
	6 MN
	7 OP
	*/
	//*
	//0:A 1:B 2:S 3:T 4:U 5:V 6:W 7:X 0:a 1:b
	
	int nonTerm = 8;
	int term = 2;
	int nonRuleCount = 11;
	int termRuleCount = 4;
	int start = 2;
	int len = 15;
	int nonRules[nonRuleCount][3];
	int termRules[termRuleCount][2];
	
	//S->AS
	nonRules[0][0] = 2;
	nonRules[0][1] = 0;
	nonRules[0][2] = 2;
	
	//S->BS
	nonRules[1][0] = 2;
	nonRules[1][1] = 1;
	nonRules[1][2] = 2;
	
	//S->AT
	nonRules[2][0] = 2;
	nonRules[2][1] = 0;
	nonRules[2][2] = 3;
	
	//T->AU
	nonRules[3][0] = 3;
	nonRules[3][1] = 0;
	nonRules[3][2] = 4;
	
	//T->BU
	nonRules[4][0] = 3;
	nonRules[4][1] = 1;
	nonRules[4][2] = 4;
	
	//U->AV
	nonRules[5][0] = 4;
	nonRules[5][1] = 0;
	nonRules[5][2] = 5;
	
	//U->BV
	nonRules[6][0] = 4;
	nonRules[6][1] = 1;
	nonRules[6][2] = 5;
	
	//V->AW
	nonRules[7][0] = 5;
	nonRules[7][1] = 0;
	nonRules[7][2] = 6;
	
	//V->BW
	nonRules[8][0] = 5;
	nonRules[8][1] = 1;
	nonRules[8][2] = 6;
	
	//W->AX
	nonRules[9][0] = 6;
	nonRules[9][1] = 0;
	nonRules[9][2] = 7;
	
	//W->BX
	nonRules[10][0] = 6;
	nonRules[10][1] = 1;
	nonRules[10][2] = 7;
	
	//X->a
	termRules[0][0] = 7;
	termRules[0][1] = 0;
	
	//X->b
	termRules[1][0] = 7;
	termRules[1][1] = 1;
	
	//A->a
	termRules[2][0] = 0;
	termRules[2][1] = 0;
	
	//B->b
	termRules[3][0] = 1;
	termRules[3][1] = 1;
	//*/
	
	

	// initialize manager
	SddLiteral var_count = term*len + nonTerm*len*(len+1)/2; // initial number of variables
	int auto_gc_and_minimize = 0; // disable (0) or enable (1) auto-gc & auto-min
	SddManager* m = sdd_manager_create(var_count,auto_gc_and_minimize);
	
	
	
	SddNode* returned = sddParsings(m,nonTerm,term,nonRules,termRules,nonRuleCount,termRuleCount,start,len);
	
	int count = var_count;
	//printf("varCount %d\n",count);
	
	//returned = sdd_condition(20,returned,m);
	SddNode* tester;
	int i;
	/*
	for(i = 1; i <= var_count;i++){
		tester = sdd_condition(i,returned,m);
		int modelCount = sdd_model_count(tester,m);
		printf("%d %d\n",i,modelCount);
	}
	*/
	/*
	int modelCount;
	for(i = 2; i < 10;i++){
		returned = sddParsings(m,nonTerm,term,nonRules,termRules,nonRuleCount,termRuleCount,start,i);
		int modelCount = sdd_model_count(returned,m);
		printf("count: %d\n",modelCount);
	}
	*/
	
	//for(i = 1; i <= len*2; i += 2) returned = sdd_condition(i,returned,m);
	
	returned = sdd_condition(1,returned,m);
	returned = sdd_condition(4,returned,m);
	returned = sdd_condition(5,returned,m);
	returned = sdd_condition(8,returned,m);
	returned = sdd_condition(10,returned,m);
	returned = sdd_condition(11,returned,m);
	returned = sdd_condition(13,returned,m);
	returned = sdd_condition(16,returned,m);
	
	//returned = sdd_condition(9,returned,m);
	int modelCount = sdd_model_count(returned,m);
	printf("count: %d\n",modelCount);
	
	
	//sdd_save_as_dot("cfgSdd.dot",returned);
	
	
	/*
	9012U45 10
	6789U12 A456789 20
	0123456 7890123 4B67890 30 40 50
	12S4567 8901234 567890Y 2B45678 60 70
	ABSTUXY
	20
	13
	
	*/

	int size = sdd_size(returned);
	printf("size: %d\n",size);
	
	sdd_save_as_dot("cfgSdd.dot",returned);
	
	
	// free manager
	sdd_manager_free(m);
	 
	return 0;
}