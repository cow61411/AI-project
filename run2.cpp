#include <iostream>
#include <string>
#include <cstdlib>
#include <fstream>

using namespace std;


int newrulecount = 1000;
bool firsttime = true;

struct Node
{
	string value;
	Node *left;
	Node *right;
	Node *parent;

	Node(string val)
	{
		this->value = val;
		this -> left = NULL;
		this -> right = NULL;
	}
};

int countParenthesis(string origin)
{
	if(origin[0] != '(')
		return 0;
	int count = 0 , i = 0;
	do
	{
		if(origin[i] == '(')
			count++;
		else if(origin[i] == ')')
			count--;
		i++;
	}while(count != 0);
	return i - 1;
}

string eliParenthesis(string origin)
{
	if(origin.size() != 1)
		if(countParenthesis(origin) == origin.size() - 1)
		{
			origin.erase(origin.begin() + origin.size() - 1);
			origin.erase(origin.begin());
		}
	return origin;
}

string eliSpace(string origin)
{
	while(origin.find(" ") != -1)
	{
		int temp = origin.find(" ");
		origin = origin.erase(temp , 1);
	}

	return origin;
}

string eliSymbolHelper(string origin , string target , string replace)
{
	int temp;
	while(origin.find(target) != -1)
	{
		temp = origin.find(target);
		origin.erase(temp , target.size());
		origin.insert(temp , replace);
	}
	return origin;
}

string eliSymbol(string origin)
{
	string temp = eliSymbolHelper(origin , "iff" , "1");
	temp = eliSymbolHelper(temp , "imp" , "2");
	temp = eliSymbolHelper(temp , "and" , "3");
	temp = eliSymbolHelper(temp , "or"  , "4");
	temp = eliSymbolHelper(temp , "neg" , "5");

	return temp;
}

class EST {

	private:
		Node *root;

		Node* duplicateTree(Node* origin , Node *parentnode)
		{
			if(origin == NULL)
				return NULL;
			Node *temp = new Node(origin -> value);
			temp -> parent = parentnode;
			temp -> right = duplicateTree(origin -> right , temp);
			temp -> left = duplicateTree(origin -> left , temp);
			return temp;
		}

		void eliIff(Node *root)
		{
			if(root == NULL)
				return;
			if(root -> value == "1")
			{
				root -> value = "3";
				Node *lefttemp = new Node("2");
				Node *righttemp = new Node("2");
				lefttemp -> left = root -> left;
				lefttemp -> left -> parent = lefttemp;
				lefttemp -> right = root -> right;
				lefttemp -> right -> parent = lefttemp;

				righttemp -> left = duplicateTree(root -> right , root);
				righttemp -> right = duplicateTree(root -> left , root);
				righttemp -> left -> parent = righttemp;
				righttemp -> right -> parent = righttemp;

				root -> left = lefttemp;
				root -> right = righttemp;
				root -> left -> parent = root;
				root -> right -> parent = root;
			}
			if(root -> left != NULL)
				eliIff(root -> left);
			if(root -> right != NULL)
				eliIff(root -> right);
		}

		void eliImp(Node *root)
		{
			if(root == NULL)
				return;
			if(root -> value == "2")
			{
				root -> value = "4";
				Node *temp = new Node("5");
				temp -> left = root -> left;
				temp -> left -> parent = temp;
				root -> left = temp;
				root -> left -> parent = root;
			}
			if(root -> right != NULL)
				eliImp(root -> right);
			if(root -> left != NULL)
				eliImp(root -> left);
		}

		void eliNeg(Node *root)
		{
			if(root == NULL)
				return;
			else if(root -> value == "5")
			{
				if(root -> left != NULL)
				{
					if(root -> left -> value == "5")
					{
						root -> parent -> left = root -> left -> left;
						root -> parent -> left -> parent = root -> parent;
					}
					else if(root -> left -> value == "3")
					{
						root -> value = "4";
						root -> left -> value = "5";
						Node *temp = new Node("5");
						temp -> left = root -> left -> right;
						temp -> left ->parent = temp;
						root -> left -> right = NULL;
						root -> right = temp;
						root -> right -> parent = root;
					}
					else if(root -> left -> value == "4")
					{
						root -> value = "3";
						root -> left -> value = "5";
						Node *temp = new Node("5");
						temp -> left = root -> left -> right;
						temp -> left ->parent = temp;
						root -> left -> right = NULL;
						root -> right = temp;
						root -> right -> parent = root;
					}
				}
			}
			if(root -> left != NULL)
				eliNeg(root -> left);
			if(root -> right != NULL)
				eliNeg(root -> right);
		}

		void distributivity(Node *root)
		{
			if(root == NULL)
				return;
			if(root -> value == "4")
			{
				if(root -> left != NULL)
				{
					if(root -> left -> value == "3")
					{
						Node *righttemp = new Node("4");
						root -> value = "3";
						root -> left -> value ="4";
						righttemp -> right = duplicateTree(root -> right , root);
						righttemp -> left = root -> left -> right;
						righttemp -> right -> parent = righttemp;
						righttemp -> left -> parent = righttemp;
						root -> left -> right = root -> right;
						root -> left -> right -> parent = root -> left;
						root -> right = righttemp;
						root -> right -> parent = root;
					}
				}
				if(root -> right != NULL)
				{
					if(root -> right -> value == "3")
					{
						Node *lefttemp = new Node("4");
						root -> value = "3";
						root -> right -> value ="4";
						lefttemp -> left = duplicateTree(root -> left , root);
						lefttemp -> right = root -> right -> left;
						lefttemp -> right -> parent = lefttemp;
						lefttemp -> left -> parent = lefttemp;
						root -> right -> left = root -> left;
						root -> right -> left -> parent = root -> right;
						root -> left = lefttemp;
						root -> left -> parent = root;
					}
				}
			}
			if(root -> left != NULL)
				distributivity(root -> left);
			if(root -> right != NULL)
				distributivity(root -> right);
		}

		void moveNeg(Node *root , Node *parentnode ,int dir)
		{
			if(root == NULL)
				return;
			if(root -> value == "5")
			{
				if(root -> left -> value == "1" || root -> left -> value == "2" || root -> left -> value == "3" || root -> left -> value == "4")
				{
					Node *temp = root -> left;
					while(temp -> left != NULL)
						temp = temp -> left;
					temp -> value = "neg (" + temp -> value;
					temp = root -> left;
					while(temp -> right != NULL)
						temp = temp -> right;
					temp -> value = temp -> value + ")";
				}
				else
					root -> left -> value = "neg " + root -> left -> value;
				if(parentnode != NULL)
				{
					if(dir == 0)
					{
						parentnode -> left = root -> left;
						parentnode -> left -> parent = parentnode;
					}
					else if(dir == 1)
					{
						parentnode -> right = root -> left;
						parentnode -> right -> parent = parentnode;
					}
					else if(dir == -1)
					{
						root = root -> left;
						root -> parent = NULL;
					}
				}
			}
			if(root -> left != NULL)
				moveNeg(root -> left , root , 0);
			if(root -> right != NULL)
				moveNeg(root -> right , root , 1);
		}

		void buildHelper(Node *root) {
			if(root -> value.size() == 1)
				return;
			root -> value = eliParenthesis(root -> value);
			if(root -> value[0] == '5')
			{
				bool judge = false;
				int i = 0;
				if(root -> value[1] != '(')
				{
					for(i = 0 ; i < root -> value.size() ; i++)
						if(root -> value[i] == '1' || root -> value[i] == '2' || root -> value[i] == '3' || root -> value[i] == '4')
						{
							judge = true;
							break;
						}
				}
				if(judge)
				{
					string temp;
					temp.assign(root -> value , 0 , i);
					root -> left = new Node(temp.assign(root -> value , 0 , i));
					root -> right = new Node(temp.assign(root -> value , i + 1 , root -> value.size() - i - 1));
					temp.assign(root -> value , i , 1);
					root -> value = temp;
					buildHelper(root -> left);
					buildHelper(root -> right);
				}
				else
				{
					string other = root -> value;
					other.erase(other.begin());
					root -> value = "5";
					root -> left = new Node(other);
					root -> left -> parent = root;
					buildHelper(root -> left);
				}
				return;
			}
			int loc = countParenthesis(root -> value);
			string temp;
			temp.assign(root -> value , 0 , loc + 1);
			root -> left = new Node(temp);
			root -> left -> parent = root;

			temp.assign(root -> value , loc + 2 , root -> value.size() - loc - 2);
			root -> right = new Node(temp);
			root -> right -> parent = root;

			temp.assign(root -> value , loc + 1 , 1);
			root -> value = temp;

			buildHelper(root -> left);
			buildHelper(root -> right);
		}

		string printHelperinside(Node *root) {
			string result;
			if (!root) return "";
			result += printHelperinside(root->left);
			if(root -> value == "1")
				result +=  "iff ";
			else if(root -> value == "2")
				result += "imp ";
			else if(root -> value == "3")
				result += "and ";
			else if(root -> value == "4")
				result +=  "or ";
			else if(root -> value != "5")
			{
				result += root->value;
				result += ' ';
			}
			result += printHelperinside(root->right);
			return result;
		}

		void printtest(Node *root) {
			if (root == NULL) return;
			if(root -> left != NULL)
				printtest(root->left);
			cout<<root->value<<' ';
			if(root -> right != NULL)
				printtest(root->right);
		}

		void getParenthesis(Node *root)
		{
			if(root == NULL)
				return;
			if(root -> value == "1" || root -> value == "2" || root -> value == "3" || root -> value == "4")
			{
				if(root -> left != NULL)
				{
					if(root -> left -> value == "1" || root -> left -> value == "2" || root -> left -> value == "3" || root -> left -> value == "4")
						if(root -> value != root -> left -> value)
						{
							Node *temp = root -> left;
							while(temp -> left != NULL)
								temp = temp -> left;
							temp -> value = "(" + temp -> value;
							temp = root -> left;
							while(temp -> right != NULL)
								temp = temp -> right;
							temp -> value = temp -> value + ")";
						}
				}
				if(root -> right != NULL)
				{
					if(root -> right -> value == "1" || root -> right -> value == "2" || root -> right -> value == "3" || root -> right -> value == "4")
						if(root -> value != root -> right -> value)
						{
							Node *temp = root -> right;
							while(temp -> left != NULL)
								temp = temp -> left;
							temp -> value = "(" + temp -> value;
							temp = root -> right;
							while(temp -> right != NULL)
								temp = temp -> right;
							temp -> value = temp -> value + ")";
						}
				}
			}
			getParenthesis(root -> left);
			getParenthesis(root -> right);
		}

		string printHelper(Node *root)
		{
			string result;
			moveNeg(root , NULL , -1);
			getParenthesis(root);
			result = printHelperinside(root);
			return result;
		}

	public:
		void add(string val) {
			root = new Node(val);
			this -> buildHelper(root);
		}

		void print() {
			printHelper(this->root);
			cout << endl;
		}

		string process()
		{
			string result;
			eliIff(this -> root);
			eliImp(this -> root);
			eliNeg(this -> root);
			distributivity(this -> root);
			result = printHelper(duplicateTree(this -> root , NULL));

			return result;
		}
};

string prob1(string origin)
{
	string result;
	origin = eliSymbol(origin);
	origin = eliSpace(origin);
	EST *est = new EST();
	est -> add(origin);
	result = est -> process();

	return result;
}

struct Rule
{
	int rulecount;
	string name;
	string neg;
	int priority;
	Rule *next;

	Rule(int count , string rulename , string negnum)
	{
		this -> rulecount = count;
		this -> name = rulename;
		this -> neg = negnum;
		this -> next = NULL;
		this -> priority = 0;
	}

	Rule(string rulename)
	{
		this -> name = rulename;
		this -> priority = 0;
		this -> next = NULL;
	}

	Rule(string rulename , int count)
	{
		this -> priority = 0;
		this -> name = rulename;
		this -> rulecount = count;
		this -> next = NULL;
	}
};

string eliSymbol_2(string origin)
{
	string temp = eliSymbolHelper(origin , "and" , " ");
	temp = eliSymbolHelper(temp , "(" , "");
	temp = eliSymbolHelper(temp , ")" , "");
	temp = eliSymbolHelper(temp , "or" , "");
	temp = eliSymbolHelper(temp , "neg" , "1");

	return temp;
}

string setrule(string origin)
{
	origin = eliSpace(origin);
	origin = eliSymbol_2(origin);
	return origin;
}

class List
{
	private:
		Rule *root;

		void addHelper(Rule *root , string value , int count)
		{
			while(root -> next != NULL)
				root = root -> next;
			root -> next = new Rule(value , count);
		}

		void printHelper(Rule *root , ofstream &output)
		{
			if(root == NULL)
				return;
			if(root -> rulecount != -1)
				output << "R" << root -> rulecount <<": ";
			else
				output << "XX: ";
			for(int i = 0 ; i < root -> name.size() ; i++)
			{
				if(root -> neg[i] == '1')
					output << "neg " << root -> name[i];
				else
					output << root -> name[i];
				if(i != root -> name.size() - 1)
					output << " or ";
			}
			output << endl;
			printHelper(root -> next , output);
		}

		void singleprintHelper(string name , string neg , ofstream &output)
		{
			for(int i = 0 ; i < name.size() ; i++)
			{
				if(neg[i] == '1')
					output << "neg " << name[i];
				else if(neg[i] == '0')
					output << name[i];
				if(i != name.size() - 1 && neg[i] != ' ')
					output << " or ";
			}
			output << endl;
		}

		void spanlistHelper(Rule *root)
		{
			if(root == NULL)
				return;
			int insidecount = 2;
			Rule *position = root;
			bool spaned = false;
			while(root -> name.find(" ") != -1)
			{
				spaned = true;
				int location = root -> name.find(" ");
				string result;
				result.assign(root -> name , 0 , location);
				Rule *temp = new Rule(result , root -> rulecount * 10 + insidecount);
				temp -> next = position -> next;
				position -> next = temp;
				position = position -> next;
				root -> name.erase(root -> name.begin() , root -> name.begin() + location + 1);
				insidecount++;
			}
			if(spaned)
				root -> rulecount = root -> rulecount * 10 + 1;
			spanlistHelper(root -> next);
		}

		void setNeg(Rule *root)
		{
			if(root == NULL)
				return;
			for(int i = 0 ; i < root -> name.size() ; i++)
			{
				if(root -> name[i] == '1')
				{
					root -> neg += "1";
					root -> name.erase(i , 1);
				}
				else
					root -> neg += "0";
			}
			setNeg(root -> next);
		}

		void majorproof(Rule * root , Rule *current ,string tname , char tneg , ofstream &output)
		{
			Rule *temp = root;
			string copycurname , target;
			bool judge;
			while(temp != NULL)
			{
				if(temp -> name.find(tname) != -1 && temp -> neg[ temp -> name.find(tname) ] != tneg)
				{
					if(temp -> priority != 1)
					{
						temp -> priority = 1;
						copycurname = temp -> name;
						for(int i = 0 ; i < copycurname.size() ; i++)
							if(copycurname[i] != tname[0])
							{
								target.assign(copycurname , i , 1);
								judge = elitarget(root , temp , target , temp -> neg[i] , output);
								if(!judge)
									majorproof(root , temp , target , temp -> neg[i] , output);
							}
						temp -> priority = 0;
						temp -> neg = eliSpace(temp -> neg);
						temp -> name = eliSpace(temp -> name);
						if(temp -> name.size() == 1)
						{
							string listname , listneg;
							char tempneg = temp -> neg[0];
							if(current -> name.find(temp -> name) != -1 && current -> neg[ current -> name.find(temp -> name) ] != tempneg)
							{
								output << "R" << current -> rulecount << " + R" << temp -> rulecount << "(canael " << tname << ")" << endl << "得到" << endl << "R" << newrulecount << ": ";
								current -> neg[current -> name.find(tname)] = ' ';
								current -> name[current -> name.find(tname)] = ' ';
								current -> rulecount = newrulecount;
								newrulecount+=1;
								listname = current -> name;
								listneg = current -> neg;
								listname = eliSpace(listname);
								listneg = eliSpace(listneg);
								singleprintHelper(listname , listneg , output);
								output << endl;
							}
						}
						temp -> priority = 0;
					}
				}
				temp = temp -> next;
			}
		}

		bool elitarget(Rule *root , Rule *current , string tname , char tneg , ofstream &output)
		{
			Rule *temp = root;
			string target;
			bool operated = false;
			while(temp != NULL)
			{
				if(temp -> name.find(tname) != -1 && temp -> neg[ temp -> name.find(tname) ] != tneg)
				{
					if(temp -> priority != 1)
					{
						if(temp -> name.size() == 1)
						{
							string listname , listneg;
							output << "R" << current -> rulecount << " + R" << temp -> rulecount << "(canael " << tname << ")" << endl << "得到" << endl << "R" << newrulecount << ": ";
							current -> neg[current -> name.find(tname)] = ' ';
							current -> name[current -> name.find(tname)] = ' ';
							current -> rulecount = newrulecount;
							newrulecount+=1;
							listname = current -> name;
							listneg = current -> neg;
							listname = eliSpace(listname);
							listneg = eliSpace(listneg);
							singleprintHelper(listname , listneg , output);
							output << endl;
							operated = true;
						}
					}
				}
				temp = temp -> next;
			}
			return operated;
		}

		void addsHelper(Rule *root , string tname , char tneg)
		{
			while(root != NULL)
				root = root -> next;
			string tempneg;
			tempneg[0] = tneg;
			root -> next = new Rule(-1 , tname , tempneg);
		}

		void checkHelper(Rule *root , ofstream &output)
		{
			Rule *target = root;
			Rule *temp = root;
			while(target != NULL)
			{
				if(target -> rulecount == -1)
					break;
				target = target -> next;
			}
			while(temp != NULL)
			{
				if(target -> name == temp -> name && target -> neg != temp -> neg)
				{
					output << "R" << temp -> rulecount << " + XX (cancel " << target -> name << ")" << endl << "得到" << endl << "空集合" << endl << endl << "所以 x 得證" << endl;
				}
				temp = temp -> next;
			}
		}



	public:
		void add(string value , int count)
		{
			if(root)
				this -> addHelper(root , value , count);
			else
				root = new Rule(value , count);
		}

		void addsingle(string tname , char tneg)
		{
			addsHelper(this -> root , tname , tneg);
		}

		void print(ofstream &output)
		{
			printHelper(this -> root , output);
		}

		void spanlist()
		{
			spanlistHelper(this -> root);
			setNeg(this -> root);
		}

		void check(ofstream &output)
		{
			checkHelper(this -> root , output);
		}

		void proof(string targetname , char targetneg , ofstream &output)
		{
			majorproof(this -> root , this -> root , targetname , targetneg , output);
		}
};

string computerule(string origin)
{
	string final;
	final = prob1(origin);
	return final;
}

int main(int argc , char **argv)
{
	ifstream input(argv[1]);
	ofstream output(argv[2]);
	string temp;
	List *rulelist = new List();
	int count = 1;
	string targetname;
	char targetneg;
	while(getline(input , temp))
	{
		if(temp[0] == 'X')
		{
			temp.assign(temp , temp.find(" ") + 1 , temp.size() - temp.find(" "));
			temp = computerule(temp);
			temp = setrule(temp);
			if(temp.size() == 1)
			{
				targetname = temp;
				targetneg = '1';
				temp = "1" + temp;
			}
			else
			{
				targetname.assign(temp , 1 , 1);
				targetneg = '0';
				temp.erase(temp.begin());
			}
			rulelist -> add(temp , -1);
		}
		else
		{
			temp.assign(temp , temp.find(" ") + 1 , temp.size() - temp.find(" "));
			temp = computerule(temp);
			temp = setrule(temp);
			rulelist -> add(temp , count);
			count++;
		}
	}
	rulelist -> spanlist();
	rulelist -> print(output);
	output << "============================" << endl;
	rulelist -> proof(targetname , targetneg , output);
	rulelist -> check(output);
	return 0;
}
