#include <iostream>
#include <math.h>
#include <string>
#include <fstream>

using namespace std;

//iff = 1
//imp = 2
//and = 3
//or  = 4
//not = 5

//templae <class T>
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

//template <class T>
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

		void printHelperinside(Node *root , ofstream &output) {
			if (!root) return;
			printHelperinside(root->left , output);
			if(root -> value == "1")
				output << "iff ";
			else if(root -> value == "2")
				output << "imp ";
			else if(root -> value == "3")
				output << "and ";
			else if(root -> value == "4")
				output << "or ";
			else if(root -> value != "5")
				output<<root->value<<' ';
			printHelperinside(root->right , output);
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

		void printHelper(Node *root , ofstream &output)
		{
			moveNeg(root , NULL , -1);
			getParenthesis(root);
			printHelperinside(root , output);
		}

	public:
		void add(string val) {
			root = new Node(val);
			this -> buildHelper(root);
		}

		/*void print() {
			printHelper(this->root);
			cout << endl;
		}*/

		void process(ofstream &output)
		{
			eliIff(this -> root);
			printHelper(duplicateTree(this -> root , NULL) , output);
			output << endl;
			eliImp(this -> root);
			printHelper(duplicateTree(this -> root , NULL) , output);
			output << endl;
			eliNeg(this -> root);
			printHelper(duplicateTree(this -> root , NULL) , output);
			output << endl;
			distributivity(this -> root);
			printHelper(duplicateTree(this -> root , NULL) , output);
			output << endl;
		}
};

int main(int argc , char **argv)
{
	ifstream input (argv[1]);
	//if(argc >= 2)
		ofstream output (argv[2]);
	//else
		//ofstream output ("prob1_result.txt");
	string origin;
	getline(input , origin);
	origin = eliSymbol(origin);
	origin = eliSpace(origin);
	EST *est = new EST();
	est -> add(origin);
	est -> process(output);
}
