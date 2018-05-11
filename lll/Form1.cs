using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.Text.RegularExpressions;
using System.IO;

namespace LexAnalysis
{
    public partial class Form1 : Form
    {

        public Form1()
        {     
            InitializeComponent();
        }


        public string viewText;
        public string[] inputText;
        
        //Переменные лексического анализатора
        #region
        public struct Var
        {
            public String name;
            public int val;
        }
        public struct Lex
        {
            public int type;
            public int id;
            public int line_id;
        };

        public const int MAX_WORD_LENGTH = 20;
        public const int VAR_ID = 0;
        public const int BEGIN_ID = 1;
        public enum LEX_TYPES { KEYWORD, OPERATOR, DELIM, CONSTANT, VAR };
        public enum LEX_ERROR_TYPES { NOTVAR, NBEGIN, UKEY, DVAR, LNID, RVAR, SYN }
        public static string[] KEYWORDS = { "var", "begin", "end", "for", "to", "end_for", "read", "write", "integer", "do" };
        public static string[] OPERATORS = { "+", "-", "*", "=" };
        public static string[] DELIMS = { ";", ")", "(", ",", ":" };
        public static string[] LEX_ERRORS = {"'var' section not found!", "'begin' section not found",
                                             "unknown keyword", "variable redefinition", "id name is to long",
                                             "unknown symbol", "reserved name used as variable name", "syntax error"};
        public List<Lex> lexs = new List<Lex>();
        public List<Var> vars = new List<Var>();
        public bool analysisOK = true;
        public bool varFind = false;
        public bool beginFind = false;
        #endregion

        //Переменные синтаксического анализатора
        #region
        private Stack<int> statesStack = new Stack<int>();
        //public LexAnalysis lex;
        public bool isAnalysisOk = true;
        private int SyntreeLevel = -1;
        public struct programTreeElement
        {
            public int type;
            public int id;
        }
        public List<List<programTreeElement>> programTree;
        public enum SYN_ERROR_TYPES
        {
            NVAR,
            VVAR,
            NQ,
            NE,
            NT,
            NBEG,
            SYN,
            NBO,
            IOMA,
            IOMD,
            NEQ,
            MBO,
            MBC,
            MF,
            MT,
            MED,
            MFV,
            MTE,
            MD,
            MFE,
            MO,
            NPE
        }
        public static string[] SYN_ERRORS = {"No var definition", "Missing ',' or ':' in vars definition",
"Missing ','","Missing ';'", "No variable type (integer)", "No 'begin' keyword",
"Syntax error", "Missing '('","I/O missing argument", "I/O missing ',' or ')'", 
"Missing '='", "Missing '('", "Missing ')'", "Missing 'for'", "Missing 'to'",
"Missing 'end_for'", "Missing 'for' variable", "Missing 'to' expression",
"Missing 'do'", "Missing 'for' expression", "Missing operator","No 'end' keyword"};
        public enum STATES_TYPES
        {
            INIT,//init state
            VAR,//INIT + "var", wait for VAR_GET, else ERROR NO VARS DEF
            VAR_GET,//VAR + "variable" (OR VAR_CONT + "variable") will wait for ',' or ':', else ERROR MISSING ':' or ','
            VAR_CONT, //VAR_GET + ",", will wait for "variable", else ERROR MISSING VAR DEF 
            VAR_TYPE_DELIM, //VAR_GET + ":", will wait for "integer", else ERROR MISSING VAR TYPE 
            VAR_TYPE,//VAR_TYPE_DELIM + "integer", will wait for ";", else ERROR MISSING ';'
            VAR_SET,//VAR_TYPE + ';'
            READ_WRITE, //EXPR _DONE + "write" or "read"
            READ_WRITE_O,//READ_WRITE + "(", else ERROR MISSING '('
            READ_WRITE_ARG,//READ_WRITE_O + "var" (OR WRITE_CONT + "var"), wait for ")" or ",", else I/O ERROR - BAD ARG
            READ_WRITE_ARG_CONT,//READ_WRITE_VAR + ",", wait for "var", else MISSING I/O ARG
            READ_WRITE_C,//WRITE_ARG + ')', else ERROR MISSING ')'
            EXPR_DONE, //READ_WRITE_C + ';', VAR_EXPR + ';', VAR_SET + "begin", VAR_EXPR_C + ";"
            BEGIN_VAR_EXPR, //EXPR_DONE + "variable" 
            EQ_VAR_EXPR, //BEGIN_VAR_EXPR + "=", else ERROR missing '=' 
            VAR_EXPR, //EQ_VAR_EXPR + "constant" or EQ_VAR_EXPR + "variable", VAR_EXPR_SIGN + "variable", "constant"
            VAR_EXPR_SIGN, //EQ_VAR_EXPR, VAR_EXPR + "-","+","*"
            VAR_EXPR_O,//EQ_VAR_EXPR + "(", VAR_EXPR_SIGN + "("
            VAR_EXPR_C,//VAR_EXPR + ")"
            BEGIN_FOR_EXPR,
            FOR,
            TO,
            DO,
            END_FOR,
            END// finish state - program is OK 
        };
        public enum LEXEM_CODES
        {
            VAR = 0,//var
            Q = 3,//,
            E = 0,//;
            EQ = 3,//=
            BEG = 1,//begin
            END = 2,//end
            INT = 8,//integer
            D = 4,//:
            W = 7,//write
            R = 6,//read
            BO = 2,//(
            BC = 1,//)
            MIN = 1,//-
            PLUS = 0,//+
            MUL = 2,//*
            FOR = 3,
            TO = 4,
            DO = 9,
            END_FOR = 5
        }
        #endregion

        //Переменные интерпретатора
        #region
        //private SynAnalysis syn;
        private int treeLevel;
        public struct for_struct
        {
            public int var_id;
            public int check_val;
            public int body_level;
        }
        public Stack<for_struct> loops;
        #endregion

        private void button1_Click(object sender, EventArgs e)
        {
            List<String> programText = new List<string>();
            
            for (int i = 0; i < textBox1.TextLength; i++)
            {
                programText.Add(textBox1.Text);
            }
            //Запуск лексического анализатора
            listBox1.Items.Clear();
            listBox1.Items.Add("Lexical analysis of code...");
            for (int line_id = 0; line_id < programText.Count; line_id++)
                doLine(prepareLine(programText[line_id]), line_id);
            if (!varFind)
                writeErrorToLog((int)LEX_ERROR_TYPES.NOTVAR);
            if (!beginFind)
                writeErrorToLog((int)LEX_ERROR_TYPES.NBEGIN);
            listBox1.Items.Add("Lexical analysis is complete!");
                        
            //Запуск синтаксического анализатора
            //listBox1.Items.Clear();
            programTree = new List<List<programTreeElement>>();
            listBox1.Items.Add("Parsing code...");
            doSynAnalysis();
            listBox1.Items.Add("Parsing completed!");

            //Запуск интерпретатора
            treeLevel = 0;
            loops = new Stack<for_struct>();
            for (int i = 0; i <= programTree.Count() - 1; i++)
            {
                programTree[i] = infixToPostfix(programTree[i]);
            }
            Intepreter();
        }

        //Листинг лексичекого анализатора
        #region
        public String getVarName(int id)
        {
            return vars[id].name;
        }
        public int getVarVal(int id)
        {
            return vars[id].val;
        }
        private void writeErrorToLog(int errorCode, int line_id)
        {
            listBox1.Items.Add("Error: " + LEX_ERRORS[errorCode] + ", line: " + line_id);
            analysisOK = false;
        }
        private void writeErrorToLog(String word, int errorCode, int line_id)
        {
            listBox1.Items.Add("Error: " + LEX_ERRORS[errorCode] + " - '" + word + "'" + ", line: " + line_id);
            analysisOK = false;
        }
        private void writeErrorToLog(int errorCode)
        {
            listBox1.Items.Add("Error: " + LEX_ERRORS[errorCode]);
            analysisOK = false;
        }
        private void addLex(int type, int id, int line_id)
        {
            Lex lex;
            lex.type = type;
            lex.id = id;
            lex.line_id = line_id;
            lexs.Add(lex);
        }
        private void addVar(String name, int val)
        {
            Var var;
            var.name = name;
            var.val = val;
            vars.Add(var);
        }
        public void setVarVal(int id, int val)
        {
            Var var;
            var.name = vars[id].name;
            var.val = val;
            vars[id] = var;
        }
        private bool checkKeyword(String word, int line_id)
        {
            for (int keyword_id = 0; keyword_id < KEYWORDS.Length; keyword_id++)
            {
                if (word == KEYWORDS[keyword_id])
                {
                    addLex((int)LEX_TYPES.KEYWORD, keyword_id, line_id);
                    if (keyword_id == VAR_ID)
                        varFind = true;
                    if (keyword_id == BEGIN_ID)
                        beginFind = true;
                    return true;
                }
            }
            return false;
        }
        private bool checkOperator(String word, int line_id)
        {
            for (int operation_id = 0; operation_id < OPERATORS.Length; operation_id++)
            {
                if (word == OPERATORS[operation_id])
                {
                    addLex((int)LEX_TYPES.OPERATOR, operation_id, line_id);
                    return true;
                }
            }
            return false;
        }
        private bool checkDelim(String word, int line_id)
        {
            for (int delim_id = 0; delim_id < DELIMS.Length; delim_id++)
            {
                if (word == DELIMS[delim_id])
                {
                    addLex((int)LEX_TYPES.DELIM, delim_id, line_id);
                    return true;
                }
            }
            return false;
        }
        private bool checkConst(String word, int line_id)
        {
            int val;
            if (!int.TryParse(word, out val))
                return false;
            addLex((int)LEX_TYPES.CONSTANT, val, line_id);
            return true;
        }
        private bool checkVar(String word, int line_id)
        {
            Regex regex = new Regex(@"\b[a-z]+");
            if (!regex.IsMatch(word))
                return false;
            for (int var_id = 0; var_id < vars.Count(); var_id++)
                if (word == vars[var_id].name)
                {
                    if (!beginFind && this.varFind)
                    {
                        writeErrorToLog(word, (int)LEX_ERROR_TYPES.DVAR, line_id);
                        return false;
                    }
                    addLex((int)LEX_TYPES.VAR, var_id, line_id);
                    return true;
                }
            if (!beginFind && this.varFind)
            {
                addVar(word, 0);
                addLex((int)LEX_TYPES.VAR, vars.Count() - 1, line_id);
                return true;
            }
            return false;
        }
        private void doWord(String word, int line_id)
        {
            if (word == "")
                return;
            if (word.Length > MAX_WORD_LENGTH)
            {
                writeErrorToLog(word, (int)LEX_ERROR_TYPES.LNID, line_id);
                return;
            }
            while (true)
            {
                if (checkKeyword(word, line_id))
                    break;
                if (checkOperator(word, line_id))
                    break;
                if (checkDelim(word, line_id))
                    break;
                if (checkConst(word, line_id))
                    break;
                if (checkVar(word, line_id))
                    break;
                writeErrorToLog(word, (int)LEX_ERROR_TYPES.UKEY, line_id);
                break;
            }
        }
        public void doLine(string line, int line_id)
        {
            String[] words = line.Split(' ');
            foreach (String word in words)
                doWord(word, line_id);
        }
        public String prepareLine(string line)
        {
            foreach (String delim in DELIMS)
                line = line.Replace(delim, " " + delim + " ");
            foreach (String oper in OPERATORS)
                line = line.Replace(oper, " " + oper + " ");
            Regex regex = new Regex(@"\s+");
            return regex.Replace(line, " ").ToLowerInvariant();
        }

        #endregion

        //Листинг синтаксического анализатора
        #region
       
        private void SynWriteErrorToLog(int errorCode, int line_id)
        {
            listBox1.Items.Add("Error: " + SYN_ERRORS[errorCode] + ", line: " + line_id);
            isAnalysisOk = false;
        }
        public void addNewTreeLevel()
        {
            programTree.Add(new List<programTreeElement>());
            SyntreeLevel++;
        }
        public void addToCurrentTreeLevel(int id, int type)
        {
            programTreeElement elem;
            elem.id = id;
            elem.type = type;
            List<programTreeElement> currentTreeLevel = this.programTree[SyntreeLevel];
            currentTreeLevel.Add(elem);
        }
        
        public void doSynAnalysis()
        {
            statesStack.Push((int)STATES_TYPES.INIT);
            int lexsId = 0;
            while (isAnalysisOk)
            {
                int currentState = statesStack.Pop();
                if (lexs.Count - 1 < lexsId)
                {
                    if (currentState != (int)STATES_TYPES.END)
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NPE, lexs[lexs.Count - 1].line_id);
                    break;
                }
                if (currentState == (int)STATES_TYPES.END)
                {
                    //listBox2.Items.Add("Синтаксический анализ успешно завершен!");
                    break;
                }
                int lexType = lexs[lexsId].type;
                int lexId = lexs[lexsId].id;
                switch (currentState)
                {
                    case ((int)STATES_TYPES.INIT):
                        if (lexType == (int)LEX_TYPES.KEYWORD && lexId == (int)LEXEM_CODES.VAR)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NVAR, lexs[lexsId].line_id);
                        
                        break;
                    case ((int)STATES_TYPES.VAR):
                        if (lexType == (int)LEX_TYPES.VAR)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_GET);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NVAR, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.VAR_GET):
                        if (lexType == (int)LEX_TYPES.DELIM && lexId == (int)LEXEM_CODES.Q)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_CONT);
                            break;
                        }
                        if (lexType == (int)LEX_TYPES.DELIM && lexId == (int)LEXEM_CODES.D)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_TYPE_DELIM);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.VVAR, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.VAR_TYPE_DELIM):
                        if (lexType == (int)LEX_TYPES.KEYWORD && lexId == (int)LEXEM_CODES.INT)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_TYPE);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NT, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.VAR_TYPE):
                        if (lexType == (int)LEX_TYPES.DELIM && lexId == (int)LEXEM_CODES.E)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_SET);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NE, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.VAR_CONT):
                        if (lexType == (int)LEX_TYPES.VAR)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_GET);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NVAR, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.VAR_SET):
                        if (lexId == (int)LEXEM_CODES.BEG && lexType == (int)LEX_TYPES.KEYWORD)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.EXPR_DONE);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NBEG, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.EXPR_DONE):
                        if (lexId == (int)LEXEM_CODES.END && lexType == (int)LEX_TYPES.KEYWORD)
                        {
                            if (statesStack.Count == 0)
                            {
                                statesStack.Push((int)STATES_TYPES.END);
                                break;
                            }
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MED, lexs[lexsId].line_id);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.END_FOR && lexType == (int)LEX_TYPES.KEYWORD)
                        {
                            statesStack.Push((int)STATES_TYPES.END_FOR);
                            addNewTreeLevel();
                            addToCurrentTreeLevel(lexId, lexType);
                            break;
                        }
                        if ((lexId == (int)LEXEM_CODES.W || lexId == (int)LEXEM_CODES.R) && lexType == (int)LEX_TYPES.KEYWORD)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.READ_WRITE);
                            addNewTreeLevel();
                            addToCurrentTreeLevel(lexId, lexType);
                            break;
                        }
                        if (lexType == (int)LEX_TYPES.VAR)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.BEGIN_VAR_EXPR);
                            addNewTreeLevel();
                            addToCurrentTreeLevel(lexId, lexType);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.FOR && lexType == (int)LEX_TYPES.KEYWORD)
                        {
                            lexsId++;
                            addNewTreeLevel();
                            addToCurrentTreeLevel(lexId, lexType);
                            statesStack.Push((int)STATES_TYPES.BEGIN_FOR_EXPR);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.SYN, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.BEGIN_FOR_EXPR):
                        if (lexType == (int)LEX_TYPES.VAR)
                        {
                            addNewTreeLevel();
                            addToCurrentTreeLevel(lexId, lexType);
                            statesStack.Push((int)STATES_TYPES.FOR);
                            statesStack.Push((int)STATES_TYPES.BEGIN_VAR_EXPR);
                            lexsId++;
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.MFV, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.READ_WRITE):
                        if (lexId == (int)LEXEM_CODES.BO && lexType == (int)LEX_TYPES.DELIM)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.READ_WRITE_O);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NBO, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.READ_WRITE_O):
                        if (lexType == (int)LEX_TYPES.VAR)
                        {
                            lexsId++;
                            addToCurrentTreeLevel(lexId, lexType);
                            statesStack.Push((int)STATES_TYPES.READ_WRITE_ARG);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.IOMA, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.READ_WRITE_ARG):
                        if (lexId == (int)LEXEM_CODES.Q && lexType == (int)LEX_TYPES.DELIM)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.READ_WRITE_ARG_CONT);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.BC && lexType == (int)LEX_TYPES.DELIM)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.READ_WRITE_C);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.IOMD, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.READ_WRITE_ARG_CONT):
                        if (lexType == (int)LEX_TYPES.VAR)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.READ_WRITE_ARG);
                            addToCurrentTreeLevel(lexId, lexType);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.IOMA, lexs[lexsId].line_id);
                        break;

                    case ((int)STATES_TYPES.READ_WRITE_C):
                        if (lexId == (int)LEXEM_CODES.E && lexType == (int)LEX_TYPES.DELIM)
                        {
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.EXPR_DONE);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NE, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.BEGIN_VAR_EXPR):
                        if (lexId == (int)LEXEM_CODES.EQ && lexType == (int)LEX_TYPES.OPERATOR)
                        {
                            statesStack.Push((int)STATES_TYPES.EQ_VAR_EXPR);
                            lexsId++;
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.NEQ, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.EQ_VAR_EXPR):
                        if (lexId == (int)LEXEM_CODES.BO && lexType == (int)LEX_TYPES.DELIM)
                        {
                            addToCurrentTreeLevel(lexId, lexType);
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR_O);
                            statesStack.Push((int)STATES_TYPES.EQ_VAR_EXPR);
                            lexsId++;
                            break;
                        }
                        if (lexType == (int)LEX_TYPES.CONSTANT || lexType == (int)LEX_TYPES.VAR)
                        {
                            addToCurrentTreeLevel(lexId, lexType);
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.MIN && lexType == (int)LEX_TYPES.OPERATOR)
                        {
                            addToCurrentTreeLevel(-1, (int)LEX_TYPES.CONSTANT);
                            addToCurrentTreeLevel((int)LEXEM_CODES.MUL, (int)LEX_TYPES.OPERATOR);
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR_SIGN);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.SYN, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.VAR_EXPR_C):
                        if (statesStack.Count == 0)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBO, lexs[lexsId].line_id);
                            break;
                        }
                        if (statesStack.Pop() != (int)STATES_TYPES.VAR_EXPR_O)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBO, lexs[lexsId].line_id);
                            break;
                        }
                        statesStack.Push((int)STATES_TYPES.VAR_EXPR);
                        break;
                    case ((int)STATES_TYPES.VAR_EXPR):
                        if ((lexId == (int)LEXEM_CODES.MIN || lexId == (int)LEXEM_CODES.PLUS || lexId == (int)LEXEM_CODES.MUL) && lexType == (int)LEX_TYPES.OPERATOR)
                        {
                            addToCurrentTreeLevel(lexId, lexType);
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR_SIGN);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.E && lexType == (int)LEX_TYPES.DELIM)
                        {
                            if (statesStack.Count > 0)
                            {
                                currentState = statesStack.Peek();
                                if (currentState == (int)STATES_TYPES.VAR_EXPR_O)
                                {
                                    SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBC, lexs[lexsId].line_id);
                                    break;
                                }
                                if (currentState == (int)STATES_TYPES.VAR_EXPR_C)
                                {
                                    SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBO, lexs[lexsId].line_id);
                                    break;
                                }
                            }
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.EXPR_DONE);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.TO && lexType == (int)LEX_TYPES.KEYWORD)
                        {
                            addNewTreeLevel();
                            addToCurrentTreeLevel(-1, (int)LEX_TYPES.VAR);
                            statesStack.Push((int)STATES_TYPES.TO);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.DO && lexType == (int)LEX_TYPES.KEYWORD)
                        {
                            statesStack.Push((int)STATES_TYPES.DO);
                            break;
                        }

                        if (lexId == (int)LEXEM_CODES.BC && lexType == (int)LEX_TYPES.DELIM)
                        {
                            addToCurrentTreeLevel(lexId, lexType);
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR_C);
                            lexsId++;
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.SYN, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.DO):
                        if (statesStack.Count == 0)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MT, lexs[lexsId].line_id);
                            break;
                        }
                        currentState = statesStack.Pop();

                        if (currentState == (int)STATES_TYPES.VAR_EXPR_O)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBC, lexs[lexsId].line_id);
                            break;
                        }

                        if (currentState == (int)STATES_TYPES.VAR_EXPR_C)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBO, lexs[lexsId].line_id);
                            break;
                        }
                        if (currentState != (int)STATES_TYPES.TO)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MT, lexs[lexsId].line_id);
                            break;
                        }
                        statesStack.Push((int)STATES_TYPES.DO);
                        statesStack.Push((int)STATES_TYPES.EXPR_DONE);
                        lexsId++;
                        break;
                    case ((int)STATES_TYPES.VAR_EXPR_SIGN):
                        if (lexType == (int)LEX_TYPES.VAR || lexType == (int)LEX_TYPES.CONSTANT)
                        {
                            addToCurrentTreeLevel(lexId, lexType);
                            lexsId++;
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR);
                            break;
                        }
                        if (lexId == (int)LEXEM_CODES.BO && lexType == (int)LEX_TYPES.DELIM)
                        {
                            addToCurrentTreeLevel(lexId, lexType);
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR_O);
                            statesStack.Push((int)STATES_TYPES.EQ_VAR_EXPR);
                            lexsId++;
                            break;
                        }
                        if (lexType == (int)LEX_TYPES.OPERATOR && lexId == (int)LEXEM_CODES.MIN)
                        {
                            lexsId++;
                            addToCurrentTreeLevel(-1, (int)LEX_TYPES.CONSTANT);
                            addToCurrentTreeLevel((int)LEXEM_CODES.MUL, (int)LEX_TYPES.OPERATOR);
                            statesStack.Push((int)STATES_TYPES.VAR_EXPR_SIGN);
                            break;
                        }
                        SynWriteErrorToLog((int)SYN_ERROR_TYPES.SYN, lexs[lexsId].line_id);
                        break;
                    case ((int)STATES_TYPES.END_FOR):
                        if (statesStack.Count == 0)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MD, lexs[lexsId].line_id);
                            break;
                        }
                        if (statesStack.Pop() != (int)STATES_TYPES.DO)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MD, lexs[lexsId].line_id);
                            break;
                        }
                        lexsId++;
                        statesStack.Push((int)STATES_TYPES.EXPR_DONE);
                        break;
                    case ((int)STATES_TYPES.TO):
                        if (statesStack.Count == 0)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MF, lexs[
                            lexsId].line_id);
                            break;
                        }
                        currentState = statesStack.Pop();
                        if (currentState == (int)STATES_TYPES.VAR_EXPR_O)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBC, lexs[lexsId].line_id);
                            break;
                        }
                        if (currentState == (int)STATES_TYPES.VAR_EXPR_C)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MBO, lexs[lexsId].line_id);
                            break;
                        }
                        if (currentState != (int)STATES_TYPES.FOR)
                        {
                            SynWriteErrorToLog((int)SYN_ERROR_TYPES.MF, lexs[lexsId].line_id);
                            break;
                        }
                        statesStack.Push((int)STATES_TYPES.TO);
                        statesStack.Push((int)STATES_TYPES.EQ_VAR_EXPR);
                        lexsId++;
                        break;
                }
            }
        }
        #endregion

        //Листинг интерпретатора
        #region
        public static DialogResult InputBox(string title, string promptText, ref string value)
        {
            Form1 form = new Form1();
            Label label = new Label();
            TextBox textBox = new TextBox();
            Button buttonOk = new Button();
            form.Text = title;
            label.Text = promptText;
            textBox.Text = value;
            buttonOk.Text = "OK";
            label.SetBounds(9, 20, 372, 13);
            textBox.SetBounds(12, 36, 372, 20);
            buttonOk.SetBounds(228, 72, 75, 23);
            buttonOk.DialogResult = DialogResult.OK;
            label.AutoSize = true;
            textBox.Anchor = textBox.Anchor | AnchorStyles.Right;
            buttonOk.Anchor = AnchorStyles.Bottom | AnchorStyles.Right;
            form.ClientSize = new Size(396, 107);
            form.Controls.AddRange(new Control[] { label, textBox, buttonOk });
            form.ClientSize = new Size(Math.Max(300, label.Right + 10), form.ClientSize.Height);
            form.FormBorderStyle = FormBorderStyle.FixedDialog;
            form.StartPosition = FormStartPosition.CenterScreen;
            form.MinimizeBox = false;
            form.MaximizeBox = false;
            form.AcceptButton = buttonOk;
            DialogResult dialogResult = form.ShowDialog();
            value = textBox.Text;
            return dialogResult;
        }
        public bool showRead()
        {
            if (treeLevel > programTree.Count() - 1)
                return false;
            List<programTreeElement> level = programTree[treeLevel];
            programTreeElement elem = level[0];
            if (elem.type != (int)LEX_TYPES.OPERATOR && elem.id != (int)LEXEM_CODES.R)
                return true;
            String msg = "";
            for (int i = 1; i <= level.Count() - 1; i++)
            {
                elem = level[i];
                msg += getVarName(elem.id) + " ";
            }
            String res = "";
            if (DialogResult.OK == InputBox("Input vars values", msg, ref res))
            {
                String[] vals = res.Split(' ');
                for (int i = 1; i <= level.Count() - 1; i++)
                {
                    elem = level[i];
                    int val;
                    if (!int.TryParse(vals[i - 1], out val))
                    {
                        MessageBox.Show
                        (
                        "Non integer var value",
                        "Error",
                        MessageBoxButtons.OK,
                        MessageBoxIcon.Error
                        );
                        return false;
                    }
                    setVarVal(elem.id, val);
                }
                treeLevel++;
                return true;
            }
            return true;
        }
        public bool showWrite()
        {
            if (treeLevel > programTree.Count() - 1)
                return false;
            List<programTreeElement> level = programTree[treeLevel];
            programTreeElement elem = level[0];
            if (elem.type != (int)LEX_TYPES.OPERATOR && elem.id != (int)LEXEM_CODES.W)
                return true;
            String msg = "Result: ";
            for (int i = 1; i <= level.Count() - 1; i++)
            {
                elem = level[i];
                msg += getVarName(elem.id) + "= " + getVarVal(elem.id) + " ";
            }
            MessageBox.Show(msg, "Write vars",
            MessageBoxButtons.OK,
            MessageBoxIcon.Information);
            treeLevel++;
            return true;
        }
        public int getExprVal()
        {
            List<programTreeElement> level = programTree[treeLevel];
            programTreeElement elem;
            Stack<int> exprVals = new Stack<int>();
            for (int i = 1; i <= level.Count() - 1; i++)
            {
                elem = level[i];
                if (elem.type == (int)LEX_TYPES.VAR)
                {
                    exprVals.Push(getVarVal(elem.id));
                    continue;
                }
                if (elem.type == (int)LEX_TYPES.CONSTANT)
                {
                    exprVals.Push(elem.id);
                    continue;
                }
                int right = exprVals.Pop();
                int left = exprVals.Pop();
                switch (elem.id)
                {
                    case (int)LEXEM_CODES.PLUS:
                        exprVals.Push(left + right);
                        break;
                    case (int)LEXEM_CODES.MIN:
                        exprVals.Push(left - right);
                        break;
                    case (int)LEXEM_CODES.MUL:
                        exprVals.Push(left * right);
                        break;
                }
            }
            return exprVals.Pop();
        }
        public bool varAssign()
        {
            if (treeLevel > programTree.Count() - 1)
                return false;
            List<programTreeElement> level = programTree[treeLevel];
            programTreeElement elem = level[0];
            if (elem.type != (int)LEX_TYPES.VAR)
                return true;
            setVarVal(elem.id, getExprVal());
            treeLevel++;
            return true;
        }
        public bool getFor()
        {
            if (treeLevel > programTree.Count() - 1)
                return false;
            List<programTreeElement> level = programTree[treeLevel];
            programTreeElement elem = level[0];
            if (elem.type != (int)LEX_TYPES.KEYWORD)
                return true;
            if (elem.id != (int)LEXEM_CODES.FOR)
                return true;
            for_struct fs;
            treeLevel++;
            level = programTree[treeLevel];
            elem = level[0];
            fs.var_id = elem.id;
            setVarVal(elem.id, getExprVal());
            treeLevel++;
            level = programTree[treeLevel];
            elem = level[0];
            fs.check_val = getExprVal();
            treeLevel++;
            fs.body_level = treeLevel;
            loops.Push(fs);
            return true;
        }
        public bool getEndFor()
        {
            if (treeLevel > programTree.Count() - 1)
                return false;
            List<programTreeElement> level = programTree[treeLevel];
            programTreeElement elem = level[0];
            if (elem.type != (int)LEX_TYPES.KEYWORD)
                return true;
            if (elem.id != (int)LEXEM_CODES.END_FOR)
                return true;
            for_struct fs = loops.Pop();
            int var_val;
            if ((var_val = getVarVal(fs.var_id)) < fs.check_val)
            {
                treeLevel = fs.body_level;
                setVarVal(fs.var_id, ++var_val);
                loops.Push(fs);
                return true;
            }
            treeLevel++;
            return true;
        }
        private void Intepreter()
        {
            while (true)
            {
                if (!showRead())
                    break;
                if (!showWrite())
                    break;
                if (!varAssign())
                    break;
                if (!getFor())
                    break;
                if (!getEndFor())
                    break;
            }
            listBox1.Items.Add("Interpretation OK");
        }
        #endregion

        //Постфиксная запись
        #region
        private static Stack<programTreeElement> operatorsStack = new Stack<programTreeElement>();
        private static int getOpPriority(programTreeElement elem)
        {
            if (elem.id == (int)LEXEM_CODES.MUL && elem.type == (int)LEX_TYPES.OPERATOR)
                return 3;
            if ((elem.id == (int)LEXEM_CODES.MIN || elem.id == (int)LEXEM_CODES.PLUS) && elem.type == (int)LEX_TYPES.OPERATOR)
                return 2;
            //if(elem.type == LexAnalysis.LEX_TYPES.DELIM)
            return 1;
        }
        public static List<programTreeElement> infixToPostfix(List<programTreeElement> expression)
        {
            operatorsStack.Clear();
            List<programTreeElement> result = new List<programTreeElement>();
            programTreeElement elem = expression[0];
            if (elem.type != (int)LEX_TYPES.VAR)
                return expression;
            result.Add(elem);
            for (int i = 1; i <= expression.Count() - 1; i++)
            {
                elem = expression[i];
                if (elem.id == (int)LEXEM_CODES.BC && elem.type == (int)LEX_TYPES.DELIM) // Если очеpедной символ - ')'
                {
                    while (true)
                    {
                        programTreeElement pop = operatorsStack.Pop();
                        if (pop.id == (int)LEXEM_CODES.BO && pop.type == (int)LEX_TYPES.DELIM)
                            break;
                        result.Add(pop);
                    }
                    continue;
                }
                if (elem.type == (int)LEX_TYPES.VAR || elem.type == (int)LEX_TYPES.CONSTANT)
                {
                    result.Add(elem);
                    continue;
                }
                if (elem.id == (int)LEXEM_CODES.BO && elem.type == (int)LEX_TYPES.DELIM)
                {
                    operatorsStack.Push(elem);
                    continue;
                }
                if (elem.type == (int)LEX_TYPES.OPERATOR)
                {
                    if (operatorsStack.Count == 0)
                        operatorsStack.Push(elem);
                    else
                        if (getOpPriority(elem) > getOpPriority(operatorsStack.Peek()))
                            operatorsStack.Push(elem);
                        else
                        {
                            while (true)
                            {
                                if (operatorsStack.Count == 0)
                                    break;
                                if (getOpPriority(elem) > getOpPriority(operatorsStack.Peek()))
                                    break;
                                result.Add(operatorsStack.Pop());
                            }
                            operatorsStack.Push(elem);
                        }
                }
            }
            while (operatorsStack.Count != 0)
                result.Add(operatorsStack.Pop());
            return result;
        }
        #endregion

        //Обработчик кнопки выхода из программы
        private void button3_Click(object sender, EventArgs e)
        {
            Close();
        }

        //Обработчик кнопки открытия файла
        private void button2_Click(object sender, EventArgs e)
        {
            OpenFileDialog openFileDialog1 = new OpenFileDialog();
            openFileDialog1.Filter = "txt files (*.txt)|*.txt|All files (*.*)|*.*";
            if(openFileDialog1.ShowDialog() == DialogResult.OK)
            {
                try
                {
                    StreamReader sr = new StreamReader(openFileDialog1.FileName);
                    while (!sr.EndOfStream)
                    {
                        viewText = sr.ReadToEnd();
                    }
                    sr.Close();
                    textBox1.Text = viewText;
                    
                }
                catch
                {
                    MessageBox.Show("Error cannot read file");
                }
            }
            
            
        }

        private void Form1_Load(object sender, EventArgs e)
        {
            this.ActiveControl = textBox1;
            //this.AcceptButton = button1;
            button1.Enabled = false;
        }

        private void textBox1_TextChanged(object sender, EventArgs e)
        {
            button1.Enabled = true;
        }

        private void button4_Click(object sender, EventArgs e)
        {
            Application.Restart();
        }
       
        
    }
   
}
