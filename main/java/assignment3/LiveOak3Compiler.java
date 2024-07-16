package assignment3;

import edu.utexas.cs.sam.core.SamSymbolTable;
import edu.utexas.cs.sam.io.SamTokenizer;
import edu.utexas.cs.sam.io.Tokenizer;
import edu.utexas.cs.sam.io.Tokenizer.TokenType;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;

class Symbol {
    private String type;
    private String val;
    private String loc;

    Symbol(String t, String v, String l) {
        type = t;
        val = v;
        loc = l;
    }

    String getType() {
        return type;
    }

    String getVal() {
        return val;
    }

    String getLoc()  {
        return  loc;
    }

    void setType(String s) {
        type = s;
    }
    
    void setVal(String v) {
        val = v;
    }

    void setLoc(String l) {
        loc = l;
    }
}


class ExpReturn {
    private String code;
    private String type;
	private boolean isReturn;

    ExpReturn(String c, String t) {
        type = t;   
        code = c;
    }

    String getType() {
        return type;
    }

    String getCode() {
        return code;
    }

	boolean getReturn() {
        return isReturn;
    }

    void setType(String s) {
        type = s;
    }
    
    void setCode(String s) {
        code = s;
    }

}


class MethodSignature {
    private String returnType;
	private Integer numParams;
	private ArrayList<Symbol> symbols;
    private boolean isConstructor;

    MethodSignature(Integer n, String t,  boolean c) {
        returnType = t;   
        numParams = n;
        isConstructor  = c;
    }

    String getReturnType() {
        return returnType;
    }

    Integer getNumParams() {
        return numParams;
    }

    Boolean getIsConstructor() {
        return isConstructor;
    }

	ArrayList<Symbol> getSymbols() {
        return symbols;
    }

    void setReturnType(String s) {
        returnType = s;
    }
    
    void setNumParams(Integer s) {
        numParams = s;
    }

	void setSymbols(ArrayList<Symbol> s) {
        symbols = s;
    }

}

class ClassSignature {
	private Integer numMembs;
	private ArrayList<Symbol> symbols;
    private boolean hasConstructor;

    ClassSignature(Integer n, boolean t) {
        hasConstructor = t;   
        numMembs = n;
    }

    Integer getNumMembs() {
        return numMembs;
    }

	ArrayList<Symbol> getSymbols() {
        return symbols;
    }

    boolean getHasConstructor() {
        return hasConstructor;
    }

    void setNumMembs(Integer s) {
        numMembs = s;
    }

	void setSymbols(ArrayList<Symbol> s) {
        symbols = s;
    }

}


public class LiveOak3Compiler
{   
    public static int numTokens = 0;
    public static int varLocation = 100;
    public static int labelCount = 0;
	public static Hashtable<String, MethodSignature> globalHash;
    public static Hashtable<String, ClassSignature> globalHashClass;
	public static String outfile;
	public static String infile;
	public static boolean firstPass = true; //used to gather method signatures

	public static void main(String[] args) throws IOException {

		//System.out.println("Testing");
		//String lo1ProgramDir = Path.of("src", "test", "resources", "LO-2", "InvalidPrograms").toString();
        String ProgramDir = Path.of("src", "test", "resources", "LO-3", "ValidPrograms").toString();
		String fileName = Path.of(ProgramDir, "test_25.lo").toString();
        //outfile = "output.sam";
		//infile = fileName;

        infile =  args[0];
        outfile = args[1];

		compiler(infile);
	}

	static String compiler(String fileName) 
	{
		try 
		{
            firstPass = true;
			globalHash = new Hashtable<>();
            globalHashClass = new Hashtable<>();
			SamTokenizer f = new SamTokenizer(fileName, SamTokenizer.TokenizerOptions.PROCESS_STRINGS);
            
			getProgram(f);  //first pass to gather method declarations
            //System.out.println("\n\n");

			labelCount = 0;
			firstPass = false;

			SamTokenizer f2 = new SamTokenizer(fileName, SamTokenizer.TokenizerOptions.PROCESS_STRINGS);
			String pgm = getProgram(f2);
			//String pgm  =  "";
            //String  fcode ="PUSHIMM 0\nLINK\nJSR Main__main\nPOPFBR\nSTOP\n";
            String  fcode ="PUSHIMM 0\nPUSHIMM 5\nMALLOC\nLINK\nJSR Main__main\nPOPFBR\nADDSP -1\nSTOP\n";
            fcode += pgm;
            fcode  += genStringLibCode();
            //System.out.println("\n" + fcode);

            try (Writer writer = new BufferedWriter(new OutputStreamWriter(
              new FileOutputStream(outfile), "utf-8"))) {
                writer.write(fcode);} catch (Exception ee) {}
            //printHashGlobal();
			return fcode;
		}
		catch (Exception e) {
			//String str = fileName.replace("\\", "/");
            String str = fileName;
			System.err.println("Failed to compile " + str);
			throw new Error("");
		}
	}

	static String getProgram(SamTokenizer f)
	{   
		try
		{
			String pgm="";
			while(f.peekAtKind()!=TokenType.EOF)
			{	
				pgm += getClassDecl(f);

			}
			return pgm;
		}
		catch(Error e)
		{   
            //System.out.println("Error in getProg");
			String str = infile.replace("\\", "/");
			System.err.println("Failed to compile " + str);
			throw new Error("");
		}		
	}

    static String getClassDecl(SamTokenizer  f) {

		String id;
		String str = "";
        try {
            
            Hashtable<String, Symbol> htc = new Hashtable<>();
            String s = f.getWord();
            if (!s.equals("class")) {
				//System.out.println("Error in getClassDecl1");
				throw new Error("");
			}
            id = getIdentifier(f);
            if  (globalHashClass.containsKey(id) && firstPass) {
                //System.out.println("Duplicate classes");
				throw new Error("");
            }
            if (!globalHashClass.containsKey("Main") && !firstPass) {
                //System.out.println("No main class");
				throw new Error("");
            }

            if (id.equals("while")) {
                throw new Error("");
            }

            htc.put("xxClassNamexx",  new Symbol("class", id, ""));

            if (!(f.check('('))) {
				//System.out.println("Error in getClassDecl2");
				throw new Error("");
			}

            boolean doneVarDecl = false;
            if (f.check(')')) {
                doneVarDecl = true;
				//f.pushBack();
                htc.put("xxNumMembersxx", new Symbol("", String.valueOf(0), ""));
            }	
            
            
            boolean first = true;
            while (!doneVarDecl) {
                getVarDeclClass(f, htc, first);
                first =false;
                if (f.check(')'))  {
                    doneVarDecl = true;
                    //f.pushBack();
                } //beginning of block
            }
            
            //get method  decl
            //printToken(f);
            if (!(f.check('{'))) {
				//System.out.println("Error in getClassDecl3");
				throw new Error("");
			}  
            
            
            boolean doneMethodDecl = false;
            if (f.check('}'))  {
                doneMethodDecl = true;
                //f.pushBack();
            } //beginning of block

            while (!doneMethodDecl) {
                str += getMethodDecl(f, htc, id);
                if (f.check('}')) {
                    doneMethodDecl =  true;
                }
            }

            //add class decl to global hash
			ClassSignature cs = new ClassSignature(htc.size() - 2, true);
			ArrayList<Symbol> ar = new ArrayList<>();

            Enumeration<String> keys = htc.keys();
            while (keys.hasMoreElements()) {
                String key = keys.nextElement();
                ar.add(htc.get(key));
            }
			cs.setSymbols(ar);
			if (firstPass) {
				globalHashClass.put(id, cs);
			}

			return str;

        } catch (Error e) {
            //System.out.println("Error in getClassDecl");
			throw new Error("");
        }
    }

	static String getMethodDecl(SamTokenizer f, Hashtable<String, Symbol> htc, String className) {

		String type;
        ArrayList<String> form = new ArrayList<>();
		String id;
		String body = "";
        try {
            

			Hashtable<String, Symbol> ht = new Hashtable<>();
            type = getType(f);
			id = getIdentifier(f);

			if (!(f.check('('))) {
				//System.out.println("Error in getMethodDecl1");
				throw new Error("");
				//throwParseError(null);
			}

			//get formals
			if (!(f.check(')'))) {
				
				form = getFormals(f);
				//printFormals(form);
				if (!(f.check(')'))) {
					//System.out.println("Error in getMethodDecl2");
					throw new Error("");
					//throwParseError(null);
				}
			}

            //check to make sure main doesn't take params
            if  (id.equals("main")  &&  form.size()  != 0) {
                //System.out.println("Error - Main  should  not take params");
                throw new Error("");
            }


			//add method decl to global hash
            boolean isConstructor = false;
            if (className.equals(id)) {
                isConstructor = true;
            }

			MethodSignature ms = new MethodSignature(form.size() / 2, type, isConstructor);
			ArrayList<Symbol> ar = new ArrayList<>();
            int paramIndex  = ms.getNumParams();

			for(int i = 0; i < form.size(); i += 2) {  
                String loc = String.valueOf(-1*paramIndex - 1); //added -1 to account for this pointer
				Symbol s = new Symbol(form.get(i), "0", loc);   //type and name is returned in alternating fashion
				ar.add(s);
				ht.put(form.get(i+1), s);  //add params to local ht
                paramIndex -=1;
			}  
			ms.setSymbols(ar);
            String mangledID = className + "__" + id;
			if (firstPass) {
				globalHash.put(mangledID, ms);
			}

            ht.put("xxMethodTypexx", new Symbol(type, "", ""));
            ht.put("xxMethodNamexx",  new Symbol(type, mangledID, "")); 

			if (!(f.check('{'))) {
				//System.out.println("Error in getMethodDecl3");
				throw new Error("");
				//throwParseError(null);
			}

			String L1 = returnNewLabel("");
			String L2 = returnNewLabel("");
			
			body = getBody(f, L1, L2, ht, htc, isConstructor);
			//body += L1 + ":\n";
			//body += L2 + ":\n";  //break

			if (!(f.check('}'))) {
				//System.out.println("Error in getMethodDecl4");
				throw new Error("");
				//throwParseError(null);
			}

            String r  = String.valueOf(-1*((form.size()/2) + 2));
            String c = ht.get("xxNumLocalsxx").getVal();
            String str1 = mangledID + ":\nADDSP " + c + "\n";
            String str2 = null;

            if (mangledID.equals("Main__main")) {
                r = "-2";
            }
            if (!c.equals("0")) {
                str2  = mangledID +"End:\nSTOREOFF " + r + "\nADDSP -" + c + "\nJUMPIND\n";
            }
            else {
                str2  = mangledID +"End:\nSTOREOFF " + r + "\nJUMPIND\n";
            }
            

			return str1 + body + str2;

        } catch (Error e) {
            //System.out.println("Error in getClassDecl");
			throw new Error("");
        }
        
	}


	static ArrayList<String> getFormals(SamTokenizer f){
		
		ArrayList<String> forms = new ArrayList<>();
		boolean doneID  = false;
		
		try {

			while (!doneID) {
				
				forms.add(getType(f));
				forms.add(getIdentifier(f));				
				if (!(f.check(','))) {
					doneID= true;
				}
			}
		} catch (Error e) {
			//System.out.println("Error in getFormals");
			throw new Error("");
		}
		return forms;
	}


	static ArrayList<ExpReturn> getActuals(SamTokenizer f, Hashtable<String, Symbol> ht, 
                                        Hashtable<String, Symbol> htc) {

		ArrayList<ExpReturn> acts = new ArrayList<>();
		boolean done = false;

		try {

			while (!done) {
				
				acts.add(getExp(f, returnNewLabel(""), returnNewLabel(""), ht, htc));				
				if (!(f.check(','))) {
					done= true;
				}
			}
		} catch (Error e) {
			//System.out.println("Error in getActuals");
			throw new Error("");
		}
		return acts;
	}


    static String getBody(SamTokenizer f, String l1, String l2, Hashtable<String, Symbol> ht,
                         Hashtable<String, Symbol> htc, boolean isConstructor)  {
        
        //System.out.println("GetBody");
        String str = "";
        try  {
            
            boolean doneVarDecl = false;
            if (f.check('{')) {
                doneVarDecl = true;
				f.pushBack();
                ht.put("xxNumLocalsxx", new Symbol("", String.valueOf(0), ""));
            }	
            
            boolean first = true;
            while (!doneVarDecl) {
                
                getVarDecl(f, ht, first);
                first  = false;

                if (f.check('{'))  {
                    doneVarDecl = true;
                    f.pushBack();
                } //beginning of block
            }
            str += getBlock(f, l1,  l2, ht, htc, "none");

            if (!ht.containsKey("ReturnBool77") && !isConstructor && 
                !ht.get("xxMethodTypexx").getType().equals("void")) {
				//System.out.println("No return and not constructor");
				throw new Error("");
			}
            else if (!ht.containsKey("ReturnBool77") && isConstructor) {
                //add code for constructor return
                str += "PUSHOFF -1\n";
            }

        } catch (Error e){
            //System.out.println("Error in getBody");
            throw new Error("");
        }
        return str;
    }

    static ArrayList<Symbol> getVarDeclClass(SamTokenizer f, Hashtable<String, Symbol> ht, boolean first) {
        
        //System.out.println("GetVarDeclClass");
        String type;
        String s;
        boolean doneID  = false;
        int numLocals;
        int  localLoc;

        if (first)  {
            numLocals = 0;
            localLoc = 0;
        }
        else {
            numLocals  = Integer.parseInt(ht.get("xxNumMembersxx").getVal());
            localLoc = numLocals;
        }

        try {
            type = getType(f);
            while (!doneID) {
                
                
                s = getIdentifier(f);
                Symbol sym = new Symbol(type, "0", String.valueOf(localLoc));
                ht.put(s,  sym);
                localLoc +=1;
                numLocals += 1;

                if (f.check(';'))  {
                    doneID = true;
                    ht.put("xxNumMembersxx", new Symbol("", String.valueOf(numLocals), ""));
                    return null;
                } 
                
                if (!(f.check(','))) {
                    //System.out.println("Error in getVarDeclClass");
                    //throwParseError(null);
					throw new Error("");
					
                }
            }

        } catch (Error e) {
            //System.out.println("Error in getVarDecl");
            throw new Error("");
        }
        return null;
    }

    static String getVarDecl(SamTokenizer f, Hashtable<String, Symbol> ht, boolean first) {
        
        //System.out.println("GetVarDecl");
        String type;
        String s;
        boolean doneID  = false;
        int numLocals;
        int  localLoc;

        if (first)  {
            numLocals = 0;
            localLoc = 2;
        }
        else {
            numLocals  = Integer.parseInt(ht.get("xxNumLocalsxx").getVal());
            localLoc = numLocals + 2;
        }

        try {
            type = getType(f);
            while (!doneID) {
                
                s = getIdentifier(f);
                if (s.equals("this")) {
                    //System.out.println("This cannot be a local");
					throw new Error("");
                }

                Symbol sym = new Symbol(type, "0", String.valueOf(localLoc));
                ht.put(s,  sym);
                localLoc +=1;
                numLocals += 1;

                if (f.check(';'))  {
                    doneID = true;
                    
                    //store numLocals in ht for method code generation, stored in value field of symbol
                    ht.put("xxNumLocalsxx", new Symbol("", String.valueOf(numLocals), ""));

                    return null;
                } //beginning of statement
                
                if (!(f.check(','))) {
                   // System.out.println("Error in getVarDecl");
                    //throwParseError(null);
					throw new Error("");
					
                }
            }

        } catch (Error e) {
           // System.out.println("Error in getVarDecl");
            throw new Error("");
        }
        return null;
    }


    static String getBlock(SamTokenizer f, String l1, String l2, Hashtable<String, Symbol> ht, 
                            Hashtable<String, Symbol> htc, String blockType) {
        
        //System.out.println("getBlock");
        String str = "";
        boolean doneStatement = false;
        try {
            
            if (!(f.check('{'))) {
               // System.out.println("Error in block (no curly bracket)");
                //throwParseError(null);
				throw new Error("");
            }

            
            while (!doneStatement) {

                String Lnext = returnNewLabel("");
                String Lbreak =  returnNewLabel("");
                //String Lbreak =  returnNewLabel("");
                str +=  getStatement(f, Lnext, Lbreak, ht, htc, blockType);
                if  (f.check('}'))  {
                    doneStatement  = true;
                }
                str += Lnext + ":\n";
                str += Lbreak + ":\n";  //break
            }

        } catch (Error e) {
           // System.out.println("Error in block");
            throw new Error("");
        }
        return str;
    }

    static String getStatement(SamTokenizer f, String  Lnext, String Lbreak, Hashtable<String, Symbol> ht, 
                                Hashtable<String, Symbol> htc, String blockType)  {

		//System.out.println("GetStatement\n");
        //printToken(f);

        try  {
            if (f.check(';'))  {
                return "";
            }
            String s = f.getWord();
			// var assignment
            if  (ht.containsKey(s)) {
				Symbol var = ht.get(s);
                if (!(f.check('='))) {
                  //  System.out.println("Error in stmt1");
                    //throwParseError(null);
					throw new Error("");
                }
                
                String l1 = returnNewLabel("");
                String l2 = returnNewLabel("");
                ExpReturn er = getExp(f, l1, l2, ht, htc);

                String eCode = er.getCode();
                //String eCode = l1 + ":\n" + er.getCode();
                if (!(f.check(';'))) {
                  //  System.out.println("Error in stmt2");
                    //throwParseError(null);
					throw new Error("");
                }

                //do type check
                if (!firstPass) {
                    if (!(er.getType().equals(var.getType())) && !er.getType().equals("this")) {

                       // System.out.println("Error in stmt3 - Mismatched types");
                    // throwParseError(null);
                        throw new Error("");
                    }
                }
                
                String originalLoc = var.getLoc();
                //return eCode + l1 + ":\nSTOREOFF " + String.valueOf(adjustedLoc) + "\n";
                return eCode + l1 + ":\nSTOREOFF " + originalLoc + "\n";
                
            }

            // class member assignnment
            if (htc.containsKey(s)) {

                Symbol member = htc.get(s);
                if (!(f.check('='))) {
                   // System.out.println("Error in stmt1");
                    //throwParseError(null);
					throw new Error("");
                }
                
                String l1 = returnNewLabel("");
                String l2 = returnNewLabel("");
                ExpReturn er = getExp(f, l1, l2, ht, htc);

                String eCode = er.getCode();
                //String eCode = l1 + ":\n" + er.getCode();
                if (!(f.check(';'))) {
                   // System.out.println("Error in stmt2");
                    //throwParseError(null);
					throw new Error("");
                }

                //do type check
                if (!firstPass) {
                    if (!(er.getType().equals(member.getType()))) {

                        //System.out.println("Error in stmt33 - Mismatched types");
                    // throwParseError(null);
                    //throw new Error("");
                    }
                }
                
                return "PUSHOFF -1\nPUSHIMM " + member.getLoc() + "\nADD\n"  + eCode + l1 + ":\nSTOREIND\n";
                //return eCode + l1 + ":\nSTOREOFF " + member.getLoc() + "\n";
                
            }
            
            if (s.equals("if"))  {

                String Lnew1 = returnNewLabel("");
                String Lnew2 = returnNewLabel("");
                if (!(f.check('('))) {
                    //System.out.println("Error in getstmt6");
                    //throwParseError(null);
					throw new Error("");
                }
                ExpReturn eif = getExp(f, Lnext, Lbreak, ht, htc);
                //eif.setCode(eif.getCode() + Lnext + ":\n");
                if (!(f.check(')'))) {
                   // System.out.println("Error in getstmt7");
                    //throwParseError(null);
					throw new Error("");
                }
                String b1 = getBlock(f, Lnext, Lbreak, ht, htc, "if");
                if (!(f.check("else"))) {
                   // System.out.println("Error in getstmt8");
                    //throwParseError(null);
					throw new Error("");
                }
                String b2 = getBlock(f, Lnext, Lbreak, ht, htc, "else");

                String ret = eif.getCode() + "JUMPC "  + Lnew1 + "\n" + Lnew2 + ":\n" 
                            + b2 + "JUMP " + Lnext  + "\n" + Lnew1  + ":\n" + b1;
                return ret;
            }

            if (s.equals("while"))  {
                String Lhead = returnNewLabel("");
                if (!(f.check('('))) {
                   // System.out.println("Error in getstmt9");
                   // throwParseError(null);
				   throw new Error("");
                }
                ExpReturn ewhile = getExp(f, Lnext, Lbreak, ht, htc);
                //ewhile.setCode(ewhile.getCode() + Lnext + ":\n");
                if (!(f.check(')'))) {
                   // System.out.println("Error in getstmt10");
                    //throwParseError(null);
					throw new Error("");
                }

                String b1 = getBlock(f, Lnext, Lbreak, ht, htc, "while");

                String ret = Lhead +  ":\n"+ ewhile.getCode() + "ISNIL\n"   
                            + "JUMPC " + Lnext + "\n" + b1 + "JUMP " + Lhead + "\n";
                return ret;

            }

            if(s.equals("break")) {
                //String ret = "JUMP "  + Lbreak + "\n";
                throw new  Error("");
                //return ret;
            }

			if (s.equals("return")) {

                //System.out.println("here");
				ExpReturn ee = getExp(f, Lbreak, s, ht, htc);
				//check for correct return type
                if (!firstPass) {
                    String mType = ht.get("xxMethodTypexx").getType();
                    if (!ee.getType().equals(mType))  {
                       // System.out.println("Wrong return type");
                        //throw new Error("");
                    }
                }

                //System.out.println(blockType);
                if (blockType.equals("none")) {
				    ht.put("ReturnBool77", new Symbol("bool", "", ""));
                }

                String  mname = ht.get("xxMethodNamexx").getVal();
				return ee.getCode() + "JUMP " + mname  + "End \n";

			}

           // System.out.println("Error in stmt11 - not a loop or var");
           // throwParseError(null);
		   throw new Error("");
            
            
        } catch (Error e) {
           // System.out.println("Error in stmt code");
            throw new Error("");
        }
    }

    static Symbol getVar(SamTokenizer f, Hashtable<String, Symbol> ht)  {

       // System.out.println("GetVar");
        //check to see if var is in symbol table
        try  {
            String s = f.getWord();
            
            if  (ht.containsKey(s)) {
                return ht.get(s);
            }
            else {
              //  System.out.println("Var not found in table");
                //throwParseError(null); 
				throw new Error("");
            }

        }  catch (Error e) {
           // System.out.println("Error in getvar");
            throw new Error("");
        }
    }


    static String getType(SamTokenizer f) {
        
        //System.out.println("GetType");
        String str = "";
        try {
            str += f.getWord();
            
            if (!(str.equals("int") || 
                str.equals("bool") || 
                str.equals("String") || 
                str.equals("void"))) {

                //then it must be a user defined  type in class table
                if (!firstPass && !globalHashClass.containsKey(str)) {
                    throw new Error("");
                }
            }
            return str;
        }
        catch (Error e) {
           // System.out.println("Error in getType");
			throw new Error("");
        }
    }


    static String getIdentifier(SamTokenizer f)  {
        
      // System.out.println("GetID");
	   //overloaded to also be used for getMethodName
        String str = "";
        try {
            str += f.getWord();
            return str;
        }
        catch (Error e) {
           // System.out.println("Error in getID / Method name");
			throw new Error("");
        }
        
    }


	static ExpReturn getExp(SamTokenizer f, String Ltrue, String Lfalse, Hashtable<String, Symbol> ht, 
                            Hashtable<String, Symbol> htc) 
	{   
       // System.out.println("GetExp");
        //printToken(f);
        try {
            switch (f.peekAtKind()) {
                case INTEGER: //E -> integer
                    ExpReturn er = new ExpReturn("PUSHIMM " + f.getInt() + "\n", "int");
                    return er;
                case STRING:
                    ExpReturn er2 = new ExpReturn("PUSHIMMSTR \"" + f.getString() + "\"\n", "String");
                    return er2;
                case WORD:
                    //check for local var 
                    String s = f.getWord();
                    if (ht.containsKey(s) && !isUserType(ht, s)) {
                         
                        ExpReturn er3 = new ExpReturn("PUSHOFF " + ht.get(s).getLoc() + "\n",
                                             ht.get(s).getType());                   
                        return er3;    
                    }
                    //check for class member variable
                    else if (htc.containsKey(s)) {

                        if (!f.check('.'))  {
                            ExpReturn er3 = new ExpReturn("PUSHOFF -1\nPUSHIMM " +  htc.get(s).getLoc() + "\nADD\n" +
                                                "PUSHIND\n",htc.get(s).getType());                   
                            return er3;  
                        }
                        else  {
                            //method call on class member
                            
                            String m2 = getIdentifier(f); //should be method name
                            String className = htc.get(s).getType();
                            m2 = className + "__" + m2;
                            

                            if(!firstPass) {
                                if (!globalHash.containsKey(m2)) {

                                   // System.out.println("Could not find method in method invoke53");
                                    throw new Error("");
                                }
                            }

                            if (!(f.check('('))) {
                               // System.out.println("Error in getMethodInvoke54");
                                throw new Error("");
                            }


                            ArrayList<ExpReturn> acts = new ArrayList<>();
                            if (!(f.check(')'))) {
                                acts = getActuals(f, ht, htc);
                            }
                            else {
                                f.pushBack();
                            }
                            
                            if(!firstPass) {
                                //check for correct args

                                int len1;
                                int len2;
                                ArrayList<Symbol> params = globalHash.get(m2).getSymbols();
                                if (acts == null) {
                                    len1 = 0;
                                } else {
                                    len1 = acts.size();
                                }
                                if (params == null) {
                                    len2 = 0;
                                } else {
                                    len2 = params.size();
                                }

                                
                                if (len1 != len2) {
                                   // System.out.println("Wrong number of parameters55");
                                    throw new Error("");
                                }

                                for (int i = 0;   i < params.size();i++) {
                                    if  (!params.get(i).getType().equals(acts.get(i).getType())) {
                                       // System.out.println("Wrong args passed55");
                                        throw new Error("");
                                    }
                                }
                            }

                            if (!(f.check(')'))) {
                               // System.out.println("Error in getMethodInvoke55");
                                throw new Error("");
                            }

                            //code for method invocation
                            //String rType = globalHash.get(m).getReturnType();
                            if (firstPass) {
                                ExpReturn ermi = new ExpReturn("Method Invoke Placeholder\n", "none"); 
                                return ermi; 
                            }
                            else {

                                String eList = "";
                                for (int i  = 0; i <acts.size(); i++) {
                                    eList += acts.get(i).getCode();
                                }
                                eList += "PUSHOFF -1\nPUSHIMM " +  htc.get(s).getLoc() + "\nADD\nPUSHIND\n";
                                String end = "LINK\nJSR " + m2 + "\nPOPFBR\nADDSP -" + String.valueOf(acts.size() + 1) + "\n";
                                String fs = "PUSHIMM 0\n" + eList + end;
                                ExpReturn ermi = new ExpReturn(fs, globalHash.get(m2).getReturnType());
                                return ermi; 
                            }
                        }
                    }

					//if not true or false its a method invocation  (possibly still a user type local  this is messy)
					else if (!(s.equals("true")) && !s.equals("false") 
                            && !s.equals("this") && !s.equals("null") && !s.equals("new")) {
						
						f.pushBack();
						String m = getIdentifier(f); //should be class object local
                        String className = ht.get(m).getType();
						
						if(!firstPass) {
							if (!ht.containsKey(m)) {

								//System.out.println("Could not find class in method invoke");
								throw new Error("");
							}
						}
						if (!(f.check('.'))) {
                            // System.out.println("Error in getMethodInvoke11");
							// throw new Error("");
                            //then its local of user defined type 
                            ExpReturn er33 = new ExpReturn("PUSHOFF " + ht.get(s).getLoc() + "\n",
                                            ht.get(s).getType());                   
                            return er33; 
                        }

                        String m2 = getIdentifier(f); //should be method name
                        m2 = className + "__" + m2;
                        

                        if(!firstPass) {
							if (!globalHash.containsKey(m2)) {

								//System.out.println("Could not find method in method invoke");
								throw new Error("");
							}
						}

                        if (!(f.check('('))) {
                           // System.out.println("Error in getMethodInvoke12");
							throw new Error("");
                        }


						ArrayList<ExpReturn> acts = new ArrayList<>();
						if (!(f.check(')'))) {
                            acts = getActuals(f, ht, htc);
                        }
						else {
							f.pushBack();
						}
						
						if(!firstPass) {
							//check for correct args

							int len1;
							int len2;
							ArrayList<Symbol> params = globalHash.get(m2).getSymbols();
							if (acts == null) {
								len1 = 0;
							} else {
								len1 = acts.size();
							}
							if (params == null) {
								len2 = 0;
							} else {
								len2 = params.size();
							}

							
							if (len1 != len2) {
								//System.out.println("Wrong number of parameters");
								throw new Error("");
							}

                            for (int i = 0;   i < params.size();i++) {
                                if  (!params.get(i).getType().equals(acts.get(i).getType())) {
                                  //  System.out.println("Wrong args passed");
                                    throw new Error("");
                                }
                            }
						}

						if (!(f.check(')'))) {
                           // System.out.println("Error in getMethodInvoke13");
							throw new Error("");
                        }

						//code for method invocation
						//String rType = globalHash.get(m).getReturnType();
						if (firstPass) {
							ExpReturn ermi = new ExpReturn("Method Invoke Placeholder\n", "none"); 
							return ermi; 
						}
						else {

                            String eList = "";
                            for (int i  = 0; i <acts.size(); i++) {
                                eList += acts.get(i).getCode();
                            }
                            eList += "PUSHOFF " +  ht.get(m).getLoc() +"\n"; //added this ptr to end of actuals
                            String end = "LINK\nJSR " + m2 + "\nPOPFBR\nADDSP -" + String.valueOf(acts.size() + 1) + "\n";
                            String fs = "PUSHIMM 0\n" + eList + end;
							ExpReturn ermi = new ExpReturn(fs, globalHash.get(m2).getReturnType());
							return ermi; 
						}
   					
					}
                    //else its a true or false literal- or null or this or new
                    else {
                        f.pushBack();
                        String word = f.getWord();
                        String b = "";
                        if (word.equals("true")) {
                            b = "1";
                            ExpReturn er4 = new ExpReturn("PUSHIMM " + b + "\n", "bool");
                            return er4;
                        }
                        else if (word.equals("false")) {
                            b = "0";
                            ExpReturn er4 = new ExpReturn("PUSHIMM " + b + "\n", "bool");
                            return er4;
                        }
                        else if (word.equals("null")) {
                            b  = "0";
                            ExpReturn er4 = new ExpReturn("PUSHIMM " + b + "\n", "null");
                            return er4;
                        }
                        else if (word.equals("this")) {
                            ExpReturn er4 = new ExpReturn("PUSHOFF -1\n", "this");
                            return er4;
                        }
                        else if (word.equals("new")) {
                            
                            String m = getIdentifier(f); //should be class name
                            if(!firstPass) {

                                if (!globalHashClass.containsKey(m)) {

                                   // System.out.println("Could not find class in const invoke");
                                    throw new Error("");
                                }
                            }
                            if (!(f.check('('))) {
                              //  System.out.println("Error in ConstInvoke");
                                throw new Error("");
                            }

                            String m2 = m + "__" + m; //should be method name
                            if(!firstPass) {
                                if (!globalHash.containsKey(m2)) {
                                    
                                    if (!(f.check(')'))) {
                                       // System.out.println("Error in getConstInvoke44");
                                        throw new Error("");
                                    }
                                    //no constructor
                                    int ssize = globalHashClass.get(m).getSymbols().size() - 2;
                                    String ss = "PUSHIMM " + String.valueOf(ssize) + "\nMALLOC\n"; //added malloc to end of args passed
                                    ExpReturn ermi = new ExpReturn(ss, m);
                                    return ermi; 
                                }
                            }
                            
                            ArrayList<ExpReturn> acts = new ArrayList<>();
                            if (!(f.check(')'))) {
                                acts = getActuals(f, ht, htc);
                            }
                            else {
                                f.pushBack();
                            }
                            
                            if(!firstPass) {
                                //check for correct args
                                int len1;
                                int len2;
                            
                                ArrayList<Symbol> params = globalHash.get(m2).getSymbols();
                                if (acts == null) {
                                    len1 = 0;
                                } else {
                                    len1 = acts.size();
                                }
                                if (params == null) {
                                    len2 = 0;
                                } else {
                                    len2 = params.size();
                                }

                                
                                if (len1 != len2) {
                                   // System.out.println("Wrong number of parameters in constructor");
                                    throw new Error("");
                                }

                                // for (int i = 0;   i < params.size();i++) {
                                //     if  (!params.get(i).getType().equals(acts.get(i).getType())) {

                                //         System.out.println(params.get(i).getType());
                                //         System.out.println(acts.get(i).getType());
                                //         System.out.println("Wrong args passed to constructor");
                                //         throw new Error("");
                                //     }
                                // }
                            }

                            if (!(f.check(')'))) {
                               // System.out.println("Error in getConstInvoke");
                                throw new Error("");
                            }

                            //code for constructor invocation
                            //String rType = globalHash.get(m).getReturnType();
                            if (firstPass) {
                                ExpReturn ermi = new ExpReturn("Constructor Invoke Placeholder\n", "none"); 
                                return ermi; 
                            }
                            else {

                                String eList = "";
                                for (int i  = 0; i <acts.size(); i++) {
                                    eList += acts.get(i).getCode();
                                }

                                int ssize = globalHashClass.get(m).getSymbols().size() - 2;
                                eList += "PUSHIMM " + String.valueOf(ssize) + "\nMALLOC\n"; //added malloc to end of args passed
                                String end = "LINK\nJSR " + m2 + "\nPOPFBR\nADDSP -" + String.valueOf(acts.size() + 1) + "\n";
                                String fs = "PUSHIMM 0\n" + eList + end;
                                ExpReturn ermi = new ExpReturn(fs, m);
                                return ermi; 
                            }
                        }
                        else {
                          //  System.out.println("Error in literal");
                            //throwParseError(null);
							throw new Error("");
                        }

                    }
                case OPERATOR:      
					
                    if (!(f.check('('))) {
                       // System.out.println("Error in getExp1");
                        //throwParseError(null);
						throw new Error("");
                    }

                    if (isUnop(f))  {
                        
                        //System.out.println("here");
                        char c = f.getOp();
                        ExpReturn er5 = getExp(f, Ltrue, Lfalse, ht, htc);
                        ExpReturn re = new ExpReturn("not init'd", "none");

                        if (er5.getType().equals("int")) {
                            String s1 = getUnopInt(f, c);
                            re.setCode(er5.getCode() + s1 + "\n");
                            re.setType("int");
                        }
                        else if (er5.getType().equals("bool")) {
                            String s2 = getUnopBool(f, c);
                            re.setCode(er5.getCode() + s2 + "\n");
                            re.setType("bool");

                        }
                        else if (er5.getType().equals("String")) {
                            String s3 = getUnopString(f, c);
                            String rev = "PUSHIMM 0\n" + er5.getCode() + s3;

                            re.setCode(rev);
                            re.setType("String");
                        }
                        else {
                           // System.out.println("Error in getExp5");
                            //throwParseError(null);
							throw new Error("");
                        }
                        //make sure you get closing paren
                        if (!(f.check(')'))) {
                           // System.out.println("Error in getExp3");
                            //throwParseError(null);
							throw new Error("");
                        }
                        return re;
                    }
                    
                    ExpReturn er6 = getExp(f, Ltrue, Lfalse, ht, htc); // for P22, P23, P25
                    //if just a double set of parentheses P25
                    if (f.check(')')) {
                        return er6;
                    }

                    //used for ternary operation --skipped
                    if (f.check('?')) {
                        
                        ExpReturn re = new ExpReturn("not init'd", "none");
                        String Lnew1 = returnNewLabel("");
                        String Lnew2 = returnNewLabel("");
                        ExpReturn firstTern = getExp(f, Ltrue, Lfalse, ht, htc);
                        if (!(f.check(':'))) {
                            //System.out.println("Error in getExpTern");
                            //throwParseError(null);
							throw new Error("");
                        }
                        ExpReturn secondTern = getExp(f, Ltrue, Lfalse, ht, htc);
                        if (!(f.check(')'))) {
                           // System.out.println("Error in getExpTern");
                            //throwParseError(null);
							throw new Error("");
                        }

                        String ret = er6.getCode() + "JUMPC " + Lnew1 + "\n" + Lnew2 + ":\n" 
                        + secondTern.getCode() + "JUMP " + Ltrue  + "\n" + Lnew1  + ":\n" + 
                        firstTern.getCode();

                        re.setCode(ret);
                        re.setType(firstTern.getType());
                        return re;

                    }
                    
                    if (isBinop(f))  {

                        char c = f.getOp();
                        ExpReturn er7 = getExp(f, Ltrue, Lfalse, ht, htc);
                        ExpReturn re = new ExpReturn("not init'd", "none");

                        if (er6.getType().equals("int") && er7.getType().equals("int")) {
                            ExpReturn b1 = getBinopInt(f, c);
                            re.setCode(er6.getCode() +  er7.getCode() + b1.getCode() + "\n");
                            re.setType(b1.getType());

                            //correct for div by 0
                            if (er7.getCode().equals("PUSHIMM 0\n") && b1.getCode().equals("DIV")){
                                re.setCode(er6.getCode() +  er7.getCode() + "GREATER" + "\n");
                                re.setType(b1.getType());
                            }
                            
                        }
                        else if (er6.getType().equals("bool") && er7.getType().equals("bool")) {
                            ExpReturn b2 = getBinopBool(f, c);
                            re.setCode(er6.getCode() +  er7.getCode() + b2.getCode() + "\n");
                            re.setType(b2.getType());
                            
                        }
                        else if (er6.getType().equals("String") && er7.getType().equals("String")) {
                        
                            ExpReturn b3 = getBinopString(f, c);
                            String con = "";
                            con = "PUSHIMM 0\n" + er6.getCode() +  er7.getCode() + b3.getCode();
                            re.setCode(con);
                            re.setType(b3.getType());
                        }
                        else if (er6.getType().equals("String") && er7.getType().equals("int")) {
                            
                            ExpReturn b3 = getBinopString(f, c);
                            String con = "PUSHIMM 0\n" + er6.getCode() +  er7.getCode() + b3.getCode();
                            re.setCode(con);
                            re.setType(b3.getType());
                        }
                        else if (er6.getType().equals("bool") && er7.getType().equals("String")) {
                            
                            String con = er6.getCode();
                            re.setCode(con);
                            re.setType("bool");
                        }
                        else if (er6.getType().equals(er7.getType()) || er6.getType().equals("null") ||
                                er7.getType().equals("null")  || er7.getType().equals("this") ||
                                er6.getType().equals("this")) {
                                
                                //pointer assignment
                                ExpReturn b = getBinopUser(f, c);
                                re.setCode(er6.getCode() +  er7.getCode() + b.getCode() + "\n");
                                re.setType(b.getType());
                        }
                        else {
                            if (!firstPass) {
                               // System.out.println("Error in getExp8");
                                throw new Error("");
                            }
                        }
                        //make sure you get closing paren
                        if (!(f.check(')'))) {
                           // System.out.println("Error in getExp9");
                           // throwParseError(null);
						   throw new Error("");
                        }
                        return re;
                    }

                default:   
                   // System.out.println("Error in getExp4");
                    //throwParseError(null);
					throw new Error("");
            }
        } catch (Error e) {
            //System.out.println("Error in getExp");
            throw new Error("");
        }

	}


    static ExpReturn getBinopUser(SamTokenizer  f, char c) {

        try {
            // System.out.println("GetBinopInt");
             //overloading the expReturn type, it doesn't really matter
             //just need to return the code and the type of the eval
             switch (c){
                 case '=':
                     return new ExpReturn("EQUAL", "null");
                 case '+':
                    return new ExpReturn("ADD", "int");
                case '&':
                    return new ExpReturn("AND", "bool");
                case '|':
                    return new ExpReturn("OR", "bool");
                case '*':
                    return new ExpReturn("TIMES", "int");
                case '/':
                    return new ExpReturn("DIV", "int");
                case '%':
                    return new ExpReturn("MOD", "int");
                case '<':
                    return new ExpReturn("LESS", "bool");
                case '>':
                    return new ExpReturn("GREATER", "bool");
                 default:
                    // System.out.println("Error in getBinopUser");
                     //throwParseError(null);
                     throw new Error("");
             }
         } catch (Error e) {
             //System.out.println("Error in getBinopUser");
             throw new Error("");
         }

    }

    static ExpReturn getBinopInt(SamTokenizer f, char c) {
        try {
           // System.out.println("GetBinopInt");
            //overloading the expReturn type, it doesn't really matter
            //just need to return the code and the type of the eval
            switch (c){
                case '+':
                    return new ExpReturn("ADD", "int");
                case '-':
                    return new ExpReturn("SUB", "int");
                case '*':
                    return new ExpReturn("TIMES", "int");
                case '/':
                    return new ExpReturn("DIV", "int");
                case '%':
                    return new ExpReturn("MOD", "int");
                case '<':
                    return new ExpReturn("LESS", "bool");
                case '>':
                    return new ExpReturn("GREATER", "bool");
                case '=':
                    return new ExpReturn("EQUAL", "bool");
                default:
                  //  System.out.println("Error in getBinopInt");
                    //throwParseError(null);
					throw new Error("");
            }
        } catch (Error e) {
           // System.out.println("Error in getBinopInt");
			throw new Error("");
        }
    }


    static ExpReturn getBinopBool(SamTokenizer f, char c) {
        try {
           // System.out.println("GetBinopBool");
            //overloading the expReturn type, it doesn't really matter
            //just need to return the code and the type of the eval
            switch (c){
                case '&':
                    return new ExpReturn("AND", "bool");
                case '|':
                    return new ExpReturn("OR", "bool");
                default:
                   // System.out.println("Error in getBinopBool");
                   // throwParseError(null);
				   throw new Error("");
            }
        } catch (Error e) {
           // System.out.println("Error in getBinopBool");
            throw new Error("");
        }
    }


    static ExpReturn getBinopString(SamTokenizer f, char c) {
        
       // System.out.println("GetBinopString");
        try {
            //strcmpL is standard strcmp, strcmpR is swapped strcmp
            String strConcat = "LINK\nJSR str_concat\nPOPFBR\nADDSP -2\n";
            String strRepeat = "LINK\nJSR str_repeat\nPOPFBR\nADDSP -2\n";
            String strCmpL = "LINK\nJSR str_cmp\nPOPFBR\nADDSP -2\nISPOS\n";
            String strCmpE = "LINK\nJSR str_cmp\nPOPFBR\nADDSP -2\nISNIL\n";
            String strCmpG = "LINK\nJSR str_cmp\nPOPFBR\nADDSP -2\nISNEG\n";

            //overloading the expReturn type, it doesn't really matter
            //just need to return the code and the type of the eval
            switch (c){
                case '*':
                    return new ExpReturn(strRepeat, "String");
                case '+':
                    return new ExpReturn(strConcat, "String");
                case '<':
                    return new ExpReturn(strCmpL, "bool");
                case '>':
                    return new ExpReturn(strCmpG, "bool");
                case '=':
                    return new ExpReturn(strCmpE, "bool"); //doesnt matter which version of strcmp to use here
                default:
                   // System.out.println("Error in getBinopString");
                   // throwParseError(null);
				   throw new Error("");
            }
        } catch (Error e) {
           // System.out.println("Error in getBinopString");
			throw new Error("");
        }
    }


    static String getUnopInt(SamTokenizer f, char c) {

       // System.out.println("GetUnopInt");
        try {
            if (c == '~') {
                //return "BITNOT";
                return   "PUSHIMM  -1\nTIMES";
            }
            else {
                //System.out.println("Error in getUnopInt");
                //throwParseError(null);
				throw new Error("");
            }
        } catch (Error e) {
           // System.out.println("Error in getUnopInt");
			throw new Error("");
        }
    }


    static String getUnopBool(SamTokenizer f, char c) {

       // System.out.println("GetUnopBool");
        try {
            if (c == '!') {
                return "NOT";
            }
            else {
               // System.out.println("Error in getUnopBool");
                //throwParseError(null);
				throw new Error("");
            }
        } catch (Error e) {
         //   System.out.println("Error in getUnopBool");
            throw new Error("");
        }
    }


    static String getUnopString(SamTokenizer f, char c) {

       // System.out.println("GetUnopString");
        String reversal = "LINK\nJSR str_rev\nPOPFBR\nADDSP -1\n";
        try {
            if (c == '~') {
                return reversal;
            }
            else {
               // System.out.println("Error in getUnopString");
               // throwParseError(null);
			   throw new Error("");
            }

        } catch (Error e) {
          //  System.out.println("Error in getUnopString");
            throw new Error("");
        }
    }


    static boolean isUnop(SamTokenizer f) {

        switch (f.peekAtKind()) {
            case OPERATOR:
                char c = f.getOp();
                if (c == '!' || c == '~') {
                    f.pushBack();
                    return true;
                }
                else {
                    f.pushBack();
                    return false;
                }
            default:
                return false;
        }
    }


    static boolean isBinop(SamTokenizer f) {

        char c = f.getOp();
        if (c == '+' || c == '-' || c == '*' || c == '/' || c == '%' 
            || c == '&' || c == '|' || c == '<' || c == '>' || c == '=') {
            f.pushBack();
            return true;
        }
        else {
            f.pushBack();
            return false;
        }
    }

    static String returnNewLabel(String type) {
        labelCount += 1;
        return "L" + type + String.valueOf(labelCount);
    }

    static boolean isUserType(Hashtable<String, Symbol> ht, String s) {
        
        String type = ht.get(s).getType();

        if (!type.equals("int")  && !type.equals("String") && 
            !type.equals("bool") && !type.equals("void") ) {
            return true;
        }
        return false;
    }


    static void throwParseError(Error e) {
		// String str = infile.replace("\\", "/");
		// System.err.println("Failed to compile " + str);
		// throw new Error("");
    }

    static void printToken(SamTokenizer f) {

        switch (f.peekAtKind()) {
            case INTEGER: //E -> integer
                System.out.print(f.getInt() + " ");
                System.out.println("integer");
                break;   
            case FLOAT:
                System.out.print(f.getFloat() + " ");
                System.out.println("float");
                break;
            case WORD:
                System.out.print(f.getWord() + " ");
                System.out.println("word");
                break;
            case OPERATOR:
                System.out.print(f.getOp() + " ");
                System.out.println("op");
                break; 
            case STRING:
                System.out.print(f.getString() + " ");
                System.out.println("string");
                break; 
            case CHARACTER:  
                System.out.print(f.getCharacter() + " ");
                System.out.println("char");
                break; 
            default:
         }
         f.pushBack();
    }

    static void printHash(Hashtable<String, Symbol> ht) {
        
        Enumeration<String> keys = ht.keys();
        while (keys.hasMoreElements()) {
            String key = keys.nextElement();
            System.out.println("Key: " + key + ", Value: " + ht.get(key).getVal()
            + ", Loc: " + ht.get(key).getLoc()
            + ", Type: " + ht.get(key).getType());
        }
    }

	static void printHashGlobal() {
		
        Enumeration<String> keys = globalHash.keys();
        while (keys.hasMoreElements()) {
            String key = keys.nextElement();
            System.out.println("Key: " + key + ", Type: " + globalHash.get(key).getReturnType());
        }
    }

	static void printArray(ArrayList<String> f) {
		for(int i = 0; i < f.size(); i++) {   
			System.out.println(f.get(i));
		}  
	}

    static String  genStringLibCode() {

        String rev = "\n\nstr_rev:\nPUSHOFF -1\nPUSHIMM 100\nMALLOC\nDUP\nSTOREOFF 15\nSTOREOFF 12\nDUP\nDUP\nSTOREOFF 14\nSTOREOFF 13\nPUSHIND\nPUSHIMMCH '\0'\n"
        + "CMP\nISNIL\nJUMPC is_nil_str_rev\nPUSHOFF 13\nloop_str_rev:\nPUSHIND\nPUSHIMMCH '\0'\nCMP\nISNIL\nJUMPC rev_prep_str_rev\n" 
        + "PUSHOFF 14\nPUSHIMM 1\nADD \nSTOREOFF 14\nPUSHOFF 14\nJUMP loop_str_rev\nstart_reverse_str_rev:\nPUSHOFF 12\nPUSHOFF 14\n"
        + "PUSHIND\nSTOREIND\nPUSHOFF 14\nPUSHOFF 13\nCMP\nISNIL\nJUMPC end1_str_rev\nPUSHOFF 14\nPUSHIMM -1\nADD \nSTOREOFF 14\nPUSHOFF 12\n"
        + "PUSHIMM 1\nADD\nSTOREOFF 12\nJUMP start_reverse_str_rev\nrev_prep_str_rev:\nPUSHOFF 14\nPUSHIMM -1\nADD\nSTOREOFF 14\nJUMP start_reverse_str_rev\n"
        + "is_nil_str_rev:\nPUSHOFF 12\nPUSHIMMCH '\0'\nSTOREIND\nJUMP true_end_str_rev\nend1_str_rev: \nPUSHOFF 12\nPUSHIMM 1\nADD\n"
        + "PUSHIMMCH '\0'\nSTOREIND\ntrue_end_str_rev:\nPUSHOFF 15\nSTOREOFF -2\nJUMPIND\n";

        String concat = "\n\nstr_concat:\nPUSHOFF -2\nPUSHOFF -1\nPUSHIMM 100\nMALLOC\nDUP\nSTOREOFF 15\nSTOREOFF 14\nSWAP\n"
        + "loop1_str_concat:\nDUP\nPUSHIND\nDUP\nPUSHIMMCH '\0'\nCMP\nISNIL\nJUMPC end1_str_concat\nPUSHOFF 14\n"
        + "SWAP\nSTOREIND\nPUSHOFF 14\nPUSHIMM 1\nADD \nSTOREOFF 14\nPUSHIMM 1\nADD\nJUMP loop1_str_concat\nend1_str_concat:\n"
        +  "ADDSP -1\nSWAP\nloop2_str_concat: \nDUP\nPUSHIND\nDUP\nPUSHIMMCH '\0'\nCMP\nISNIL\nJUMPC end2_str_concat\n"
        + "PUSHOFF 14\nSWAP\nSTOREIND\nPUSHOFF 14\nPUSHIMM 1\nADD \nSTOREOFF 14\nPUSHIMM 1\nADD\nJUMP loop2_str_concat\n"
        + "end2_str_concat:\nPUSHOFF 14\nPUSHIMMCH '\0'\nSTOREIND\nADDSP -3\nPUSHOFF 15\nSTOREOFF -3\nJUMPIND\n";

        String rep = "\n\nstr_repeat:\nPUSHOFF -2\nPUSHOFF -1\nPUSHIMM 100\nMALLOC\nDUP\nSTOREOFF 15\nSTOREOFF 14\nSTOREOFF 13\nDUP\nSTOREOFF 12\n"
        + "STOREOFF 11\nloop_str_repeat:\nPUSHOFF 13\nPUSHIMM 0 \nGREATER\nISNIL\nJUMPC end1_str_repeat\n"
        + "strloop_str_repeat: \nPUSHOFF 11\nPUSHIND\nDUP\nPUSHIMMCH '\0'\nCMP\nISNIL\nJUMPC loop_prep_str_repeat\n"
        + "PUSHOFF 14\nSWAP\nSTOREIND\nPUSHOFF 14\nPUSHIMM 1\nADD\nSTOREOFF 14\nPUSHOFF 11\nPUSHIMM 1\nADD\n"
        + "STOREOFF 11\nJUMP strloop_str_repeat\nloop_prep_str_repeat:\nADDSP -1\nPUSHOFF 13\nPUSHIMM -1\nADD\n"
        + "STOREOFF 13\nPUSHOFF 12\nSTOREOFF 11\nJUMP loop_str_repeat\nend1_str_repeat:\nPUSHOFF 14\nPUSHIMMCH '\0'\n"
        + "STOREIND\nPUSHOFF 15\nSTOREOFF -3\nJUMPIND\n";

        String cmp  = "\n\nstr_cmp:\nPUSHOFF -2\nPUSHOFF -1\nDUP\nSTOREOFF 14\nSWAP\nDUP\nSTOREOFF 15\nloop_str_cmp:\nPUSHIND\nSWAP\n"
        + "PUSHIND\nSWAP\nCMP\nISPOS\nJUMPC is_greater_str_cmp\nPUSHOFF 14\nPUSHOFF 15\nPUSHIND\nSWAP\nPUSHIND\nSWAP\n"
        + "CMP\nISNEG\nJUMPC is_less_str_cmp\nPUSHOFF 14\nPUSHIND\nPUSHIMMCH '\0'\nCMP\nISNIL\nJUMPC is_equal_str_cmp\nPUSHOFF 14\n"
        + "PUSHIMM 1\nADD \nSTOREOFF 14\nPUSHOFF 15\nPUSHIMM 1\nADD \nSTOREOFF 15\nPUSHOFF 14\nPUSHOFF 15\nJUMP loop_str_cmp\n"
        + "is_greater_str_cmp:\nPUSHIMM -1\nJUMP end1_str_cmp\nis_less_str_cmp:\nPUSHIMM 1\nJUMP end1_str_cmp\nis_equal_str_cmp:\n"
        + "PUSHIMM 0\nJUMP end1_str_cmp\nend1_str_cmp:\nSTOREOFF -3\nJUMPIND\n";

        return rev + concat + rep +  cmp;
    }
}

