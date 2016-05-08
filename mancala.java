import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

/*FILE TO BE SUBMITTED*/
class GreedySearch{

	static GameState bestGameState;
	static int score;

	public StringBuilder genStates(GameState gamestate){

		bestGameState = new GameState().setWorstState(gamestate.getInit_play());
		genStatesUtil(new GameState().makeNewGameStateInstance(gamestate),1,gamestate.getInit_play());
		return printBoard(bestGameState);
	}

	public void genStatesUtil(GameState parentgamestate,int depth,int turn){
		GameState nextGameState;

		if(parentgamestate.getPeb_p1_side()+parentgamestate.getPeb_p2_side()==0){
			return;
		}

		if(depth <= 1){

			for(int pos = 2;pos<=parentgamestate.getNum_bins()+1;pos++){

				if(parentgamestate.checkPit(pos,turn)==0)
					continue;
				nextGameState = parentgamestate.nextLegalState(new GameState().makeNewGameStateInstance(parentgamestate),turn,pos);
				if(nextGameState.haveAnoth_chance())
					genStatesUtil(nextGameState,depth,turn);
				else{
					if(nextGameState.evaluation(turn)>bestGameState.evaluation(turn))
						bestGameState = nextGameState;
				}
			}

		}

	}

	StringBuilder printBoard(GameState gamestate){
		int i;
		StringBuilder string = new StringBuilder();
		String p1="",p2="";

		for(i = 2;i<=gamestate.getNum_bins()+1;i++)
			p1 = p1.concat(String.valueOf(gamestate.checkPit(i,0))+" ");
		for(i = 2;i<=gamestate.getNum_bins()+1;i++)
			p2 = p2.concat(String.valueOf(gamestate.checkPit(i,1))+" ");

		string.append(p2).append(System.lineSeparator());
		string.append(p1).append(System.lineSeparator());
		string.append(gamestate.checkManca(1)).append(System.lineSeparator());
		string.append(gamestate.checkManca(0)).append(System.lineSeparator());
		return string;
	}
}

class MiniMaxSearchNode{
	GameState gameState;
	double value;

	public MiniMaxSearchNode(GameState gameState,int turn){
		this.gameState = gameState;
		if(turn == 0)
			this.value = Double.NEGATIVE_INFINITY;

		else
			this.value = Double.POSITIVE_INFINITY;		
	}

}
class MiniMaxSearch{

	private MiniMaxSearchNode node;
	private static int cutOffDepth;
	private static MiniMaxSearchNode bestNode; //my next move
	private static int initPlay;
	private static int count;
	private static BufferedWriter w2;

	public void genInitStates(GameState gamestate,int depth,BufferedWriter wr1,BufferedWriter wr2) throws IOException{
		initPlay = gamestate.getInit_play();
		w2 = wr2;
		w2.append("Node"+","+"Depth"+","+"Value").append(System.lineSeparator());
		w2.append("root"+","+"0"+","+"-Infinity").append(System.lineSeparator());
		bestNode = new MiniMaxSearchNode(new GameState().setWorstState(gamestate.getInit_play()), gamestate.getInit_play());
		this.cutOffDepth = depth;
		node = new MiniMaxSearchNode(gamestate,gamestate.getInit_play());
		genStatesUtil(node,1,node.gameState.getInit_play(),-1,1);
		printTraverseLog("root",0,bestNode.value);
		wr1.append(printBoard(bestNode.gameState));
	}

	public double genStatesUtil(MiniMaxSearchNode parentNode,int depth,int turn,int parentPos,int dfp) throws IOException{
		MiniMaxSearchNode childNode = null;
		double bestValLoc = turn==0?Double.NEGATIVE_INFINITY:Double.POSITIVE_INFINITY;
		GameState nextState = null;


		if(parentNode.gameState.getPeb_p1_side()+parentNode.gameState.getPeb_p2_side()==0){
			//System.out.println("Game End State");
			if(depth-1<cutOffDepth){
				if(!parentNode.gameState.isSpecial_Case())
					printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth-1,parentNode.value);
				else
					printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth-1,-1*parentNode.value);	
			}
            if(depth-1 == cutOffDepth)
            	if(parentNode.gameState.isSpecial_Case())
            		printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth-1,-1*parentNode.value);	
			return parentNode.gameState.evaluationMiniMax();
		}

		if(depth > cutOffDepth)
			return parentNode.gameState.evaluationMiniMax();

		else{

			for(int pos = 2;pos<=parentNode.gameState.getNum_bins()+1;pos++){

				if(parentNode.gameState.checkPit(pos,turn)==0)
					continue;
				nextState = parentNode.gameState.nextLegalState(new GameState().makeNewGameStateInstance(parentNode.gameState),turn,pos);

				childNode = new MiniMaxSearchNode(nextState,(turn+1)%2);
				if(depth!=cutOffDepth && childNode.gameState.getPeb_p1_side()+childNode.gameState.getPeb_p2_side()!=0){//Non terminal conditions
					if((turn == 0||turn ==1) && childNode.gameState.haveAnoth_chance())
						printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth,-1*childNode.value); 
					else
						printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth,childNode.value);
				}
				if(childNode.gameState.haveAnoth_chance()){
					if(depth == cutOffDepth)

						printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth,-1*childNode.value);

					if(turn == 0)
					{
						childNode.value = Math.min(childNode.value, genStatesUtil(childNode,depth,turn,pos,depth+1));
					}

					else
					{
						childNode.value = Math.max(childNode.value, genStatesUtil(childNode,depth,turn,pos,depth+1));
					}
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth,childNode.value);
				}

				else{

					if(turn == 0)
					{ 
						childNode.value = Math.min(childNode.value, genStatesUtil(childNode,depth+1,(turn+1)%2,pos,depth+1));

					}
					else
					{
						childNode.value = Math.max(childNode.value, genStatesUtil(childNode,depth+1,(turn+1)%2,pos,depth+1));

					}
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth,childNode.value);
				}

				if(turn == 0){
					if(childNode.value>bestValLoc)
						bestValLoc = childNode.value;
				}
				else {
					if(childNode.value<bestValLoc)
						bestValLoc = childNode.value;
				}

				//Printing Parent
				if(depth-1>0 && dfp - depth + 1 == 1  && pos<parentNode.gameState.getNum_bins()+1 && parentNode.gameState.isAnyMancaBeyondPos(pos, turn)!=0)
					printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth-1,bestValLoc);
				else if(depth-1>0 && dfp - depth + 1 > 1  && pos<parentNode.gameState.getNum_bins()+1 && pos<parentNode.gameState.getNum_bins()+1 && parentNode.gameState.isAnyMancaBeyondPos(pos, turn)!=0)
					printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth,bestValLoc);	
				else if(depth-1==0 && dfp - depth + 1 > 1 && pos<parentNode.gameState.getNum_bins()+1 && pos<parentNode.gameState.getNum_bins()+1 && parentNode.gameState.isAnyMancaBeyondPos(pos, turn)!=0)
					printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth,bestValLoc);
				else if(depth-1==0 &&dfp - depth + 1 == 1  && pos<parentNode.gameState.getNum_bins()+1 && parentNode.gameState.isAnyMancaBeyondPos(pos, turn)!=0)
					printTraverseLog("root",depth-1,bestValLoc);


				if(depth == 1)
				{    
					if(turn == 0){
						if(bestNode.value<childNode.value)
							bestNode = childNode;}
					else{
						if(bestNode.value>childNode.value)
							bestNode = childNode;
					}

				}
			}

			return bestValLoc;
		}



	}

	StringBuilder printBoard(GameState gamestate){
		StringBuilder nextState= new StringBuilder();
		int i;
		String p1="",p2="";
		for(i = 2;i<=gamestate.getNum_bins()+1;i++)
			p1 = p1.concat(String.valueOf(gamestate.checkPit(i,0))+" ");
		for(i = 2;i<=gamestate.getNum_bins()+1;i++)
			p2 = p2.concat(String.valueOf(gamestate.checkPit(i,1))+" ");

		nextState.append(p2).append(System.lineSeparator());
		nextState.append(p1).append(System.lineSeparator());
		nextState.append(gamestate.checkManca(1)).append(System.lineSeparator());
		nextState.append(gamestate.checkManca(0)).append(System.lineSeparator());
		return nextState;

	}

	void printTraverseLog(String node,int depth,double value) throws IOException{
		//	count++;
		StringBuilder sb = new StringBuilder();
		sb.append(node).append(",");
		sb.append(depth).append(",");
		if(value == Double.NEGATIVE_INFINITY || value == Double.POSITIVE_INFINITY)
			if(initPlay==0)
				sb.append(value);
			else
				sb.append(-1*value);
		else
			if(initPlay==0)
				sb.append((int)value);
			else
				sb.append(-1*(int)value);	
		w2.append(sb.toString()).append(System.lineSeparator());
		//	System.out.println(count);
	}
}



class AlphaBetaSearchNode{
	GameState gameState;
	double value;

	public AlphaBetaSearchNode(GameState gameState,int turn){
		this.gameState = gameState;
		if(turn == 0)
			this.value = Double.NEGATIVE_INFINITY;
		else
			this.value = Double.POSITIVE_INFINITY;	
	}
}

class AlphaBetaSearch{

	private static int cutOffDepth;
	private static AlphaBetaSearchNode bestState;
	//private static StringBuilder string[];
	private static int initPlay;
	private static int count =0;
	private static BufferedWriter w2;

	public void AlphaBetaSearchUtil(GameState gameState,int cutOffDepth,BufferedWriter wr1,BufferedWriter wr2) throws IOException{
		double v;
		this.cutOffDepth = cutOffDepth;
		initPlay = gameState.getInit_play();
		w2 = wr2;
		w2.append("Node"+","+"Depth"+","+"Value"+","+"Alpha"+","+"Beta").append(System.lineSeparator());
		bestState = new AlphaBetaSearchNode(new GameState().setWorstState(gameState.getInit_play()),gameState.getInit_play());
		if(gameState.getInit_play() == 0)
			v = MaxVal(gameState,Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY,0,gameState.getInit_play(),-1,0,-1);
		else
			v = MinVal(gameState,Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY,0,gameState.getInit_play(),-1,0,-1);

		System.out.println(v);
		wr1.append(printBoard(bestState.gameState));
	}

	public double MaxVal(GameState parentgamestate,double alpha,double beta,int depth,int turn,int parentPos,int dfs,int prevTurn) throws IOException{

		double v = Double.NEGATIVE_INFINITY;
		GameState nextGameState = null;
		if(parentgamestate.getPeb_p1_side()+parentgamestate.getPeb_p2_side()==0)
		{
			if(depth == cutOffDepth){
				double initVal = ((turn+1)%2==0) ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
				if(!parentgamestate.isSpecial_Case())
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
					else{
						printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,initVal,alpha,beta);
						printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
					}
			}
				
			else
			{
				double initVal = ((turn+1)%2==0) ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
				if(!parentgamestate.isSpecial_Case()){
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,-1*initVal,alpha,beta);
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
				}
				else if(parentgamestate.isSpecial_Case()){
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,initVal,alpha,beta);
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
				}
			}
			return parentgamestate.evaluationMiniMax();
		}

		if(depth == cutOffDepth){
			printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
			return parentgamestate.evaluationMiniMax();
		}


		for(int pos = 2;pos<=parentgamestate.getNum_bins()+1;pos++){

			if(parentgamestate.checkPit(pos,turn)==0)
				continue;
			nextGameState = parentgamestate.nextLegalState(new GameState().makeNewGameStateInstance(parentgamestate),turn,pos);

			if(depth == 0 && dfs - depth == 0 )
				printTraverseLog("root",depth,v,alpha,beta);

			double initVal = ((turn+1)%2==0) ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
			if(depth+1!=cutOffDepth && nextGameState.getPeb_p1_side()+nextGameState.getPeb_p2_side()!=0){//Non terminal conditions@@

				if((turn == 0||turn ==1) && nextGameState.haveAnoth_chance())//@@
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth+1,-1*initVal,alpha,beta);//@@ 
				else
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth+1,initVal,alpha,beta);//@@
			}
			if(nextGameState.haveAnoth_chance()){

				if(depth+1 == cutOffDepth)//@
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth+1,-1*initVal,alpha,beta);//@

				v = Math.max(v, MaxVal(nextGameState,alpha,beta,depth,turn,pos,depth+1,turn));	



			}
			else{
				v = Math.max(v, MinVal(nextGameState,alpha,beta,depth+1,(turn+1)%2,pos,depth+1,turn));
				if(depth == 0 && parentgamestate.getInit_play()==0 && v>bestState.value)
				{
					bestState.gameState = nextGameState;
					bestState.value = v;
				}   
			}

			if(v>=beta) {
				if(depth>0 && dfs - depth == 0  && pos<=parentgamestate.getNum_bins()+1)
					printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth,v,alpha,beta);
				else if(depth>0 && dfs - depth  > 0  && pos<=parentgamestate.getNum_bins()+1)
					printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);	
				else if(depth==0 && dfs - depth > 0 && pos<=parentgamestate.getNum_bins()+1)
					printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);

				return v;
			}
			alpha = Math.max(alpha, v);

			//Printing Parent
			if(depth>0 && dfs - depth == 0  && pos<=parentgamestate.getNum_bins()+1)
				printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth,v,alpha,beta);
			else if(depth>0 && dfs - depth  > 0  && pos<=parentgamestate.getNum_bins()+1)
				printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);	
			else if(depth==0 && dfs - depth > 0 && pos<=parentgamestate.getNum_bins()+1)
				printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);
			else if((depth==0 && dfs - depth  == 0 && pos==parentgamestate.getNum_bins()+1) || (depth==0 && dfs - depth  == 0 && parentgamestate.isAnyMancaBeyondPos(pos, turn)==0))
				printTraverseLog("root",depth,v,alpha,beta);
		}
		return v;
	}

	public double MinVal(GameState parentgamestate,double alpha,double beta,int depth,int turn,int parentPos,int dfs,int prevTurn) throws IOException{

		GameState nextGameState = null;
		double v = Double.POSITIVE_INFINITY;
		if(parentgamestate.getPeb_p1_side()+parentgamestate.getPeb_p2_side()==0){
			if(depth == cutOffDepth){
				double initVal = ((turn+1)%2==0) ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
				if(!parentgamestate.isSpecial_Case())
				printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
				else{
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,initVal,alpha,beta);
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
				}
				}
			else
			{
				double initVal = ((turn+1)%2==0) ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
				if(!parentgamestate.isSpecial_Case()){
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,-1*initVal,alpha,beta);
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
				}
				else if(parentgamestate.isSpecial_Case()){
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,initVal,alpha,beta);
					printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
				}
			}
			return parentgamestate.evaluationMiniMax();
		}

		if(depth == cutOffDepth){
			printTraverseLog((turn==0)?"A"+parentPos:"B"+parentPos,depth,parentgamestate.evaluationMiniMax(),alpha,beta);
			return parentgamestate.evaluationMiniMax();
		}

		for(int pos = 2;pos<=parentgamestate.getNum_bins()+1;pos++){

			if(parentgamestate.checkPit(pos,turn)==0)
				continue;
			nextGameState = parentgamestate.nextLegalState(new GameState().makeNewGameStateInstance(parentgamestate),turn,pos);

			if(depth == 0 && dfs - depth == 0 )
				printTraverseLog("root",depth,v,alpha,beta);

			double initVal = ((turn+1)%2==0) ? Double.NEGATIVE_INFINITY : Double.POSITIVE_INFINITY;
			if(depth+1!=cutOffDepth && nextGameState.getPeb_p1_side()+nextGameState.getPeb_p2_side()!=0){//Non terminal conditions@@

				if((turn == 0||turn ==1) && nextGameState.haveAnoth_chance())//@@
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth+1,-1*initVal,alpha,beta);//@@ 
				else
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth+1,initVal,alpha,beta);//@@
			}

			if(nextGameState.haveAnoth_chance()){
				if(depth+1 == cutOffDepth)
					printTraverseLog((turn == 0)?"B"+pos:"A"+pos,depth+1,-1*initVal,alpha,beta);
				v = Math.min(v, MinVal(nextGameState,alpha,beta,depth,turn,pos,depth+1,turn));
			}
			else{
				v = Math.min(v, MaxVal(nextGameState,alpha,beta,depth+1,(turn+1)%2,pos,depth+1,turn));
				if(depth == 0 && parentgamestate.getInit_play()==1 && v<bestState.value)
				{
					bestState.gameState = nextGameState;
					bestState.value = v;
				}   
			}

			if(v<=alpha) {

				if(depth>0 && dfs - depth == 0  && pos<=parentgamestate.getNum_bins()+1)
					printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth,v,alpha,beta);
				else if(depth>0 && dfs - depth  > 0  && pos<=parentgamestate.getNum_bins()+1)
					printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);	
				else if(depth==0 && dfs - depth > 0 && pos<=parentgamestate.getNum_bins()+1)
					printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);
				return v;}
			beta = Math.min(beta, v);

			if(depth>0 && dfs - depth == 0  && pos<=parentgamestate.getNum_bins()+1)
				printTraverseLog((turn == 0)?"A"+parentPos:"B"+parentPos,depth,v,alpha,beta);
			else if(depth>0 && dfs - depth  > 0  && pos<=parentgamestate.getNum_bins()+1)
				printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);	
			else if(depth==0 && dfs - depth > 0 && pos<=parentgamestate.getNum_bins()+1)
				printTraverseLog((turn == 0)?"B"+parentPos:"A"+parentPos,depth+1,v,alpha,beta);
			else if((depth==0 && dfs - depth  == 0 && pos==parentgamestate.getNum_bins()+1)||(depth==0 && dfs - depth  == 0 && parentgamestate.isAnyMancaBeyondPos(pos, turn)==0))
				printTraverseLog("root",depth,v,alpha,beta);
		}
		return v;
	}

	StringBuilder printBoard(GameState gamestate){
		StringBuilder nextState= new StringBuilder();
		int i;
		String p1="",p2="";
		for(i = 2;i<=gamestate.getNum_bins()+1;i++)
			p1 = p1.concat(String.valueOf(gamestate.checkPit(i,0))+" ");
		for(i = 2;i<=gamestate.getNum_bins()+1;i++)
			p2 = p2.concat(String.valueOf(gamestate.checkPit(i,1))+" ");

		nextState.append(p2).append(System.lineSeparator());
		nextState.append(p1).append(System.lineSeparator());
		nextState.append(gamestate.checkManca(1)).append(System.lineSeparator());
		nextState.append(gamestate.checkManca(0)).append(System.lineSeparator());
		return nextState;
	}

	void printTraverseLog(String node,int depth,double value,double alpha,double beta) throws IOException{
		StringBuilder sb = new StringBuilder();
		sb.append(node).append(",");
		sb.append(depth).append(",");
		if(value == Double.NEGATIVE_INFINITY || value == Double.POSITIVE_INFINITY)
			if(initPlay==0)
				sb.append(value).append(",");
			else
				sb.append(-1*value).append(",");
		else
			if(initPlay==0)
				sb.append((int)value).append(",");
			else
				sb.append(-1*(int)value).append(",");

		if(initPlay == 0){
			if(alpha == Double.NEGATIVE_INFINITY || alpha == Double.POSITIVE_INFINITY)
				sb.append(alpha).append(",");
			else
				sb.append((int)alpha).append(",");


			if(beta == Double.NEGATIVE_INFINITY || beta == Double.POSITIVE_INFINITY)
				sb.append(beta);
			else
				sb.append((int)beta);
		}

		else{
			if(beta == Double.NEGATIVE_INFINITY || beta == Double.POSITIVE_INFINITY)
				sb.append(-1*beta).append(",");
			//sb.append(-1*alpha);
			else
				sb.append(-1*(int)beta).append(",");
			//sb.append(-1*(int)alpha);

			if(alpha == Double.NEGATIVE_INFINITY || alpha == Double.POSITIVE_INFINITY)
				sb.append(-1*alpha);
			//sb.append(-1*beta).append(",");
			else
				sb.append(-1*(int)alpha);
			//sb.append(-1*(int)beta).append(",");
		}
		w2.append(sb.toString()).append(System.lineSeparator());
		//	System.out.println(count++);
	}

}

class GameState{

	private int board[];
	private int idx_m1;
	private int idx_m2;
	private int num_bins;
	private int size_board;
	private int total_pebbles;
	private int init_play;
	private boolean anoth_chance;
	private int lastPosMoved = 1; 
	private boolean illegalMove = false;
	private boolean specialCase = false;


	public GameState makeNewGameStateInstance(GameState gamestateref){
		GameState gamestate = new GameState();
		gamestate.board = gamestateref.board.clone();
		gamestate.idx_m1 = gamestateref.idx_m1;
		gamestate.idx_m2 = gamestateref.idx_m2;
		gamestate.num_bins = gamestateref.num_bins;
		gamestate.size_board = gamestateref.size_board;
		gamestate.total_pebbles = gamestateref.total_pebbles;
		gamestate.init_play = gamestateref.init_play;
		gamestate.anoth_chance = gamestateref.anoth_chance;
		gamestate.specialCase = gamestateref.specialCase;
		return gamestate;

	}

	public GameState setWorstState(int turn){

		GameState gamestate = new GameState();
		gamestate.board = new int[4];
		gamestate.idx_m1 = 1;
		gamestate.idx_m2 = 3;

		if(turn==0){
			gamestate.board[gamestate.idx_m1] = Integer.MIN_VALUE/2;
			gamestate.board[gamestate.idx_m2]= Integer.MAX_VALUE/2;
		}
		else
		{
			gamestate.board[gamestate.idx_m2] = Integer.MIN_VALUE/2;
			gamestate.board[gamestate.idx_m1]= Integer.MAX_VALUE/2;
		}


		return gamestate;
	}


	public int checkPit(int pos,int turn){
		int pitValue = (turn == 0) ? board[pos-2] : board[2*num_bins-(pos-2)];
		return pitValue;
	}

	public int checkManca(int turn){
		if(turn==0)
			return board[idx_m1];
		else
			return board[idx_m2];
	}

	/**
	 * @return the illegalMove
	 */
	public boolean checkIllegalMove() {
		return illegalMove;
	}

	public void changeIllegalVar(){
		this.illegalMove = false;
	}

	/**
	 * @return the lastPosMoved
	 */
	public int getLastPosMoved() {
		return lastPosMoved;
	}

	/**
	 * @return the anoth_chance
	 */
	public boolean haveAnoth_chance() {
		return anoth_chance;
	}

	/**
	 * @return the special_case
	 */
	public boolean isSpecial_Case() {
		return specialCase;
	}

	/**
	 * @return the num_bins
	 */
	public int getNum_bins() {
		return num_bins;
	}

	/**
	 * @return the curr_play
	 */
	public int getInit_play() {
		return init_play;
	}

	/**
	 * @return the total_pebbles
	 */
	public int getTotal_pebbles() {
		return total_pebbles;
	}

	/**
	 * @return the pebbles_p1
	 */
	public int getPeb_p1_side() {
		int total = 0;
		for(int i = 0;i<num_bins;i++)
			total+=board[i];
		return total;
	}

	/**
	 * @return the pebbles_p2
	 */
	public int getPeb_p2_side() {
		int total = 0;
		for(int i = num_bins+1;i<=2*num_bins;i++)
			total+=board[i];
		return total;
	}

	public int isAnyMancaBeyondPos(int pos, int turn){
		int total = 0;
		if(turn == 0){
			for(int i = pos -2 +1;i<num_bins;i++)
				total+=board[i];
			return total;
		}
		else{
			for(int i = (2*num_bins)-(pos-2);i<=2*num_bins;i++)
				total+=board[i];
			return getPeb_p2_side() - total;
		}		
	}

	public void initBoard(int curr_play,int p1[],int p1manca,int p2[],int p2manca){
		size_board = p1.length+1+p2.length+1;
		board = new int[size_board];

		int i,j;
		for(i=0;i<p1.length;i++)
		{
			board[i] = p1[i];
			total_pebbles+=board[i];
		}

		idx_m1 = i;
		board[i] = p1manca;
		total_pebbles+=p1manca;

		for(j = i+1;j<=2*p2.length;j++){
			board[j] = p2[j-i-1];
			total_pebbles+=board[j];
		}

		idx_m2 = j;
		board[j] = p2manca; 
		total_pebbles+=p2manca;

		num_bins = p1.length;
		this.init_play = curr_play;
		anoth_chance = false;
		specialCase = false;

	}

	//add the finishing condition when all the pits in the opponents side are empty
	public GameState nextLegalState(GameState currState,int curr_play,int move_pos){  //move_pos lies  between 2 to num of bins +1
		GameState gameState = currState;

		if(move_pos<2 && move_pos > gameState.num_bins+1){
			System.out.println("Illegal move, move out of board");
			gameState.anoth_chance = false;
			//currState.illegalMove = true;
			return gameState;
		}

		if(curr_play == 0){

			//finishing move
			if(gameState.getPeb_p2_side()==0)
			{

				for(int i = 0;i<gameState.getNum_bins();i++)
				{
					gameState.board[gameState.idx_m1]+= gameState.board[i];
					gameState.board[i] = 0;
				}

				gameState.anoth_chance = false;
				return gameState;
			}

			if(gameState.board[move_pos-2] == 0){   
				System.out.println("Can't make this move, zero pebbls in the pit");
				gameState.anoth_chance = false;
				return gameState;
			}

			else{
				int pebbles = gameState.board[move_pos-2];
				int i;
				gameState.board[move_pos-2] = 0;
				for(i = move_pos-2+1;pebbles>0;i++){

					if(i%gameState.board.length == gameState.idx_m2)
						continue;
					gameState.board[i%gameState.board.length]++;
					pebbles--;
				}

				//condition where last pebble lies in empty pit on our side
				//No need to check if i-1==idx_m2, will never happen
				if((i-1)%gameState.board.length<=gameState.num_bins-1 && gameState.board[(i-1)%gameState.board.length]==1)
				{
					gameState.board[gameState.idx_m1]+= gameState.board[2*gameState.num_bins-((i-1)%gameState.board.length)]+1;
					gameState.board[2*gameState.num_bins-((i-1)%gameState.board.length)] = 0;
					gameState.board[(i-1)%gameState.board.length] = 0;
				}

				if((i-1)%gameState.board.length == gameState.idx_m1 && gameState.getPeb_p1_side()!=0)
					//if((i-1)%gameState.board.length == gameState.idx_m1)
					gameState.anoth_chance = true;

				else
					gameState.anoth_chance = false;

				// SPECIAL CASE ************************//
				if((i-1)%gameState.board.length == gameState.idx_m1 && gameState.getPeb_p1_side()==0)
					gameState.specialCase = true;
				//***********************************************//

				//if in the current move, all the pits get empty
				if(gameState.getPeb_p1_side()==0)
				{
					for(int j = gameState.getNum_bins()+1;j<=2*gameState.getNum_bins();j++)
					{
						gameState.board[gameState.idx_m2]+= gameState.board[j];
						gameState.board[j] = 0;
					}

					gameState.anoth_chance = false;
					return gameState;
				}

				if(gameState.getPeb_p2_side()==0)
				{

					for(int k = 0;k<gameState.getNum_bins();k++)
					{
						gameState.board[gameState.idx_m1]+= gameState.board[k];
						gameState.board[k] = 0;
					}

					gameState.anoth_chance = false;
					return gameState;
				}



				gameState.lastPosMoved = move_pos;

				return gameState;
			}

		}

		else if(curr_play == 1){

			//finishing move
			if(gameState.getPeb_p1_side()==0)
			{
				for(int i = gameState.getNum_bins()+1;i<=2*gameState.getNum_bins();i++)
				{
					gameState.board[gameState.idx_m2]+= gameState.board[i];
					gameState.board[i] = 0;
				}

				gameState.anoth_chance = false;
				return gameState;
			}

			if(gameState.board[(2*gameState.num_bins)-(move_pos-2)] == 0){   
				System.out.println("Can't make this move, zero pebbls in the pit");
				gameState.anoth_chance = false;
				//currState.illegalMove = true;
				return gameState;
			}
			else{
				int pos = (2*gameState.num_bins)-(move_pos-2);
				int pebbles = gameState.board[pos];
				int i;
				gameState.board[pos] = 0;
				for(i = pos+1;pebbles>0;i++){

					if(i%gameState.board.length == gameState.idx_m1)
						continue;
					gameState.board[i%gameState.board.length]++;
					pebbles--;
				}

				//condition where last pebble lies in empty pit on our side
				//No need to check if i-1==idx_m1, will never happen
				if((i-1)%gameState.board.length>=gameState.num_bins && (i-1)%gameState.board.length<=2*gameState.num_bins && gameState.board[(i-1)%gameState.board.length]==1)
				{
					gameState.board[gameState.idx_m2]+= gameState.board[2*gameState.num_bins-((i-1)%gameState.board.length)]+1;
					gameState.board[2*gameState.num_bins-((i-1)%gameState.board.length)] = 0;
					gameState.board[(i-1)%gameState.board.length] = 0;
				}

				if((i-1)%gameState.board.length == gameState.idx_m2 && gameState.getPeb_p2_side()!=0)
					//if((i-1)%gameState.board.length == gameState.idx_m2) 
					gameState.anoth_chance = true;
				else
					gameState.anoth_chance = false;


				// SPECIAL CASE ************************//
				if((i-1)%gameState.board.length == gameState.idx_m2 && gameState.getPeb_p2_side()==0)
					gameState.specialCase = true;
				//***********************************************//

				//if in the current move, all the pits get empty
				if(gameState.getPeb_p2_side()==0)
				{

					for(int j = 0;j<gameState.getNum_bins();j++)
					{
						gameState.board[gameState.idx_m1]+= gameState.board[j];
						gameState.board[j] = 0;
					}

					gameState.anoth_chance = false;
					return gameState;
				}

				if(gameState.getPeb_p1_side()==0)
				{
					for(int k =gameState.getNum_bins()+1;k<=2*gameState.getNum_bins();k++)
					{
						gameState.board[gameState.idx_m2]+= gameState.board[k];
						gameState.board[k] = 0;
					}

					gameState.anoth_chance = false;
					return gameState;
				}

				return gameState;
			}
		}

		System.out.println("Illegal Player");
		return null; 
	}


	public int evaluation(int turn){
		int eval;
		eval = turn == 0? board[idx_m1] - board[idx_m2] : board[idx_m2] - board[idx_m1];
		return eval;
	}

	public int evaluationMiniMax(){
		int eval;
		eval = board[idx_m1] - board[idx_m2];
		return eval;
	}


}


public class mancala {
	public static void main(String args[]) throws NumberFormatException, IOException{

		long starttime = System.currentTimeMillis();
		int task;
		int myPlayer;
		int cutOffDepth;
		String boardStateP2[];
		String boardStateP1[];
		int p2[];
		int p1[];
		int p2Manca;
		int p1Manca;
		FileReader filereader;
		FileWriter filewriter1;
		FileWriter filewriter2;
		StringBuilder string[];

		if(args.length>0){
			filereader = new FileReader(args[0]);
			//System.out.println(args[1]);
		}

		else
		{
			filereader = null;
			System.err.println("File Not Found");
			System.exit(0);

		}
		BufferedReader br = new BufferedReader(filereader);

		//Taking Inputs
		task = Integer.parseInt(br.readLine());
		myPlayer = Integer.parseInt(br.readLine())-1;
		cutOffDepth = Integer.parseInt(br.readLine());
		boardStateP2 = br.readLine().split(" ");
		boardStateP1 = br.readLine().split(" ");
		p2Manca = Integer.parseInt(br.readLine());
		p1Manca = Integer.parseInt(br.readLine());

		p2 = new int [boardStateP2.length];
		p1 = new int [boardStateP1.length];
		for(int i = 0;i<boardStateP2.length;i++){
			p2[p2.length-i-1] = Integer.parseInt(boardStateP2[i]);
			p1[i] = Integer.parseInt(boardStateP1[i]);
		}

		//Initializing game state
		GameState gameState = new GameState();
		gameState.initBoard(myPlayer,p1,p1Manca,p2,p2Manca);

		//initializing filewriter
		filewriter1 = new FileWriter("next_state.txt");
		filewriter2 = new FileWriter("traverse_log.txt");
		BufferedWriter wr1 = new BufferedWriter(filewriter1);
		BufferedWriter wr2 = new BufferedWriter(filewriter2);


		switch(task){
		case 1: wr1.write(new GreedySearch().genStates(gameState).toString());
		break;
		case 2: new MiniMaxSearch().genInitStates(gameState, cutOffDepth,wr1,wr2);
		break;
		case 3: new AlphaBetaSearch().AlphaBetaSearchUtil(gameState,cutOffDepth,wr1,wr2);
		break;
		}

		wr1.close();
		wr2.close();
		System.out.println("Done");
		System.out.println(System.currentTimeMillis() - starttime);

	}
}
