import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Queue;
import java.util.TreeMap;


class Interval{

	int start_time;
	int end_time;

	public int getStart_time() {
		return start_time;
	}

	public int getEnd_time() {
		return end_time;
	}
}


class intervalComarator implements Comparator<Interval>{

	@Override
	public int compare(Interval i1, Interval i2) {
		// TODO Auto-generated method stub
		return i1.end_time - i2.end_time;
	}

}

class Vertex{

	String nodeName;
	String type; // Source node = s,Destination node = d, Middle node = m Sentinel node = x
	Boolean visited;

	public Vertex(String nodeName, String type){
		this.type = type;
		this.nodeName = nodeName;
		this.visited = false;
	}

	/**
	 * @return the nodeName
	 */
	public String getNodeName() {
		return nodeName;
	}

	/**
	 * @return the type
	 */
	public String getType() {
		return type;
	}

	/**
	 * @return the visited
	 */
	public Boolean getVisited() {
		return visited;
	}


}


class vertexComparator implements Comparator<Vertex>
{

	@Override
	public int compare(Vertex v1, Vertex v2) {
		return v1.nodeName.compareTo(v2.nodeName);
	}

}

class vertexComparatorReverse implements Comparator<Vertex>
{

	@Override
	public int compare(Vertex v1, Vertex v2) {
		return v2.nodeName.compareTo(v1.nodeName);
	}

}

class Edge{

	String sourceNode;
	String endNode;
	int length;
	ArrayList<Interval> offTimes;

	/**
	 * @return the sourceNode
	 */
	public String getSourceNode() {
		return sourceNode;
	}
	/**
	 * @return the endNode
	 */
	public String getEndNode() {
		return endNode;
	}
	/**
	 * @return the length
	 */
	public int getLength() {
		return length;
	}
	/**
	 * @return the offTimes
	 */
	public ArrayList<Interval> getOffTimes() {
		return offTimes;
	}

}

class Graph{

	HashMap<String,Vertex> list_vertices ;
	HashMap<String,ArrayList<Edge>> list_edges ;
	Vertex source;
	String sourceVertex;

	/**
	 * @return the source
	 */
	public Vertex getSource() {

		source = list_vertices.get(sourceVertex);
		return source;
	}

	Graph(String s){
		this.sourceVertex = s;
		list_vertices = new HashMap<>();
		list_edges = new HashMap<>();

	}

	public void addVertices(String source,String[]destination,String[]middle){


		list_vertices.put(source, new Vertex(source,"s"));

		for(String dest : destination){
			list_vertices.put(dest, new Vertex(dest,"d"));
		}

		for(String mid : middle){
			list_vertices.put(mid, new Vertex(mid,"m"));
		}
	}
	public void addEdges(ArrayList<String> edge){

		for(String edgeInfo : edge){

			Edge e = new Edge();
			String [] temp = edgeInfo.split(" ");
			String startnode = temp[0];
			String endnode = temp[1];

			if(!list_vertices.containsKey(startnode)||!list_vertices.containsKey(endnode)) //Handle the condition where edge may contain a non existent node
				continue;

			int length = Integer.parseInt(temp[2]);
			int offtime_intervals = Integer.parseInt(temp[3]);
			ArrayList<Interval> offTimes = new ArrayList<Interval>();

			for(int i=4 ; i<4+offtime_intervals && i< temp.length ; i++){
				String interval_[] = temp[i].split("-");
				Interval interval = new Interval();
				interval.start_time = Integer.parseInt(interval_[0])%24;
				interval.end_time = Integer.parseInt(interval_[1])%24;
				offTimes.add(interval);
			}

			//Collections.sort(offTimes,new intervalComarator());

			e.sourceNode = startnode;
			e.endNode = endnode;
			e.length = length;
			e.offTimes = offTimes;

			if(list_edges.containsKey(temp[0])){
				list_edges.get(temp[0]).add(e);
			}
			else{
				ArrayList<Edge> arrayList = new ArrayList<>();
				arrayList.add(e);
				list_edges.put(startnode, arrayList);
			}
		}

	}

}



class BFS{

	Queue<Vertex> queue;
	boolean found;
	int start_time;

	public BFS(int start_time){
		this.start_time = start_time;
		found = false;
	}

	public String compute(Graph graph){

		Vertex v,sentinel;
		ArrayList<Edge> edges;
		ArrayList<Vertex> children;
		int level = 0;
		String output = "";

		sentinel = new Vertex("sentinel","x");
		queue = new LinkedList<Vertex>();
		v = graph.getSource();
		queue.add(v);
		queue.add(sentinel);


		while(!queue.isEmpty()){


			v = queue.remove();

			if(v.type.equals("x") && queue.peek()!=null)
			{
				//sentinel encountered
				level++;
				queue.add(sentinel);
				continue;
			}

			if(v.visited == true)
				continue;

			v.visited = true;

			if(v.type.equals("d")){

				//System.out.println(v.nodeName+" "+(level+start_time)%24);
				output = output.concat(v.nodeName+" "+(level+start_time)%24);  
				found = true;
				break;
			}

			if((edges = graph.list_edges.get(v.nodeName))!=null){

				children = new ArrayList<Vertex>();

				for(Edge e : edges){

					children.add(graph.list_vertices.get(e.endNode));
				}

				Collections.sort(children, new vertexComparator());

				for(Vertex child : children){

					if(!child.visited){

						queue.add(child);
					}
				}

			}

		}

		if(!found){
			//System.out.println("None");
			output = output.concat("None");
		}

		return output;
	}


}

class DFS{

	int start_time;
	Graph graph;
	String output = "";
	static boolean found;

	public DFS(int start_time){
		found = false;
		this.start_time = start_time;
	}

	public String compute(Graph graph){

		this.graph = graph;
		recursiveDFS(graph.getSource(),start_time);
		if(found)
			return output;
		output = output.concat("None");
		return output;
	}

	public void recursiveDFS(Vertex v,int cost){

		ArrayList<Edge>  list;
		ArrayList<Vertex> children;
		v.visited = true;


		if(v.type.equals("d")&&!found){
			//System.out.println(v.nodeName+" "+cost%24);
			found = true;
			output  = output.concat(v.nodeName+" "+cost%24);
			return;
		}

		if((list = graph.list_edges.get(v.nodeName))!=null){

			if(!list.isEmpty()){
				children = new ArrayList<>();
				for(Edge e: list){
					if(!graph.list_vertices.get(e.endNode).visited)
						children.add(graph.list_vertices.get(e.endNode));
				}

				Collections.sort(children, new vertexComparator());

				for(Vertex child : children){
					if(found)
						break;
					recursiveDFS(child,cost+1);
				}
			}
		}

	}


}

class UCS{

	TreeMap<Integer,ArrayList<Vertex>> p_Queue;
	int finalCost,start_time,current_cost;
	boolean found;

	public UCS(int start_time){
		this.start_time = start_time;
		found = false;
	}
	public String compute(Graph graph) {

		ArrayList<Vertex> value_list;
		ArrayList<Edge> edges;
		Vertex selected,generated;
		String output = "";

		p_Queue = new TreeMap<>();
		value_list = new ArrayList<>();
		value_list.add(graph.getSource());
		p_Queue.put(this.start_time, value_list);
		finalCost = Integer.MAX_VALUE;


		while(!p_Queue.isEmpty()){

			value_list = p_Queue.get(p_Queue.firstKey());

			if(value_list.size()>1){
				Collections.sort(value_list, new vertexComparator());
			}


			selected = value_list.get(0);  
			
			//if poped node is already visited
			if(selected.visited){
				if(value_list.size()==1)
					p_Queue.remove(p_Queue.firstKey());
				else
					value_list.remove(0);
				
				continue;
			}
			selected.visited = true;
			current_cost =  p_Queue.firstKey();



			if(value_list.size()==1){
				p_Queue.remove(p_Queue.firstKey());
			}

			else{
				value_list.remove(0);
			}	

			if(selected.type.equals("d"))
			{
				found = true;
				//System.out.println(selected.getNodeName()+" "+ current_cost%24);
				String write  = selected.getNodeName()+" "+ current_cost%24;
				output = output.concat(write);
				break;
			}

			edges = graph.list_edges.get(selected.nodeName);

			if(edges!=null){
				for(Edge e:edges){

					if(e.getOffTimes().isEmpty())
					{


						generated = graph.list_vertices.get(e.getEndNode());

						if(!generated.visited){
							if(p_Queue.containsKey(current_cost+e.length)){

								if(!(p_Queue.get(current_cost+e.length).contains(generated)))
								     p_Queue.get(current_cost+e.length).add(generated);
							}
							else {

								ArrayList<Vertex> temp = new ArrayList<>();
								temp.add(generated);
								p_Queue.put(current_cost+e.length, temp);

							}
						}
					}


					else{
						int i=0;
						generated = graph.list_vertices.get(e.getEndNode());

						if(!generated.visited){
							for(Interval v:e.getOffTimes()){

								if(((current_cost)%24>=v.getStart_time() && (current_cost)%24<=v.getEnd_time())){
									break;
								}

								i++;
							}

							if(i==e.getOffTimes().size()){


								if(p_Queue.containsKey(current_cost+e.length))
									if(!(p_Queue.get(current_cost+e.length).contains(generated))){
									p_Queue.get(current_cost+e.length).add(generated);
								}
								else{
									ArrayList<Vertex> temp = new ArrayList<>();
									temp.add(generated);
									p_Queue.put(current_cost+e.length, temp);
								}
							}
						}
					}
				}
			}

		}


		if(!found){
			//System.out.println("None");
			output = output.concat("None");
		}

		return output;
	}

}

public class waterFlow {

	@SuppressWarnings("finally")
	public static void main(String[]args) throws NumberFormatException, IOException{


		//long starttime = System.currentTimeMillis();
		FileReader filereader;
		FileWriter filewriter;

		if(args.length>0){
			filereader = new FileReader(args[0]);

			//System.out.println(args[0]);
		}


		else
		{
			filereader = null;
			System.err.println("File Not Found");
			System.exit(0);

		}

		//BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
		BufferedReader br = new BufferedReader(filereader);
		int testCases = Integer.parseInt(br.readLine().trim());
		filewriter = new FileWriter("output.txt");
		BufferedWriter wr = new BufferedWriter(filewriter);

		String algorithm,source;
		String destination[], middle[];
		int num_pipes, start_time;
		ArrayList<String> arrayList;

		while(testCases > 0 ){

		
			algorithm = br.readLine().trim();
			source = br.readLine().trim();
			destination = br.readLine().split(" ");
			middle = br.readLine().split(" ");
			num_pipes = Integer.parseInt(br.readLine().trim());
			arrayList= new ArrayList<>();

			for(int j = 0;j< num_pipes;j++){
				arrayList.add(br.readLine());
			}


			start_time = Integer.parseInt(br.readLine().trim());
			/*
			 * 
			 * Calling Logic is Here
			 * 
			 */

			Graph graph = new Graph(source);
			graph.addVertices(source,destination,middle);
			graph.addEdges(arrayList);
			
			switch(algorithm){
			case "BFS" : try{
				wr.write(new BFS(start_time).compute(graph));
			}
			catch(Exception ex){
				wr.write("None");
			}
			finally{
				wr.newLine();
			    break;
			}

			case "DFS" : try{wr.write(new DFS(start_time).compute(graph));}
			catch(Exception ex){
				wr.write("None");
			}
			finally{
				wr.newLine();
			    break;
			}

			case "UCS" : try{wr.write(new UCS(start_time).compute(graph));}
			catch(Exception ex){
				wr.write("None");
			}
			finally{
				wr.newLine();
			    break;
			}
			}



			if(br.readLine()==null)
				break;// test case ends here

			testCases--;
		}

		wr.close();

		System.out.println("Done");
		//System.out.println(System.currentTimeMillis() - starttime);
	}
}
