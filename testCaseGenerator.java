import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

public class testCaseGenerator {
public static void main(String...args) throws IOException{
	String algorithm;
	String sourcenode;
	Set<String> nodes = new HashSet<>();
	ArrayList<String> list_nodes = new ArrayList<>();
	ArrayList<String> dest_nodes_list = new ArrayList<>();
	ArrayList<String> edges = new ArrayList<>();
    int no_of_nodes = 2000;
    int xxx;
	
    String algos[] = {"UCS","DFS","BFS"};
    char arr[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ".toCharArray();
    Random random = new Random();
    int len_of_node;
    StringBuilder node_name ;
    
    //Generating node names
    while(nodes.size()<no_of_nodes){
    	node_name= new StringBuilder();
    	len_of_node = random.nextInt(4)+1;
    	for(int i = 0; i<len_of_node;i++)
    		node_name.append(arr[random.nextInt(arr.length)]);
    	nodes.add(node_name.toString());
    	//System.out.println("!");
    }
    list_nodes.addAll(nodes);
    
    
    //Generating algorithm
    algorithm = algos[random.nextInt(algos.length)];
    
    //Selecting a source, destinations
    int index;
    index = random.nextInt(nodes.size());
    sourcenode = list_nodes.get(index);
    list_nodes.remove(index);
    
    
    int no_of_dest = random.nextInt(4); //at max 100 dest
    for(int i=0; i<no_of_dest;i++){
    	index = random.nextInt(list_nodes.size());
    	dest_nodes_list.add(list_nodes.get(index));
    	 list_nodes.remove(index);
    		//System.out.println("@");
    }
    
    //Generating edges
    //int Max_Edges = 10000;
    String edge;
    Set<Integer> indices;
    Set<String> edges_set;
    String s,d;
    //1) Generating edges from source to middle
     indices = new HashSet<>();
    while(indices.size()<(int)0.2*(no_of_nodes-no_of_dest-1)+10){
    	indices.add(random.nextInt(list_nodes.size()));
    	//System.out.println("#");
    }
    for(int x : indices){
    	xxx = random.nextInt(50)+1;
    	edge = sourcenode + " " + list_nodes.get(x)+" "+xxx+" "+"0";
    	edges.add(edge);
    	//System.out.println("$");
    }
    

    //2) Generating edges from Middle to Middle
    edges_set = new HashSet<>();
   
   
   int temp = random.nextInt((int) (0.5*no_of_nodes*(no_of_nodes-1)+100));
   int  num_mid_edge = 22000;// 400000 < temp ? 400000 : temp;
   while(edges_set.size()<num_mid_edge)
    {
    	s = list_nodes.get(random.nextInt(list_nodes.size()));
    	d = list_nodes.get(random.nextInt(list_nodes.size()));
    	xxx = random.nextInt(50)+1;
    	edges_set.add(s+" "+d+" "+xxx+" "+"0");  	
    //System.out.println("%");
    }
    
   edges.addAll(edges_set);
   
   //3) Generating edges between middle and dest 
   edges_set = new HashSet<>();
  int num_des_edge = 4;//random.nextInt((int) (0.02*no_of_nodes*(no_of_nodes-1)+100));
 
   while(edges_set.size()<num_des_edge)
   {
   	s = list_nodes.get(random.nextInt(list_nodes.size()));
   	d = dest_nodes_list.get(random.nextInt(dest_nodes_list.size()));
   	xxx = random.nextInt(50)+1;
   	edges_set.add(s+" "+d+" "+xxx+" "+"0");  	
  //  System.out.println("^");
   }
   
   edges.addAll(edges_set);
   
//    for(String x : nodes)
//    	System.out.println(x);
    
   FileWriter filewriter;
   filewriter = new FileWriter("inputGenerator.txt");
   BufferedWriter wr = new BufferedWriter(filewriter);
   wr.write("1");
   wr.newLine();
   wr.write(algorithm);
   wr.newLine();
   wr.write(sourcenode);
   wr.newLine();
   for(int i = 0; i<dest_nodes_list.size();i++)
   {
	   if(i == dest_nodes_list.size()-1)
		   wr.write(dest_nodes_list.get(i));
	   else{
	   wr.write(dest_nodes_list.get(i));
	   wr.write(" ");
	   }
   }
   wr.newLine();
   for(int i = 0; i<list_nodes.size();i++)
   {
	   if(i == list_nodes.size()-1)
		   wr.write(list_nodes.get(i));
	   else{
	   wr.write(list_nodes.get(i));
	   wr.write(" ");
	   }
   }
   wr.newLine();
   wr.write(Integer.toString(edges.size()));
   wr.newLine();
   for(String x : edges){
	   wr.write(x);
	   wr.newLine();
   }
   wr.write(Integer.toString(random.nextInt(24)));
   wr.close();
	System.out.println("Done");
}
}
