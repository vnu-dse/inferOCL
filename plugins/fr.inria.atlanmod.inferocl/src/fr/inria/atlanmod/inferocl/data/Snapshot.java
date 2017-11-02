package fr.inria.atlanmod.inferocl.data;

import java.util.ArrayList;
import java.util.List;

public class Snapshot {
	private String id;
	private boolean isValidSnapshot;
	private String snapshotStr;
	
	public Snapshot(boolean isValidSnapshot, String snapshotStr){
		this.isValidSnapshot = isValidSnapshot;
		String str = snapshotStr.replaceAll(",\\s*_\\s*,", ",oclUndefined,");
		str = str.replaceAll(",\\s*_\\s*,", ",oclUndefined,");
		str = str.replaceAll(",\\s*_\\s*\\)", ",oclUndefined)");		
		this.snapshotStr = str;
	}
	public boolean isValidSnapshot(){
		return isValidSnapshot;
	}
	public String getId(){
		return this.id;
	}
	public String toString(){
		return snapshotStr;
	}
	public static void main(String[]arg){
		//String s = "hanh,  _   , chao em ";
		//System.out.println( s.replaceAll(",\\s*_\\s*,", ",oclUndefined,") );
		List<String> s = new ArrayList<String>();
		s.add("hanh");s.add("em");s.add("ta");
		System.out.println(s.contains("ta"));
	}
}
