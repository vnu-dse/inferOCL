package fr.inria.atlanmod.inferocl.data;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * @author duc-hanh.dang
 */

public class Invariant{
	private String patternId;
	private String patternName;
	private String matchingPara;
	private String oclInv;
	private List<String> labelCls;
	private List<String> labelLink;
	private List<String> labelAttr;

	public Invariant(String patternId, String patternName, String matchingPara, String oclInv,
			List<String> cls, List<String> link, List<String> attr){
		this.patternId = patternId;
		this.patternName = patternName;
		this.matchingPara = matchingPara;
		this.oclInv = oclInv;
		this.labelCls = cls;
		this.labelLink = link;
		this.labelAttr = attr;
	}

	public String getPatternId() {
		return patternId;
	}
	public void setPatternId(String patternId) {
		this.patternId = patternId;
	}
	public String getPatternName() {
		return patternName;
	}
	public void setPatternName(String patternName) {
		this.patternName = patternName;
	}
	public String getMatchingPara() {
		return matchingPara;
	}
	public void setMatchingPara(String matchingPara) {
		this.matchingPara = matchingPara;
	}
	public String getOclInv() {
		return oclInv;
	}
	public void setOclInv(String oclInv) {
		this.oclInv = oclInv;
	}
	public List<String> getLabelCls(){
		return labelCls;
	}
	public List<String> getLabelLink(){
		return labelLink;
	}
	public List<String> getLabelAttr(){
		return labelAttr;
	}
	public static List<List<Invariant>> getInvLists(File retFile) {
		try {
			List<List<Invariant>> invLists = new ArrayList<List<Invariant>>();
			BufferedReader readbuffer = new BufferedReader(new FileReader(retFile) );
			String strRead;
			strRead = readbuffer.readLine();
			int allINV = Integer.valueOf(strRead).intValue();
			int size;
			List<Invariant> invs;
			Set<Set<String>> invSets = new HashSet<Set<String>>();
			Set<String> invSet;
			for(int i = 0; i < allINV; i++){
				strRead = readbuffer.readLine();
				size = Integer.valueOf(strRead).intValue();
				invs = new ArrayList<Invariant>();
				invSet = new HashSet<String>();
				for(int j = 0; j < size; j++){					
					strRead=readbuffer.readLine();					
					String attr[] = strRead.split("\t");
					String patIdStr = attr[0];
					String patName = attr[1];
					String paraStr = attr[2].replace("'", "\"");
					String oclStr = attr[3].replace("....","\n");
					List<String> labelCls = new ArrayList<String>();
					List<String> labelLink = new ArrayList<String>();
					List<String> labelAttr = new ArrayList<String>();
					int numCls = Integer.valueOf(attr[4]).intValue();
					int idx = 5;
					for(int k = 0; k< numCls; k++,idx++){
						labelCls.add( attr[idx] );
					}
					int numLink = Integer.valueOf(attr[idx]).intValue();
					idx++;
					for(int k = 0; k< numLink; k++,idx++){
						labelLink.add( attr[idx] );
					}
					int numAttr = Integer.valueOf(attr[idx]).intValue();
					idx++;
					for(int k = 0; k< numAttr; k++,idx++){
						labelAttr.add( attr[idx] );
					}
					if(! invSet.contains(oclStr)){
					  invs.add(new Invariant(patIdStr,patName,paraStr,oclStr,labelCls,labelLink,labelAttr));
					  invSet.add(oclStr);
					}else{
						//System.out.println("Lap one" + oclStr);
					}
				}
				if(! invSets.contains(invSet)){
					invLists.add(invs);
					invSets.add(invSet);
				}else{
					//System.out.println("Lap group" + invSet.toString());
				}
			}
			readbuffer.close();
			System.out.println("The number of candidates is " + invLists.size());
			return invLists;
		} catch (IOException e) {		
			e.printStackTrace();
			return null;
		}
	}

	/*@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((oclInv == null) ? 0 : oclInv.hashCode());
		return result;
	}*/

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Invariant other = (Invariant) obj;
		if (oclInv == null) {
			if (other.oclInv != null)
				return false;
		} else if (!oclInv.equals(other.oclInv))
			return false;
		return true;
	}
}