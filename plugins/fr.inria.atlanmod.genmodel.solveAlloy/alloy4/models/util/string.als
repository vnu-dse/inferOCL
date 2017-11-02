module util/string
open util/sequniv
open util/boolean as Bool
/*
 * A collection of utility functions for using Strings in Alloy.
 */



abstract sig AlphaNumericCharacter{}
abstract sig NumericCharacter extends AlphaNumericCharacter{}
abstract sig LowerCaseCharacter extends AlphaNumericCharacter{ upper : one UpperCaseCharacter}
abstract sig UpperCaseCharacter extends AlphaNumericCharacter{ lower : one LowerCaseCharacter}
abstract sig SpecialCharacter extends AlphaNumericCharacter{}

one sig c_NL, //New Line 
			 c_TAB, //Tab Space
		     c_Space, //White Space
			 c_Excl, //Exclamation Mark !
			 c_DQ, //Double Quotes "
 			 c_Hash, // Hash Mark #
			 c_Dollar, // Dollar Sign $
			 c_Percentage, //Percentage %
			 c_And, //And &
			 c_SQ, //Single Quote '
			 c_LP, //Left Paranthesis (
			 c_RP, //Right Paranthesis )
			 c_Star, // Star *
 			 c_Plus, // Plus +
			 c_Comma, // Comma ,
 			 c_Hyphen, // Hypehn -
			 c_FS, //Full Stop .
			 c_RS, //Right Slash /
			 c_Colon, //Colon :
			 c_SColon, //Semi-colon ;
			 c_LT, //Less Than <
			 c_EQ, //Equal =
			 c_GT, //Greater Than
			 c_QM, //Question mark ?
			 c_At, //At Mark @
			 c_LSB, //Left Square Bracket [
			 c_LS, //Left Slash \
			 c_RSB, //Right Square Bracket
			 c_CF, //Circonflex ^
			 c_US, //Underscore _
			 c_AP, //Apostrophe `
			 c_LCB, //Left Curly Bracket {
			 c_RCB, //Right Curly Bracket }
			 c_Pipe, //Pipe |
			 c_Tilde //Tilde ~
			 extends SpecialCharacter {}
			 
				


one sig c_0, 
			c_1, 
			c_2, 
			c_3, 
			c_4,
			c_5,
			c_6,
			c_7,
			c_8,
			c_9
			extends NumericCharacter{} 

one sig c_A, 
			c_B, 
			c_C, 
			c_D, 
			c_E,
			c_F,
			c_G,
			c_H,
			c_I,
			c_J,
			c_K,
			c_L, 
			c_M,
			c_N,
			c_O,
			c_P,
			c_Q,
			c_R,
			c_S,
			c_T,
			c_U,
			c_V,
			c_W,
			c_X,
			c_Y,
			c_Z
			extends UpperCaseCharacter{} 

one sig c_a, 
			c_b, 
			c_c, 
			c_d, 
			c_e,
			c_f,
			c_g,
			c_h,
			c_i,
			c_j,
			c_k,
			c_l, 
			c_m,
			c_n,
			c_o,
			c_p,
			c_q,
			c_r,
			c_s,
		    c_t,
			c_u,
			c_v,
			c_w,
			c_x,
			c_y,
			c_z
			extends LowerCaseCharacter{} 


sig String {value : seq AlphaNumericCharacter}

fact setLowerCase
{
c_A.lower = c_a and 
c_B.lower = c_b and
c_C.lower = c_c and
c_D.lower = c_d and
c_E.lower = c_e and
c_F.lower = c_f and
c_G.lower = c_g and
c_H.lower = c_h and
c_I.lower = c_i and
c_J.lower = c_j and
c_K.lower = c_k and
c_L.lower = c_l and
c_M.lower = c_m and
c_N.lower = c_n and
c_O.lower = c_o and
c_P.lower = c_p and
c_Q.lower = c_q and
c_R.lower = c_r and
c_S.lower = c_s and
c_T.lower = c_t and
c_U.lower = c_u and
c_V.lower = c_v and
c_W.lower = c_w and
c_X.lower = c_x and
c_Y.lower = c_y and
c_Z.lower = c_z 
}

fact setUpperCase
{
c_a.upper = c_A and
c_b.upper = c_B and
c_c.upper = c_C and
c_d.upper = c_D and
c_e.upper = c_E and
c_f.upper = c_F and
c_g.upper = c_G and
c_h.upper = c_H and
c_i.upper = c_I and
c_j.upper = c_J and
c_k.upper = c_K and
c_l.upper = c_L and
c_m.upper = c_M and
c_n.upper = c_N and
c_o.upper = c_O and
c_p.upper = c_P and
c_q.upper = c_Q and
c_r.upper = c_R and
c_s.upper = c_S and
c_t.upper = c_T and
c_u.upper = c_U and
c_v.upper = c_V and
c_w.upper = c_W and
c_x.upper = c_X and
c_y.upper = c_Y and
c_z.upper = c_Z 
}

//Size of a String atom returned

fun size[string : String] : Int 
{
      #string.value
}

//Concatenation String3.value = String1+ String2
pred concat[string1: String,string2: String,string3:String]
{

   string3.value = string1.value.append[string2.value] 
}

//Substring between lower and upper, String2.value = substring(a,b,String1)

pred substring[lower : Int, upper: Int, string1: String , string2:String]
{
		string2.value=string1.value.subseq[lower,upper]
}


//To Lower for a String

pred toLower [string1 : one String, string2: one String]
{
   #string1.value=#string2.value and all i:Int | (i>=0 and i<#string1.value=> string2.value[i]=string1.value[i].lower)
}

//To Upper for a String

pred toUpper[string1 : one String, string2: one String]
{
   #string1.value=#string2.value and all i:Int | (i>=0 and i<#string1.value=> string2.value[i]=string1.value[i].upper)
}
//Two String isEqual returns Bool 

pred isEqual[string1:String, string2:String, Value:Bool]
{
string1.value = string2.value => Value = True else Value=False
}
//Two Strings are not Equal returns Bool

pred isNotEqual[string1:String, string2:String, Value: Bool]
{
string1.value != string2.value => Value= True else Value=False
}

//Two String strings always equal

pred equal[string1:String, string2:String]
{
(string1.value = string2.value) 
}

//Two String strings always different
pred notEqual[string1 : String, string2: String] 
{
not(string1.value = string2.value) 
}

//A set of String atoms strings are all unique
pred uniqueStrings[strings: set String]
{

all str1:strings, str2:strings |  str1 = str2 => str1.value in str2.value

}

//A Set of String atoms strings are all unique and of a fixed length
pred uniqueStringsFixedLength[strings: set String, length: Int]
{
all str1:strings, str2:strings | str1.value = str2.value => str1 =str2 and #str1.value = length and #str2.value =length
}



sig Example
{
a: String,
b: String,
c: String,
d: String,
e: String,
f: set String,
g:String,
h: String,
i: Bool
}

pred Test
{size[Example.a]>5 and isNotEqual[Example.a,Example.b,Example.i] and toUpper[Example.a, Example.h] and #Example.f >5 and size[Example.b]>5 and uniqueStringsFixedLength[Example.f,5] and equal[Example.d,Example.e] and concat[Example.a , Example.b,Example.c] and notEqual[Example.a, Example.b] and substring[2,3,Example.c,Example.d]}

pred Test1
{size[Example.a]=5 and size[Example.b]=5 concat[Example.a , Example.b,Example.c] and notEqual[Example.a,Example.b] }

run Test for 20 but exactly 10 String, exactly 1 Example,  5 int

