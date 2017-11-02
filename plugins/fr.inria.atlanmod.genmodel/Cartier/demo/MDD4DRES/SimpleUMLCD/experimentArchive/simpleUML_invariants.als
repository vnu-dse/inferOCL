
//Meta-model constraints//

//There must be no cyclic inheritance in the generated UML class diagram
fact noCyclicInheritance {
	no c: Class | c in c.^parent
}

//All the attributes in a Class must have unique attribute names
fact uniqueAttributeNames {
all c:Class |  all a1:  c.attrs , a2 : c.attrs |a1.name==a2.name => a1 = a2  
}

//An attribute object can be contained by only one class
fact attributeContainment {
all c1:Class, c2:Class | all a1:c1.attrs, a2:c2.attrs | a1==a2 => c1=c2
}

//There is exactly one ClassModel object
fact oneClassModel {
 one ClassModel
}

//All Classifier objects are contained in a ClassModel
fact classifierContainment {
all c:Classifier | c in ClassModel.classifier
}

//All Association objects are contained in a ClassModel
fact associationContainment {
all a:Association | a in ClassModel.association
}



//A Classifier must have a unique name in the class diagram
fact uniqueClassifierName {
all c1:Classifier, c2:Classifier | c1.name==c2.name => c1=c2
}



//An associations have the same name either they are the same association or they have different sources
fact uniqeNameAssocSrc {
all a1:Association, a2:Association | a1.name == a2.name => (a1 = a2 or a1.src != a2.src)
}


//Model Transformation UMLCD to RDBMS Pre-condition
fact atleastOnePrimaryAttribute {
    all c:Class| one a:c.attrs | a.is_primary==True
}


//Improved Model Transformation pre-conditions
fact no4CyclicClassAttribute{
	all a:Attribute | a.type in Class => all a1:a.type.attrs|a1.type in Class => all a2:a.type.attrs|a2.type in Class => all a3:a.type.attrs|a3.type in Class => all a4:a.type.attrs|a4.type in PrimitiveDataType
}

//A Class cannot have an association and an attribute of the same name 
fact noAttribAndAssocSameName{
	all c:Class, assoc:Association | all a : c.attrs | (assoc.src == c) => a.name != assoc.name
}


//No cycles between non-persistent classes



fact no1CycleNonPersistent
{
      all a: Association | (a.dest == a.src) => a.dest.is_persistent= True 
}



fact no2CycleNonPersistent
{
      all a1: Association, a2:Association | (a1.dest == a2.src and a2.dest==a1.src) => a1.src.is_persistent= True or a2.src.is_persistent=True  
}

/*
fact no3CycleNonPersistent
{
      all a1: Association, a2:Association, a3:Association | (a1.dest == a2.src and a2.dest==a3.src and a3.dest==a1.src) => a1.src.is_persistent= True or a2.src.is_persistent=True  or a3.src.is_persistent=True
}

fact no4CycleNonPersistent
{
      all a1: Association, a2:Association, a3:Association, a4:Association | (a1.dest == a2.src and a2.dest==a3.src and a3.dest == a4.src and a4.dest==a1.src ) => a1.src.is_persistent= True or a2.src.is_persistent=True  or a3.src.is_persistent=True or a4.src.is_persistent=True
}

*/
