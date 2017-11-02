module simpleUML_MM

open util/Boolean as Bool

abstract sig Classifier  
{ 
	name : lone Int
}

 sig Association  
{ 
	name : lone Int,
	src : one Class,
	dest : one Class
}

 sig Attribute  
{ 
	type : one Classifier,
	name : lone Int,
	is_primary : lone Bool
}

 sig Class extends Classifier 
{ 
	is_persistent : lone Bool,
	attrs : some Attribute,
	parent : lone Class
}

 sig PrimitiveDataType extends Classifier 
{
}

 sig ClassModel  
{ 
	classifier : set Classifier,
	association : set Association
}


fact Classifier_containers
{
	(all  o : Classifier |o in ClassModel.classifier)
}


fact Association_containers
{
	(all  o : Association |o in ClassModel.association)
}


fact Attribute_containers
{
	(all  o : Attribute |o in Class.attrs)
}


fact Class_attrs_composite
{
	all  o1 : Class, o2 : Class |all  p1 : o1.attrs, p2 : o2.attrs |p1 = p2 implies o1 = o2
}


fact ClassModel_classifier_composite
{
	all  o1 : ClassModel, o2 : ClassModel |all  p1 : o1.classifier, p2 : o2.classifier |p1 = p2 implies o1 = o2
}


fact ClassModel_association_composite
{
	all  o1 : ClassModel, o2 : ClassModel |all  p1 : o1.association, p2 : o2.association |p1 = p2 implies o1 = o2
}


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

pred Classifier_name_partition1

{
	some  o : Classifier |o.name = 0
}

pred Classifier_name_partition2

{
	some  o : Classifier |o.name = 1
}

pred Classifier_name_partition3

{
	some  o : Classifier |o.name >= 5
}

pred Association_name_partition1

{
	some  o : Association |o.name = 0
}

pred Association_name_partition2

{
	some  o : Association |o.name = 1
}

pred Association_name_partition3

{
	some  o : Association |o.name >= 5
}

pred Association_src_partition1

{
	some  o : Association |#o.src = 0
}

pred Association_src_partition2

{
	some  o : Association |#o.src = 1
}

pred Association_src_partition3

{
	some  o : Association |#o.src >= 5
}

pred Association_dest_partition1

{
	some  o : Association |#o.dest = 0
}

pred Association_dest_partition2

{
	some  o : Association |#o.dest = 1
}

pred Association_dest_partition3

{
	some  o : Association |#o.dest >= 5
}

pred Attribute_type_partition1

{
	some  o : Attribute |#o.type = 0
}

pred Attribute_type_partition2

{
	some  o : Attribute |#o.type = 1
}

pred Attribute_type_partition3

{
	some  o : Attribute |#o.type >= 5
}

pred Attribute_name_partition1

{
	some  o : Attribute |o.name = 0
}

pred Attribute_name_partition2

{
	some  o : Attribute |o.name = 1
}

pred Attribute_name_partition3

{
	some  o : Attribute |o.name >= 5
}

pred Attribute_is_primary_partition1

{
	some  o : Attribute |o.is_primary = True
}

pred Attribute_is_primary_partition2

{
	some  o : Attribute |o.is_primary = False
}

pred Class_is_persistent_partition1

{
	some  o : Class |o.is_persistent = True
}

pred Class_is_persistent_partition2

{
	some  o : Class |o.is_persistent = False
}

pred Class_attrs_partition1

{
	some  o : Class |#o.attrs = 0
}

pred Class_attrs_partition2

{
	some  o : Class |#o.attrs = 1
}

pred Class_attrs_partition3

{
	some  o : Class |#o.attrs >= 5
}

pred Class_parent_partition1

{
	some  o : Class |#o.parent = 0
}

pred Class_parent_partition2

{
	some  o : Class |#o.parent = 1
}

pred Class_parent_partition3

{
	some  o : Class |#o.parent >= 5
}

pred ClassModel_classifier_partition1

{
	some  o : ClassModel |#o.classifier = 0
}

pred ClassModel_classifier_partition2

{
	some  o : ClassModel |#o.classifier = 1
}

pred ClassModel_classifier_partition3

{
	some  o : ClassModel |#o.classifier >= 5
}

pred ClassModel_association_partition1

{
	some  o : ClassModel |#o.association = 0
}

pred ClassModel_association_partition2

{
	some  o : ClassModel |#o.association = 1
}

pred ClassModel_association_partition3

{
	some  o : ClassModel |#o.association >= 5
}

pred mfAllRanges_Classifier_name_partition1

{
	Classifier_name_partition1
}

pred mfAllRanges_Classifier_name_partition2

{
	Classifier_name_partition2
}

pred mfAllRanges_Classifier_name_partition3

{
	Classifier_name_partition3
}

pred mfAllRanges_Association_name_partition1

{
	Association_name_partition1
}

pred mfAllRanges_Association_name_partition2

{
	Association_name_partition2
}

pred mfAllRanges_Association_name_partition3

{
	Association_name_partition3
}

pred mfAllRanges_Association_src_partition1

{
	Association_src_partition1
}

pred mfAllRanges_Association_src_partition2

{
	Association_src_partition2
}

pred mfAllRanges_Association_src_partition3

{
	Association_src_partition3
}

pred mfAllRanges_Association_dest_partition1

{
	Association_dest_partition1
}

pred mfAllRanges_Association_dest_partition2

{
	Association_dest_partition2
}

pred mfAllRanges_Association_dest_partition3

{
	Association_dest_partition3
}

pred mfAllRanges_Attribute_type_partition1

{
	Attribute_type_partition1
}

pred mfAllRanges_Attribute_type_partition2

{
	Attribute_type_partition2
}

pred mfAllRanges_Attribute_type_partition3

{
	Attribute_type_partition3
}

pred mfAllRanges_Attribute_name_partition1

{
	Attribute_name_partition1
}

pred mfAllRanges_Attribute_name_partition2

{
	Attribute_name_partition2
}

pred mfAllRanges_Attribute_name_partition3

{
	Attribute_name_partition3
}

pred mfAllRanges_Attribute_is_primary_partition1

{
	Attribute_is_primary_partition1
}

pred mfAllRanges_Attribute_is_primary_partition2

{
	Attribute_is_primary_partition2
}

pred mfAllRanges_Class_is_persistent_partition1

{
	Class_is_persistent_partition1
}

pred mfAllRanges_Class_is_persistent_partition2

{
	Class_is_persistent_partition2
}

pred mfAllRanges_Class_attrs_partition1

{
	Class_attrs_partition1
}

pred mfAllRanges_Class_attrs_partition2

{
	Class_attrs_partition2
}

pred mfAllRanges_Class_attrs_partition3

{
	Class_attrs_partition3
}

pred mfAllRanges_Class_parent_partition1

{
	Class_parent_partition1
}

pred mfAllRanges_Class_parent_partition2

{
	Class_parent_partition2
}

pred mfAllRanges_Class_parent_partition3

{
	Class_parent_partition3
}

pred mfAllRanges_ClassModel_classifier_partition1

{
	ClassModel_classifier_partition1
}

pred mfAllRanges_ClassModel_classifier_partition2

{
	ClassModel_classifier_partition2
}

pred mfAllRanges_ClassModel_classifier_partition3

{
	ClassModel_classifier_partition3
}

pred mfAllRanges_ClassModel_association_partition1

{
	ClassModel_association_partition1
}

pred mfAllRanges_ClassModel_association_partition2

{
	ClassModel_association_partition2
}

pred mfAllRanges_ClassModel_association_partition3

{
	ClassModel_association_partition3
}

pred mfAllPartitions_Classifier_name_partition1_Classifier_name_partition2_Classifier_name_partition3

{
	Classifier_name_partition1 and Classifier_name_partition2 and Classifier_name_partition3 
}

pred mfAllPartitions_Association_name_partition1_Association_name_partition2_Association_name_partition3

{
	Association_name_partition1 and Association_name_partition2 and Association_name_partition3 
}

pred mfAllPartitions_Association_src_partition1_Association_src_partition2_Association_src_partition3

{
	Association_src_partition1 and Association_src_partition2 and Association_src_partition3 
}

pred mfAllPartitions_Association_dest_partition1_Association_dest_partition2_Association_dest_partition3

{
	Association_dest_partition1 and Association_dest_partition2 and Association_dest_partition3 
}

pred mfAllPartitions_Attribute_type_partition1_Attribute_type_partition2_Attribute_type_partition3

{
	Attribute_type_partition1 and Attribute_type_partition2 and Attribute_type_partition3 
}

pred mfAllPartitions_Attribute_name_partition1_Attribute_name_partition2_Attribute_name_partition3

{
	Attribute_name_partition1 and Attribute_name_partition2 and Attribute_name_partition3 
}

pred mfAllPartitions_Attribute_is_primary_partition1_Attribute_is_primary_partition2

{
	Attribute_is_primary_partition1 and Attribute_is_primary_partition2 
}

pred mfAllPartitions_Class_is_persistent_partition1_Class_is_persistent_partition2

{
	Class_is_persistent_partition1 and Class_is_persistent_partition2 
}

pred mfAllPartitions_Class_attrs_partition1_Class_attrs_partition2_Class_attrs_partition3

{
	Class_attrs_partition1 and Class_attrs_partition2 and Class_attrs_partition3 
}

pred mfAllPartitions_Class_parent_partition1_Class_parent_partition2_Class_parent_partition3

{
	Class_parent_partition1 and Class_parent_partition2 and Class_parent_partition3 
}

pred mfAllPartitions_ClassModel_classifier_partition1_ClassModel_classifier_partition2_ClassModel_classifier_partition3

{
	ClassModel_classifier_partition1 and ClassModel_classifier_partition2 and ClassModel_classifier_partition3 
}

pred mfAllPartitions_ClassModel_association_partition1_ClassModel_association_partition2_ClassModel_association_partition3

{
	ClassModel_association_partition1 and ClassModel_association_partition2 and ClassModel_association_partition3 
}

pred GenerateAndTestSimple

{

}

run GenerateAndTestSimple  for 20
