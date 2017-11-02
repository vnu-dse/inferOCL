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

pred Classifier_name_partition1_value

{
	some  o : Classifier |all  p : o.name |p = 0
}

pred Classifier_name_partition2_value

{
	some  o : Classifier |all  p : o.name |p = 1
}

pred Classifier_name_partition3_value

{
	some  o : Classifier |all  p : o.name |p >= 5
}

pred Classifier_name_partition1_multiplicity

{
	some  o : Classifier |#o.name = 0
}

pred Classifier_name_partition2_multiplicity

{
	some  o : Classifier |#o.name = 1
}

pred Association_name_partition1_value

{
	some  o : Association |all  p : o.name |p = 0
}

pred Association_name_partition2_value

{
	some  o : Association |all  p : o.name |p = 1
}

pred Association_name_partition3_value

{
	some  o : Association |all  p : o.name |p >= 5
}

pred Association_name_partition1_multiplicity

{
	some  o : Association |#o.name = 0
}

pred Association_name_partition2_multiplicity

{
	some  o : Association |#o.name = 1
}

pred Association_src_partition1_multiplicity

{
	some  o : Association |#o.src = 0
}

pred Association_src_partition2_multiplicity

{
	some  o : Association |#o.src = 1
}

pred Association_dest_partition1_multiplicity

{
	some  o : Association |#o.dest = 0
}

pred Association_dest_partition2_multiplicity

{
	some  o : Association |#o.dest = 1
}

pred Attribute_type_partition1_multiplicity

{
	some  o : Attribute |#o.type = 0
}

pred Attribute_type_partition2_multiplicity

{
	some  o : Attribute |#o.type = 1
}

pred Attribute_name_partition1_value

{
	some  o : Attribute |all  p : o.name |p = 0
}

pred Attribute_name_partition2_value

{
	some  o : Attribute |all  p : o.name |p = 1
}

pred Attribute_name_partition3_value

{
	some  o : Attribute |all  p : o.name |p >= 5
}

pred Attribute_name_partition1_multiplicity

{
	some  o : Attribute |#o.name = 0
}

pred Attribute_name_partition2_multiplicity

{
	some  o : Attribute |#o.name = 1
}

pred Attribute_is_primary_partition1_value

{
	some  o : Attribute |all  p : o.is_primary |p = True
}

pred Attribute_is_primary_partition2_value

{
	some  o : Attribute |all  p : o.is_primary |p = False
}

pred Attribute_is_primary_partition1_multiplicity

{
	some  o : Attribute |#o.is_primary = 0
}

pred Attribute_is_primary_partition2_multiplicity

{
	some  o : Attribute |#o.is_primary = 1
}

pred Class_is_persistent_partition1_value

{
	some  o : Class |all  p : o.is_persistent |p = True
}

pred Class_is_persistent_partition2_value

{
	some  o : Class |all  p : o.is_persistent |p = False
}

pred Class_is_persistent_partition1_multiplicity

{
	some  o : Class |#o.is_persistent = 0
}

pred Class_is_persistent_partition2_multiplicity

{
	some  o : Class |#o.is_persistent = 1
}

pred Class_attrs_partition1_multiplicity

{
	some  o : Class |#o.attrs = 0
}

pred Class_attrs_partition3_multiplicity

{
	some  o : Class |#o.attrs >= 5
}

pred Class_parent_partition1_multiplicity

{
	some  o : Class |#o.parent = 0
}

pred Class_parent_partition2_multiplicity

{
	some  o : Class |#o.parent = 1
}

pred ClassModel_classifier_partition1_multiplicity

{
	some  o : ClassModel |#o.classifier = 0
}

pred ClassModel_classifier_partition3_multiplicity

{
	some  o : ClassModel |#o.classifier >= 5
}

pred ClassModel_association_partition1_multiplicity

{
	some  o : ClassModel |#o.association = 0
}

pred ClassModel_association_partition3_multiplicity

{
	some  o : ClassModel |#o.association >= 5
}

pred mfAllRanges_Classifier_name_partition1_value

{
	Classifier_name_partition1_value
}

pred mfAllRanges_Classifier_name_partition2_value

{
	Classifier_name_partition2_value
}

pred mfAllRanges_Classifier_name_partition3_value

{
	Classifier_name_partition3_value
}

pred mfAllRanges_Classifier_name_partition1_multiplicity

{
	Classifier_name_partition1_multiplicity
}

pred mfAllRanges_Classifier_name_partition2_multiplicity

{
	Classifier_name_partition2_multiplicity
}

pred mfAllRanges_Association_name_partition1_value

{
	Association_name_partition1_value
}

pred mfAllRanges_Association_name_partition2_value

{
	Association_name_partition2_value
}

pred mfAllRanges_Association_name_partition3_value

{
	Association_name_partition3_value
}

pred mfAllRanges_Association_name_partition1_multiplicity

{
	Association_name_partition1_multiplicity
}

pred mfAllRanges_Association_name_partition2_multiplicity

{
	Association_name_partition2_multiplicity
}

pred mfAllRanges_Association_src_partition1_multiplicity

{
	Association_src_partition1_multiplicity
}

pred mfAllRanges_Association_src_partition2_multiplicity

{
	Association_src_partition2_multiplicity
}

pred mfAllRanges_Association_dest_partition1_multiplicity

{
	Association_dest_partition1_multiplicity
}

pred mfAllRanges_Association_dest_partition2_multiplicity

{
	Association_dest_partition2_multiplicity
}

pred mfAllRanges_Attribute_type_partition1_multiplicity

{
	Attribute_type_partition1_multiplicity
}

pred mfAllRanges_Attribute_type_partition2_multiplicity

{
	Attribute_type_partition2_multiplicity
}

pred mfAllRanges_Attribute_name_partition1_value

{
	Attribute_name_partition1_value
}

pred mfAllRanges_Attribute_name_partition2_value

{
	Attribute_name_partition2_value
}

pred mfAllRanges_Attribute_name_partition3_value

{
	Attribute_name_partition3_value
}

pred mfAllRanges_Attribute_name_partition1_multiplicity

{
	Attribute_name_partition1_multiplicity
}

pred mfAllRanges_Attribute_name_partition2_multiplicity

{
	Attribute_name_partition2_multiplicity
}

pred mfAllRanges_Attribute_is_primary_partition1_value

{
	Attribute_is_primary_partition1_value
}

pred mfAllRanges_Attribute_is_primary_partition2_value

{
	Attribute_is_primary_partition2_value
}

pred mfAllRanges_Attribute_is_primary_partition1_multiplicity

{
	Attribute_is_primary_partition1_multiplicity
}

pred mfAllRanges_Attribute_is_primary_partition2_multiplicity

{
	Attribute_is_primary_partition2_multiplicity
}

pred mfAllRanges_Class_is_persistent_partition1_value

{
	Class_is_persistent_partition1_value
}

pred mfAllRanges_Class_is_persistent_partition2_value

{
	Class_is_persistent_partition2_value
}

pred mfAllRanges_Class_is_persistent_partition1_multiplicity

{
	Class_is_persistent_partition1_multiplicity
}

pred mfAllRanges_Class_is_persistent_partition2_multiplicity

{
	Class_is_persistent_partition2_multiplicity
}

pred mfAllRanges_Class_attrs_partition1_multiplicity

{
	Class_attrs_partition1_multiplicity
}

pred mfAllRanges_Class_attrs_partition3_multiplicity

{
	Class_attrs_partition3_multiplicity
}

pred mfAllRanges_Class_parent_partition1_multiplicity

{
	Class_parent_partition1_multiplicity
}

pred mfAllRanges_Class_parent_partition2_multiplicity

{
	Class_parent_partition2_multiplicity
}

pred mfAllRanges_ClassModel_classifier_partition1_multiplicity

{
	ClassModel_classifier_partition1_multiplicity
}

pred mfAllRanges_ClassModel_classifier_partition3_multiplicity

{
	ClassModel_classifier_partition3_multiplicity
}

pred mfAllRanges_ClassModel_association_partition1_multiplicity

{
	ClassModel_association_partition1_multiplicity
}

pred mfAllRanges_ClassModel_association_partition3_multiplicity

{
	ClassModel_association_partition3_multiplicity
}

pred mfAllPartitions_Classifier_name_partition1_value_Classifier_name_partition2_value_Classifier_name_partition3_value_Classifier_name_partition1_multiplicity_Classifier_name_partition2_multiplicity

{
	Classifier_name_partition1_value and Classifier_name_partition2_value and Classifier_name_partition3_value and Classifier_name_partition1_multiplicity and Classifier_name_partition2_multiplicity 
}

pred mfAllPartitions_Association_name_partition1_value_Association_name_partition2_value_Association_name_partition3_value_Association_name_partition1_multiplicity_Association_name_partition2_multiplicity

{
	Association_name_partition1_value and Association_name_partition2_value and Association_name_partition3_value and Association_name_partition1_multiplicity and Association_name_partition2_multiplicity 
}

pred mfAllPartitions_Association_src_partition1_multiplicity_Association_src_partition2_multiplicity

{
	Association_src_partition1_multiplicity and Association_src_partition2_multiplicity 
}

pred mfAllPartitions_Association_dest_partition1_multiplicity_Association_dest_partition2_multiplicity

{
	Association_dest_partition1_multiplicity and Association_dest_partition2_multiplicity 
}

pred mfAllPartitions_Attribute_type_partition1_multiplicity_Attribute_type_partition2_multiplicity

{
	Attribute_type_partition1_multiplicity and Attribute_type_partition2_multiplicity 
}

pred mfAllPartitions_Attribute_name_partition1_value_Attribute_name_partition2_value_Attribute_name_partition3_value_Attribute_name_partition1_multiplicity_Attribute_name_partition2_multiplicity

{
	Attribute_name_partition1_value and Attribute_name_partition2_value and Attribute_name_partition3_value and Attribute_name_partition1_multiplicity and Attribute_name_partition2_multiplicity 
}

pred mfAllPartitions_Attribute_is_primary_partition1_value_Attribute_is_primary_partition2_value_Attribute_is_primary_partition1_multiplicity_Attribute_is_primary_partition2_multiplicity

{
	Attribute_is_primary_partition1_value and Attribute_is_primary_partition2_value and Attribute_is_primary_partition1_multiplicity and Attribute_is_primary_partition2_multiplicity 
}

pred mfAllPartitions_Class_is_persistent_partition1_value_Class_is_persistent_partition2_value_Class_is_persistent_partition1_multiplicity_Class_is_persistent_partition2_multiplicity

{
	Class_is_persistent_partition1_value and Class_is_persistent_partition2_value and Class_is_persistent_partition1_multiplicity and Class_is_persistent_partition2_multiplicity 
}

pred mfAllPartitions_Class_attrs_partition1_multiplicity_Class_attrs_partition3_multiplicity

{
	Class_attrs_partition1_multiplicity and Class_attrs_partition3_multiplicity 
}

pred mfAllPartitions_Class_parent_partition1_multiplicity_Class_parent_partition2_multiplicity

{
	Class_parent_partition1_multiplicity and Class_parent_partition2_multiplicity 
}

pred mfAllPartitions_ClassModel_classifier_partition1_multiplicity_ClassModel_classifier_partition3_multiplicity

{
	ClassModel_classifier_partition1_multiplicity and ClassModel_classifier_partition3_multiplicity 
}

pred mfAllPartitions_ClassModel_association_partition1_multiplicity_ClassModel_association_partition3_multiplicity

{
	ClassModel_association_partition1_multiplicity and ClassModel_association_partition3_multiplicity 
}

pred GenerateAndTestSimple

{

}

run mfAllPartitions_Class_parent_partition1_multiplicity_Class_parent_partition2_multiplicity  for 20
