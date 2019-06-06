/*

Defines a fusion law and the necessary functions to use it.

version 2 (version 1 was a FusTab)

A fusion law is a set F together with a map *: F x F -> 2^F

There is also an evalutaion map eval: F -> eigs to some eigenvalues

*/
declare type FusLaw[FusLawElt];

declare attributes FusLaw:
  name,          // the name of the fusion table
  directory,     // a name to use as a directory to save under
  set,           // a SetIndx of elements
  evaluation,    // a map from set to eigenvalues
  eigenvalues,   // a SetIndx of eigenvalues
  table,         // table of values for the fusion law
  useful,        // a SetIndx of tuples of the useful fusion rules
  group,         // a GrpPerm which is the grading on the table
  grading;       // a map from the values to the group giving the grading

declare attributes FusLawElt:
  elt,           // an element
  parent,        // the parent
  eigenvalue;    // the eigenvalue
//
//
// =========== Properties of FusLaws ===========
//
//
/*

Pretty printing for Fusion tables!

*/
intrinsic Print(T::FusLaw)
  {
  Prints a fusion law.
  }
  if assigned T`name then
    printf "%o fusion table.\n\n", T`name;
  end if;

  obj := T`set;
  if not Type(Universe(T`set)) in { RngInt, FldRat} then
    function Name(x)
      return Position(obj, x);
    end function;
    relabel := true;
  else
    function Name(x)
      return x;
    end function;
    relabel := false;
  end if;

  L := [[ {@ Name(x) : x in S@} : S in r ] : r in T`table];

  top := [ " " cat Sprint(Name(x)) cat " " : x in obj ];
  width1st := Max([#t : t in top]);
  table := [ [Sprintf("%*o|", width1st, top[i])] cat [Substring(Sprint(L[i,j]), 3, #Sprint(L[i,j])-4) : j in [1..#L[i]]] : i in [1..#L]];
  widths := [ Max([#table[i,j] : i in [1..#table]] cat [j eq 1 select 0 else #top[j-1]]) : j in [1..#table+1]];
  top_table := [[ " "^(widths[1]-1) cat "|"] cat top] cat [[ "-"^widths[i] : i in [1..#widths] ]] cat table;
  for j in [1..#top_table] do
    for i in [1..#widths] do
      printf "%*o", widths[i], top_table[j,i];
    end for;
    printf "\n";
  end for;

  if relabel then
    print "\nWhere we use the labelling\n";
    printf Join([ Sprintf("%o :-> %o", Name(i), i) : i in obj], "\n");
  end if;

  if assigned T`evaluation then
    printf "\nEvaluation is %o", T`evaluation;
  end if;
end intrinsic;



intrinsic 'eq'(A::FusLaw, B::FusLaw) -> BoolElt
  {
  Checks whether the set and table are the same.
  }
  return A`set eq B`set and A`table eq B`table;
end intrinsic;

intrinsic IsIsomorphic(A::FusLaw, B::FusLaw) -> BoolElt, GrpPermElt
  {
  Checks whether the two fusion laws are isomorphic and if so returns an isomorphism from one set to the other.
  }


end intrinsic;

intrinsic AssignEvaluationMap(~T::FusLaw, f::Map: check:=true)
  {
  Assigns the evaluation map f to the fusion law.  check is an optional parameter whether to check if it already has a evaluation map.
  }
  if check then
    require not assigned T`evaluation: "The fusion law already has an assigned evaluation map.";
  end if;

  require T`set subset Domain(f): "The fusion law is not a subset of the domain of the given map.";

  T`evaluation := f;
  T`eigenvalues := T`set@f;
end intrinsic;

intrinsic AssignEvaluationMap(T::FusLaw, f::Map: check:=true) -> FusLaw
  {
  Assigns the evaluation map f to the fusion law.  check is an optional parameter whether to check if it already has a evaluation map.
  }
  Tnew := New(FusLaw);
  for attr in GetAttributes(FusLaw) do
    Tnew``attr := T``attr;
  end for;

  AssignEvaluationMap(~Tnew, f: check:=check);
  return Tnew;
end intrinsic;
//
//
// =========== Properties of FusLawElts ===========
//
//
intrinsic Parent(x::FusLawElt) -> FusLaw
  {
  Parent of x.
  }
  return x`parent;
end intrinsic;

intrinsic Print(x::FusLawElt)
  {
  Print x.
  }
  printf "%o", x`elt;
end intrinsic;

intrinsic 'eq'(x::FusLawElt, y::FusLawElt) -> BoolElt
  {
  Equality of elements.
  }
  require x`parent eq y`parent: "The two elements are not in the same fusion law.";
  return x`elt eq y`elt;
end intrinsic;

intrinsic 'in'(x::FusLawElt, T::FusLaw) -> BoolElt
  {
  Returns whether x is in T.
  }
  return x`parent eq T;
end intrinsic;

// maybe this should be a function?
intrinsic CreateElement(T::FusLaw, x::.) -> FusLawElt
  {
  Creates an element.
  }
  xx := New(FusLawElt);
  xx`parent := T;
  xx`elt := (T`set)!x;
  if assigned T`evaluation then
    xx`eigenvalue := xx`elt @ T`evaluation;
  end if;

  return xx;
end intrinsic;

intrinsic IsCoercible(T::FusLaw, x::.) -> BoolElt, .
  {
  Returns whether x is coercible into T and the result if so.
  }
  if Type(x) eq FusLawElt and x`parent eq T then
    return true, x;
  end if;

  so, xx := IsCoercible(T`set, x);
  if so then
    return true, CreateElement(T, xx);
  else
    return false, _;
  end if;
end intrinsic;

intrinsic Hash(x::FusLawElt) -> RngIntElt
  {
  Returns the hash value of x.
  }
  return Hash(x`elt);
end intrinsic;
//
//
// ============ OPERATIONS FOR ELEMENTS ==============
//
//
intrinsic '*'(x::FusLawElt, y::FusLawElt) -> SetIndx[FusLawElt]
  {
  Returns the product of x and y.
  }
  T := Parent(x);
  require T eq Parent(y): "x and y are not in the same fusion law.";

  return T`table[Position(T`set, x`elt), Position(T`set, y`elt)];
end intrinsic;
//
//
// ============ Changes ring ==============
//
//
/*

Changes the field for the fusion table.

*/
intrinsic ChangeField(T::FusLaw, F::Fld) -> FusLaw
  {
  If the fusion law has an evaluation map, changes its field of definition.
  }
  return ChangeRing(T, F);
end intrinsic;

intrinsic ChangeField(T::FusLaw, F::Fld, f::Map) -> FusLaw
  {
  If the fusion law has an evaluation map, changes its field of definition.

  Note that we need to be able to coerce any scalars into the new field.  For example, the rationals to a finite field is ok, but not the other way.
  }
  if not assigned T`evaluation then
    print "No evaluation map assigned.";
    return T;
  end if;

  im := Setseq(T`set)@(T`evaluation*f);
  return AssignEvaluationMap(T, map<T`set -> im | [<i, im[i]> : i in T`set]>: check := false);
end intrinsic;

intrinsic ChangeRing(T::FusLaw, R::Rng) -> FusLaw
  {
  If the fusion law has an evaluation map, changes its ring of definition.

  Note that we need to be able to coerce any scalars into the new field.  For example, the rationals to a finite field is ok, but not the other way.
  }
  if not assigned T`evaluation then
    print "No evaluation map assigned.";
    return T;
  end if;

  im := ChangeUniverse(Setseq(T`set)@T`evaluation, R);
  return AssignEvaluationMap(T, map<T`set -> im | [<i, im[i]> : i in T`set]>: check := false);
end intrinsic;
//
//
// ============ Functions on a FusTab ============
//
//
/*

A sub fusion table

*/
intrinsic SubConstructor(T::FusLaw, t::.) -> FusLaw
  {
  Return the sub fusion law table given by elements of t.
  }
  t := Flat(t);
  require forall{ i : i in t | IsCoercible(T, i)}: "The second argument are not all in the fusion law.";

  Tnew := New(FusLaw);
  Tnew`set := {@ (T!i)`elt : i in t @};
  Sort(~Tnew`set, func<x,y|Position(T`set, x) - Position(T`set, y)>);

  pos := [Position(T`set, i) : i in Tnew`set];
  Tnew`table := [[ T`table[i,j] meet Tnew`set : j in pos] : i in pos];

  if assigned T`evaluation then
    Tnew`eigenvalues := Tnew`set @ T`evaluation;
    Tnew`evaluation := map< Tnew`set -> Tnew`eigenvalues | [ <i, i@T`evaluation> : i in Tnew`set]>;
  end if;

  return Tnew;
end intrinsic;
/*

Calculates the grading for the fusion law.

*/
intrinsic FinestAdequateGrading(T::FusLaw) -> GrpPerm, Map
  {
  Calculates the finest adequate grading group G and the grading function gr:F -> G.
  }
  if assigned T`group then
    return T`group, T`grading;
  end if;
  // We form a group whose generators are the elements of the set and relations given by the table to find the grading.
  // Any elements which are in a set which is an entry in the fusion table must have the same grading
  set := T`set;
  entries := {@ S : S in Flat(T`table) | S ne {@@} @};
  Sort(~entries,func<x,y|#y-#x>);
  gens := [* e : e in entries *];
  for e in entries do
    gens := [* #(e meet g) ne 0 select e join g else g : g in gens *];
  end for;
  gens := {@ g : g in gens @};

  // We set up a function to give the generator number of an eigenvalue
  genno := AssociativeArray();
  for e in set do
    assert exists(i){g : g in gens | e in g };
    genno[e] := Position(gens, i);
  end for;

  F := FreeAbelianGroup(#gens);
  rels := [ F.genno[1] ];

  // We build some relations
  e1 := gens[genno[1]];
  for i in e1 do
    for j in set diff e1 do
      for prod in T`table[Position(set,i), Position(set,j)] do
        Append(~rels, F.genno[j] - F.genno[prod]);
      end for;
    end for;
  end for;
  for i in set diff e1 do
    for j in set diff e1 do
      for prod in T`table[Position(set,i), Position(set,j)] do
        Append(~rels, F.genno[i] + F.genno[j] - F.genno[prod]);
        Append(~rels, F.genno[j] + F.genno[i] - F.genno[prod]);
      end for;
    end for;
  end for;

  G, map := quo<F|rels>;
  assert Order(G) le #set;
  GG, iso := PermutationGroup(G);
  T`group := GG;
  T`grading := map< set -> GG | i:-> (F.genno[i] @map)@@iso>;
  return T`group, T`grading;
end intrinsic;
/*

Calculates the useful fusion rules.

*/
intrinsic UsefulFusionRules(T::FusLaw) -> SetIndx
  {
  Returns those fusion rules for a Z_2-graded table which are useful.
  }
  if assigned T`useful then
    return T`useful;
  end if;
  set := T`set;
  G, grad := FinestAdequateGrading(T);
  require Order(G) eq 2: "The group is %o-graded.", G;
  pos := {@ i : i in set | i @ grad eq G!1 @};
  subsets := {@ S : S in Subsets(Set(pos)) | S ne {} @};
  Sort(~subsets, func< x,y | #y-#x>);

  FT := [ [] : i in [1..#subsets]];
  for i in [1..#subsets] do
    for j in [1..i] do
      FT[i,j] := &join { T`table[Position(set,k), Position(set,l)] : k in subsets[i], l in subsets[j] };
      FT[j,i] := FT[i,j];
    end for;
  end for;

  T`useful := {@ @};
  for i in [1..#subsets] do
    row := Set(FT[i]);
    for S in row do
      pos := Position(FT[i], S);
      assert exists(j){ j : j in [1..i] | FT[j,pos] eq FT[i,pos]};
      if j ne 1 or pos ne 1 then
        if i le pos then
          Include(~T`useful, < subsets[pos], subsets[j], Set(FT[j,pos])>);
        else
          Include(~T`useful, < subsets[j], subsets[pos], Set(FT[j,pos])>);
        end if;
      end if;
    end for;
  end for;

  return T`useful;
end intrinsic;
//
//
// ============ Some Examples ============
//
//
/*

Returns the Jordan type fusion law.

*/
intrinsic JordanFusionLaw(eta) -> FusLaw
  {
  Returns the Jordan type fusion law.
  }
  require eta notin {1,0}: "The parameter may not be 0, or 1.";
  T := New(FusLaw);
  T`name := "Jordan";
  T`directory := Join(Split(Sprintf("Jordan_%o", eta), "/"), ",");
  T`set := {@ 1, 2, 3 @};
  T`table := [[ {@1@}, {@ @}, {@3@}], [ {@@}, {@ 2 @}, {@3@}], [ {@3@}, {@3 @}, {@1,2@}]];
  evals := [1, 0, eta];
  T`eigenvalues := IndexedSet(evals);
  T`evaluation := map< T`set -> T`eigenvalues | [ <i, evals[i]> : i in T`set]>;
  _ := UsefulFusionRules(T);

  return T;
end intrinsic;
/*

Returns the Monster fusion law.

*/
intrinsic MonsterFusionLaw() -> FusLaw
  {
  Returns the fusion table for the Monster.
  }
  T := IsingTypeFusionLaw(1/4, 1/32);
  T`name := "Monster";
  T`directory := "Monster_1,4_1,32";
/*
  T := New(FusLaw);
  T`name := "Monster";
  T`directory := "Monster_1,4_1,32";
  T`set := {@ 1, 2, 3, 4 @};
  T`table := [[ {@1@}, {@ @}, {@3@}, {@4@}], [ {@@}, {@ 2 @}, {@3@}, {@4@}], [ {@3@}, {@3 @}, {@1,2@}, {@4@}], [ {@4@}, {@4@}, {@4@}, {@1,2,3@}]];
  evals := [1, 0, eta];
  T`eigenvalues := {@ 1, 0, 1/4, 1/32 @};
  T`evaluation := map< T`set -> T`eigenvalues | [ <i, evals[i]> : i in T`set]>;
  T`eigenvalues := IndexedSet(evals);
  _ := UsefulFusionRules(T);
*/
  return T;
end intrinsic;
/*

Returns the Ising type law.

*/
intrinsic IsingTypeFusionLaw(alpha::FldRatElt, beta::FldRatElt) -> FusLaw
  {
  Returns the fusion table of Ising type alpha, beta.
  }
  require #({alpha, beta} meet {1,0}) eq 0 : "The parameters may not be 0, or 1.";
  T := New(FusLaw);
  T`name := "Ising";
  T`directory := Join(Split(Sprintf("Ising_%o_%o", alpha, beta), "/"), ",");
  T`set := {@ 1, 2, 3, 4 @};
  T`table := [[ {@1@}, {@ @}, {@3@}, {@4@}], [ {@@}, {@ 2 @}, {@3@}, {@4@}], [ {@3@}, {@3 @}, {@1,2@}, {@4@}], [ {@4@}, {@4@}, {@4@}, {@1,2,3@}]];
  evals := [1, 0, alpha, beta];
  T`eigenvalues := IndexedSet(evals);
  T`evaluation := map< T`set -> T`eigenvalues | [ <i, evals[i]> : i in T`set]>;
  _ := UsefulFusionRules(T);

  return T;
end intrinsic;
/*

Returns the extended Jordan-type law.

*/
intrinsic HyperJordanTypeFusionLaw(eta::FldRatElt) -> FusLaw
  {
  Returns the fusion table of extended Jordan-type eta.
  }
  return IsingTypeFusionLaw(2*eta, eta);
end intrinsic;
/*

Creates the representation fusion law

*/
intrinsic RepresentationFusionLaw(G::Grp) -> FusLaw
  {
  Returns the representation fusion law for the group G.
  }
  return RepresentationFusionLaw(CharacterTable(G));
end intrinsic;

intrinsic RepresentationFusionLaw(CT::SeqEnum[AlgChtrElt]) -> FusLaw
  {
  Returns the representation fusion law for the group G.
  }
  T := New(FusLaw);
  T`set := IndexedSet(CT);
  T`table := [[ {@ C : C in CT | InnerProduct(XY, C) ne 0 where XY := CT[i]*CT[j] @} : j in [1..i]] : i in [1..#CT]];
  // Now symmetrise
  for i in [1..#CT] do
    for j in [i+1..#CT] do
      T`table[i,j] := T`table[j,i];
    end for;
  end for;

  if assigned Universe(CT)`Group then
    T`name := Sprintf("Representation fusion law for %o", GroupName(Group(Universe(CT))));
    T`directory := Sprintf("Rep_fusion_law_%o", MyGroupName(Group(Universe(CT))));
  end if;
  return T;
end intrinsic;

intrinsic RepresentationFusionLaw(D::LieRepDec) -> FusLaw
  {
  Returns the representation fusion law for the irreducible representations occuring in D
  }
  T := New(FusLaw);
  T`set := Weights(D);
  T`table := [[ {@ C : C in T`set | Multiplicity(T,C) ne 0 where T := TensorProduct(RootDatum(D),T`set[i],T`set[j])@} : j in [1..i]] : i in [1..#D]];
  // Now symmetrise
  for i in [1..#D] do
    for j in [i+1..#D] do
      T`table[i,j] := T`table[j,i];
    end for;
  end for;
  T`name := Sprintf("Lie Representation fusion law for %o", RootDatum(D));
  return T;
end intrinsic;

//-----------------------------------------------------------
//
// Code to load and save a fusion law in the json format
//
//-----------------------------------------------------------
/*

Code to serialise a fusion law

*/
intrinsic FusTabToList(T::FusLaw) -> List
  {
  Transform a fusion table to a List prior to serialising as a JSON.
  }
  L := [* *];
  Append(~L, <"class", "Fusion law">);

  if assigned T`name then
    Append(~L, <"name", T`name>);
    Append(~L, <"directory", T`directory>);
  end if;

  set := Setseq(T`set);
  Append(~L, <"set", set>);
  Append(~L, <"table", T`table>);

  if assigned T`evaluation then
    Append(~L, <"evaluation", set@T`evaluation>);
  end if;

  return L;
end intrinsic;
/*

Code to load a fusion table.

*/
intrinsic FusionLaw(A::Assoc) -> FusLaw
  {
  Create a fusion table T from an associative array.  We assume that the associative array represents T stored in json format.
  }
  keys := Keys(A);
  require "class" in keys and A["class"] eq "Fusion law": "The file given does not have a valid fusion law.";
  T := New(FusLaw);
  T`set := IndexedSet(Numbers(A["set"]));
  T`eigenvalues := IndexedSet(Numbers(A["eigenvalues"]));
  T`table := [ [ IndexedSet(Numbers(S)) : S in row ] : row in A["table"]];

  if "name" in keys then
    T`name := A["name"];
    T`directory := A["directory"];
  end if;

  if "evaluation" in keys then
    evals := Numbers(A["evaluation"]);
    T`evaluation := map< T`set -> T`eigenvalues | [ <i, evals[i]> : i in T`set]>;
    T`eigenvalues := IndexedSet(evals);
  end if;

  _ := UsefulFusionRules(T);

  return T;
end intrinsic;
