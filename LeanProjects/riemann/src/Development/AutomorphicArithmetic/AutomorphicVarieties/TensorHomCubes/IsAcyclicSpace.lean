import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

noncomputable section

open CategoryTheory unitInterval
open scoped Topology

namespace UpperTheory.V.KL

abbrev ZZ : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ

abbrev singC (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ := (TopCat.toSSet.obj X).chainComplex ZZ

abbrev singH (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ := (TopCat.toSSet.obj X).homology ZZ n

abbrev singHMap {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) : singH X n ⟶ singH Y n :=
  SSet.homologyMap (TopCat.toSSet.map f) ZZ n

theorem singH_eq (X : TopCat.{0}) (n : ℕ) :
    singH X n = ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj ZZ).obj X := rfl

def IsAcyclicSpace (F : TopCat.{0}) : Prop :=
  PathConnectedSpace F ∧ ∀ n : ℕ, Limits.IsZero (singH F (n + 1))

def hoFib {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) : TopCat.{0} :=
  TopCat.of {p : X × C(I, Y) // p.2 0 = f p.1 ∧ p.2 1 = y}

structure IsConnCW (X : TopCat.{0}) : Prop where
  t2 : T2Space X
  cw : Nonempty (Topology.CWComplex (Set.univ : Set X))
  conn : PathConnectedSpace X

def BG (G : Type) [Group G] : TopCat.{0} := SSet.toTop.obj (nerve (SingleObj G))

structure PlusOf (B : TopCat.{0}) where

  X : TopCat.{0}
  connCW : IsConnCW X

  q : B ⟶ X

  b : B
  acyclic : IsAcyclicSpace (hoFib q (q b))
  ker_eq : (FundamentalGroup.map q.hom b).ker = commutator (FundamentalGroup B b)

abbrev Plus (R : Type) [CommRing R] : Type 1 := PlusOf (BG (GLinf R))

abbrev PlusOf.pt {B : TopCat.{0}} (M : PlusOf B) : M.X := M.q M.b

abbrev PlusOf.K {B : TopCat.{0}} (M : PlusOf B) (n : ℕ) : Type := HomotopyGroup.Pi n M.X M.pt

example (R : Type) [CommRing R] (M : Plus R) (n : ℕ) : Group (M.K (n + 1)) := inferInstance
example (R : Type) [CommRing R] (M : Plus R) (n : ℕ) : AddCommGroup (Additive (M.K (2 * n + 2))) := inferInstance

end UpperTheory.V.KL

end
