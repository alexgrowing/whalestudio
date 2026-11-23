import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarizedAbelianVarieties

noncomputable section

def IsTrivialLB {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : LB.Gen L, t.IsGen

def powLB {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X where
  ι := L.ι
  U := L.U
  g := fun i j => L.g i j ^ n

def nonvanishingLocus {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) : X.Opens :=
  ⨆ i, X.basicOpen (s.f i)

def IsAmpleLB {X : Scheme.{0}} (L : LB X) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s : LB.Sec (powLB L n),
    x ∈ nonvanishingLocus s ∧ IsAffineOpen (nonvanishingLocus s)

def IsRelAmpleLB {X S : Scheme.{0}} (f : X ⟶ S) (L : LB X) : Prop :=
  QuasiCompact f ∧ ∀ V : S.Opens, IsAffineOpen V → IsAmpleLB (L.pull (f ⁻¹ᵁ V).ι)

section Conditions

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)

def IsRigidified : Prop := IsTrivialLB (L.pull (eSec A))

def IsSymmetric : Prop := ∃ t : LB.Iso (L.pull (GrpObj.inv (X := A)).left) L, t.IsGen

def IsRelAmple : Prop := IsRelAmpleLB A.hom L

def MemK {T : Over S} (x : T ⟶ A) : Prop := IsTrivialLB ((abelian₂ A L).pull (x ▷ A).left)

def KTrivial : Prop := ∀ (T : Over S) (x : T ⟶ A), MemK A L x → x = pzero A T

end Conditions

structure PolAV (S : Scheme.{0}) (g : ℕ) where

  A : Over S
  [grp : GrpObj A]
  isAbelian : IsAbelianScheme A
  relDim : SmoothOfRelativeDimension g A.hom

  L : LB A.left
  isLB : L.IsLB
  rigidified : IsRigidified A L
  symmetric : IsSymmetric A L
  relAmple : IsRelAmple A L
  kTrivial : KTrivial A L

attribute [instance] PolAV.grp

def trivialLB (X : Scheme.{0}) : LB X where
  ι := PUnit
  U := fun _ => ⊤
  g := fun _ _ => 1

lemma trivialLB_isLB (X : Scheme.{0}) : (trivialLB X).IsLB where
  cover := by simp [trivialLB]
  g_self := fun _ => map_one _
  cocycle := fun _ _ _ => by
    change res _ 1 * res _ 1 = res _ 1
    rw [map_one, map_one, map_one, one_mul]

lemma isTrivialLB_of_g {X : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) : IsTrivialLB L :=
  ⟨⟨fun _ => 1⟩, fun i j => by simp [h]⟩

lemma linComb_g {X Y : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j) : (L.LinComb φ ε).g i j = 1 := by
  refine Finset.prod_eq_one fun k _ => ?_
  rw [h, map_one]
  erw [map_one, one_zpow]
  rfl

example {S : Scheme.{0}} (A : Over S) [GrpObj A] (h : KTrivial A (trivialLB A.left)) :
    𝟙 A = pzero A A :=
  h A (𝟙 A) (isTrivialLB_of_g _ (linComb_g _ (linComb_g _ (fun _ _ => rfl) _ _) _ _))

lemma isAmpleLB_of_isAffine {X : Scheme.{0}} [IsAffine X] (L : LB X) (h : ∀ i j, L.g i j = 1)
    (hc : ⨆ i, L.U i = ⊤) : IsAmpleLB L := by
  refine ⟨inferInstance, fun x => ⟨1, one_pos, ⟨fun _ => 1, fun i j => ?_⟩, ?_⟩⟩
  · have : (powLB L 1).g i j = 1 := (pow_one _).trans (h i j)
    rw [this]
    simp
  have : ∀ s : LB.Sec (powLB L 1), (∀ i, s.f i = 1) → nonvanishingLocus s = ⊤ := by
    intro s hs
    rw [← hc]
    unfold nonvanishingLocus
    refine iSup_congr fun i => ?_
    rw [hs i]
    exact X.basicOpen_one
  rw [this _ (fun _ => rfl)]
  exact ⟨trivial, isAffineOpen_top X⟩

lemma geometricallyConnected_id (S : Scheme.{0}) : GeometricallyConnected (𝟙 S) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [(pullback.snd (𝟙 S) x).homeomorph.connectedSpace_iff]
  infer_instance

def PolAV.zero (S : Scheme.{0}) : PolAV S 0 where
  A := 𝟙_ (Over S)
  isAbelian := ⟨inferInstance, (inferInstance : Smooth (𝟙 S)), (inferInstance : IsProper (𝟙 S)),
    geometricallyConnected_id S⟩
  relDim := (inferInstance : SmoothOfRelativeDimension 0 (𝟙 S))
  L := trivialLB _
  isLB := trivialLB_isLB _
  rigidified := isTrivialLB_of_g _ (linComb_g _ (fun _ _ => rfl) _ _)
  symmetric := isTrivialLB_of_g _ fun i j => by
    simp only [LB.div, linComb_g (trivialLB _) (fun _ _ => rfl)]
    erw [map_one, map_one, inv_one, one_mul]
    rfl
  relAmple := ⟨(inferInstance : QuasiCompact (𝟙 S)), fun V hV => by
    haveI : IsAffine ((𝟙_ (Over S)).hom ⁻¹ᵁ V).toScheme := hV
    refine isAmpleLB_of_isAffine _ (linComb_g _ (fun _ _ => rfl) _ _) ?_
    refine top_le_iff.1 (le_iSup_of_le (fun _ => PUnit.unit) ?_)
    intro y _
    exact Set.mem_iInter.2 fun _ => trivial⟩
  kTrivial := fun _ _ _ => toUnit_unique _ _

end

end GlobalTheory.IndefiniteRowSideFullHecke.PolarizedAbelianVarieties
