import Mathlib
import GroundTheory.TateCohomology.CoresRes
import GroundTheory.TateCohomology.TateZeroClass
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

section Invariants

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

def invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) : (res f A).ρ.invariants :=
  ⟨x, fun h => x.2 (f h)⟩

@[simp]
lemma coe_invariantsRes (f : H →* G) {A : Rep.{u} k G} (x : A.ρ.invariants) :
    (invariantsRes f x : A) = x := rfl

variable (S : Subgroup G) {A : Rep.{u} k G}

lemma ρ_mul_of_mem (y : (res S.subtype A).ρ.invariants) (g : G) {s : G} (hs : s ∈ S) :
    A.ρ (g * s) (y : A) = A.ρ g y := by
  rw [map_mul, Module.End.mul_apply]
  exact congrArg (A.ρ g) (y.2 ⟨s, hs⟩)

def cosetSMul (y : (res S.subtype A).ρ.invariants) (q : G ⧸ S) : A :=
  Quotient.liftOn' q (fun g => A.ρ g y) fun g g' h => by
    rw [QuotientGroup.leftRel_apply] at h
    rw [← ρ_mul_of_mem S y g h, mul_inv_cancel_left]

@[simp]
lemma cosetSMul_mk (y : (res S.subtype A).ρ.invariants) (g : G) :
    cosetSMul S y (g : G ⧸ S) = A.ρ g y := rfl

lemma cosetSMul_smul (y : (res S.subtype A).ρ.invariants) (h : G) (q : G ⧸ S) :
    cosetSMul S y (h • q) = A.ρ h (cosetSMul S y q) := by
  induction q using QuotientGroup.induction_on with | H g =>
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, cosetSMul_mk, cosetSMul_mk, map_mul,
    Module.End.mul_apply]

variable [Fintype G]

open scoped Classical in

noncomputable def transferSum (y : (res S.subtype A).ρ.invariants) : A :=
  ∑ q : G ⧸ S, cosetSMul S y q

lemma transferSum_mem_invariants (y : (res S.subtype A).ρ.invariants) :
    transferSum S y ∈ A.ρ.invariants := fun h => by
  classical
  simp only [transferSum, map_sum]
  rw [show (∑ q : G ⧸ S, A.ρ h (cosetSMul S y q)) = ∑ q : G ⧸ S, cosetSMul S y (h • q) from
    Finset.sum_congr rfl fun q _ => (cosetSMul_smul S y h q).symm]
  exact Fintype.sum_equiv (MulAction.toPerm h) _ _ fun _ => rfl

noncomputable def transferInv (y : (res S.subtype A).ρ.invariants) : A.ρ.invariants :=
  ⟨transferSum S y, transferSum_mem_invariants S y⟩

@[simp]
lemma coe_transferInv (y : (res S.subtype A).ρ.invariants) :
    (transferInv S y : A) = transferSum S y := rfl

end Invariants

section Shapiro

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

def coindConst (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (coind S.subtype B).ρ.invariants :=
  ⟨⟨fun _ => y, (Representation.mem_coindV _ _ _).2 fun s _ => (y.2 s).symm⟩,
    fun _ => rfl⟩

@[simp]
lemma coindConst_apply (B : Rep.{u} k S) (y : B.ρ.invariants) (g : G) :
    ((coindConst S B y : coind S.subtype B) : G → B) g = y := rfl

variable [Fintype G] [Fintype S]

lemma homologyMap_tateShapiroMap_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (HomologicalComplex.homologyMap (tateShapiroMap S B) 0).hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) :=
  homologyMap_tateZeroClass _ y _ (funext fun v => Subtype.ext (funext fun g =>
    shapiroCochains_hom_f_zero_const S B y y.2 v g))

lemma tateCoindIso_inv (B : Rep.{u} k S) (n : ℤ) :
    (tateCoindIso S B n).inv = HomologicalComplex.homologyMap (tateShapiroMap S B) n := by
  refine (cancel_mono (tateCoindIso S B n).hom).1 ?_
  exact (Iso.inv_hom_id _).trans (homologyMap_tateShapiroMap_comp_tateCoindIso_hom S B n).symm

theorem tateCoindIso_hom_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (tateCoindIso S B 0).hom.hom (tateZeroClass (coind S.subtype B) (coindConst S B y)) =
      tateZeroClass B y := by
  rw [← homologyMap_tateShapiroMap_tateZeroClass, ← tateCoindIso_inv]
  exact Iso.inv_hom_id_apply (tateCoindIso S B 0) _

theorem tateCoindIso_inv_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (tateCoindIso S B 0).inv.hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) := by
  rw [tateCoindIso_inv]
  exact homologyMap_tateShapiroMap_tateZeroClass S B y

end Shapiro

section ResCores

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

theorem tateRes_tateZeroClass (A : Rep.{u} k G) (x : A.ρ.invariants) :
    ((tateRes S 0).app A).hom (tateZeroClass A x) =
      tateZeroClass (res S.subtype A) (invariantsRes S.subtype x) := by
  rw [tateRes_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [tateCohomologyFunctor_map_tateZeroClass]
  have h : ((Rep.invariantsFunctor k G).map
      ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)).hom x =
      coindConst S (res S.subtype A) (invariantsRes S.subtype x) :=
    Subtype.ext (Subtype.ext (funext fun g => x.2 g))
  rw [h]
  exact tateCoindIso_hom_tateZeroClass S (res S.subtype A) (invariantsRes S.subtype x)

omit [Fintype S] in

lemma counit_indCoindIso_inv_coindConst [DecidableRel (QuotientGroup.rightRel S)]
    (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((Rep.indResAdjunction.{u} k S.subtype).counit.app A).hom
      ((indCoindIso (res S.subtype A)).inv.hom (coindConst S (res S.subtype A) y)) =
      transferSum S y := by
  classical
  change ((Rep.indResAdjunction k S.subtype).counit.app A).hom
      (coindToInd (res S.subtype A) (coindConst S (res S.subtype A) y)) = _
  rw [coindToInd_apply, map_sum, transferSum]
  refine (Finset.sum_congr (by convert rfl) fun x _ => ?_ : _ = ∑ x : Quotient (QuotientGroup.rightRel S),
    cosetSMul S y (QuotientGroup.quotientRightRelEquivQuotientLeftRel S x)).trans (Equiv.sum_comp _ _)
  induction x using Quotient.inductionOn with
  | h g =>
    rw [Quotient.liftOn_mk, indResAdjunction_counit_app_hom_mk]
    rfl

theorem tateCores_tateZeroClass (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((tateCores S 0).app A).hom (tateZeroClass (res S.subtype A) y) =
      tateZeroClass A (transferInv S y) := by
  classical
  rw [tateCores_app, tateIndIso_inv_eq, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, tateCoindIso_inv_tateZeroClass,
    tateCohomologyFunctor_map_tateZeroClass, tateCohomologyFunctor_map_tateZeroClass]
  congr 1
  exact Subtype.ext (counit_indCoindIso_inv_coindConst S A y)

end ResCores

end GroundTheory.GroupCoh
