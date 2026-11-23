import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfIsDual
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualKernel

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem evc_ker_iff {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over S} (x : T ⟶ A) :
    evc hP (fst T B ≫ x) (snd T B) = 0 ↔ evc hP (snd B T ≫ x) (fst B T) = 0 := by
  constructor
  · intro h
    have e := congrArg (CechPic.pull (lift (snd B T) (fst B T)).left) h
    rwa [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  · intro h
    have e := congrArg (CechPic.pull (lift (snd T B) (fst T B)).left) h
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e

theorem evc_ker_mul {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x y : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) (hy : evc hP (fst T B ≫ y) (snd T B) = 0) :
    evc hP (fst T B ≫ (x * y)) (snd T B) = 0 := by
  rw [MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, hy, add_zero]

theorem evc_ker_one {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) (T : Over S) :
    evc hP (fst T B ≫ (1 : T ⟶ A)) (snd T B) = 0 := by
  rw [MonObj.comp_one]
  exact hA.evc_one hP _

theorem evc_ker_inv {P : LB (A ⊗ B).left} (hP : P.IsLB) (hA : IsAdditive P) {T : Over S} (x : T ⟶ A)
    (hx : evc hP (fst T B ≫ x) (snd T B) = 0) : evc hP (fst T B ≫ x⁻¹) (snd T B) = 0 := by
  have e := evc_ker_one hP hA T
  rw [← mul_inv_cancel x, MonObj.comp_mul, (isAdditive_iff hP).1 hA, hx, zero_add] at e
  exact e

end GlobalTheory.DualKernel

namespace GlobalTheory.DualKernel

theorem exists_closed_subgroup_ker : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P →
    ∃ (N : Over (Sp K)) (_ : GrpObj N) (i : N ⟶ A), IsMonHom i ∧ IsClosedImmersion i.left ∧
      Triv (ev P (fst N B ≫ i) (snd N B)) ∧
      ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → ∃ z : T ⟶ N, z ≫ i = x := by
  intro K _ _ A B _ _ P hA hB hD
  have hP := hD.isLB
  have hs : (swap P).IsLB := pull_isLB hP _
  have ht : (LB.triv (B ⊗ A).left).IsLB := LB.isLB_triv _
  have h0 : ∀ (Y : Over (Sp K)) (b : Y ⟶ B) (a : Y ⟶ A), evc ht b a = 0 := fun _ _ _ ↦ map_zero _
  have hN : Fam B (swap P) := ⟨hs, isDual_isAdditive_swap _ A B P hB hD⟩
  have hN' : Fam B (LB.triv (B ⊗ A).left) :=
    ⟨ht, (isAdditive_iff ht).2 fun _ _ _ _ ↦ by simp only [h0, add_zero]⟩
  haveI := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨N, i, hi, hG⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp K) B A hB (swap P) _ hN hN'
  have key : ∀ (T : Over (Sp K)) (x : T ⟶ A),
      evc hP (fst T B ≫ x) (snd T B) = 0 ↔ ∃ z : T ⟶ N, z ≫ i = x := fun T x ↦ by
    rw [← hG, same_iff hs ht, h0, evc_swap hP hs, evc_ker_iff]
  have hK : ∀ (T : Over (Sp K)) (z : T ⟶ N), evc hP (fst T B ≫ z ≫ i) (snd T B) = 0 :=
    fun T z ↦ (key T _).2 ⟨z, rfl⟩
  haveI : Mono i.left := inferInstance
  haveI : Mono i := Over.mono_of_mono_left i
  have hl : ∀ {T : Over (Sp K)} (x : T ⟶ A), evc hP (fst T B ≫ x) (snd T B) = 0 →
      ∃ z : T ⟶ N, z ≫ i = x := fun x h ↦ (key _ x).1 h
  obtain ⟨o, ho⟩ := hl (η[A] : 𝟙_ (Over (Sp K)) ⟶ A) (by
    have e := evc_ker_one hP hD.additive (𝟙_ (Over (Sp K)))
    rwa [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp] at e)
  obtain ⟨m, hm⟩ := hl ((i ⊗ₘ i) ≫ μ[A]) (by
    have e := evc_ker_mul hP hD.additive (fst N N ≫ i) (snd N N ≫ i) (hK _ _) (hK _ _)
    rwa [Hom.mul_def, ← lift_map_assoc, lift_fst_snd, Category.id_comp] at e)
  obtain ⟨n, hn⟩ := hl (i ≫ GrpObj.inv) (by
    have e := evc_ker_inv hP hD.additive i (by simpa using hK N (𝟙 N))
    rwa [Hom.inv_def] at e)
  obtain ⟨g, hg⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  refine ⟨N, g, i, hg, hi, (triv_ev_iff hP _ _).2 (by simpa using hK N (𝟙 N)), fun T x hx ↦ ?_⟩
  exact (key T x).1 ((triv_ev_iff hP _ _).1 hx)

end GlobalTheory.DualKernel
