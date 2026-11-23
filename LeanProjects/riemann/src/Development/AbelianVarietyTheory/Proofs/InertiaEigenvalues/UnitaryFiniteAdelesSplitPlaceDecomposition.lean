import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.SplitAdelic

open TensorProduct GlobalTheory.InertUmax GlobalTheory.SplitLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem exists_imag (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, IsCMField.complexConj L δ = -δ ∧ δ ≠ 0 := by
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  refine ⟨y - IsCMField.complexConj L y, ?_, sub_ne_zero.2 (Ne.symm hy)⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]; ring

theorem linIndep_one_imag (δ : L) (hδ : IsCMField.complexConj L δ = -δ) (hδ0 : δ ≠ 0) :
    LinearIndependent L⁺ ![(1 : L), δ] := by
  rw [LinearIndependent.pair_iff]
  intro a t h
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  have h2 := congrArg (IsCMField.complexConj L) h
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_zero] at h2
  have ht : algebraMap L⁺ L t * δ = 0 := by linear_combination (h - h2) / 2
  have ht' : algebraMap L⁺ L t = 0 := (mul_eq_zero.mp ht).resolve_right hδ0
  have hs : algebraMap L⁺ L a = 0 := by linear_combination (h + h2) / 2
  exact ⟨(algebraMap L⁺ L).injective (hs.trans (map_zero _).symm),
    (algebraMap L⁺ L).injective (ht'.trans (map_zero _).symm)⟩

theorem compAt_eq_zero_of_proj (s : SplitPlace L) (a : AL L) (h1 : s.proj a = 0)
    (h2 : s.proj (conjAL L a) = 0) : compAt L s.v a = 0 := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_imag L
  let b : Module.Basis (Fin 2) L⁺ L := basisOfLinearIndependentOfCardEqFinrank
    (linIndep_one_imag δ hδ hδ0)
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = δ := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_decomp b a
  rw [hb0, hb1] at hAB
  subst hAB
  rw [map_add, proj_tmul, proj_tmul, map_one, one_mul] at h1
  rw [map_add, conjAL_tmul, conjAL_tmul, map_one, hδ, map_add, proj_tmul, proj_tmul, map_one, one_mul,
    map_neg] at h2
  have hr : s.i δ ≠ 0 := (_root_.map_ne_zero _).2 hδ0
  have hA2 : 2 * A s.v = 0 := by linear_combination h1 + h2
  have hA : A s.v = 0 := (mul_eq_zero.mp hA2).resolve_left (two_ne s)
  have hB2 : 2 * (s.i δ * B s.v) = 0 := by linear_combination h1 - h2
  have hB : s.i δ * B s.v = 0 := (mul_eq_zero.mp hB2).resolve_left (two_ne s)
  have hB' : B s.v = 0 := (mul_eq_zero.mp hB).resolve_left hr
  rw [map_add, compAt_tmul, compAt_tmul, hA, hB', tmul_zero, tmul_zero, add_zero]

theorem loc_apply (s : SplitPlace L) {n : ℕ} (x : GAf L n) (i j : Fin n) :
    ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) i j =
      s.proj (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) := rfl

theorem conj_entry {n : ℕ} (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : (((x : GL (Fin n) (AL L))⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (x : GL (Fin n) (AL L)) :=
    Units.inv_eq_of_mul_eq_one_right hm
  rw [InvMemClass.coe_inv, h1]
  simp [conjT]

theorem compAt_entries_eq (s : SplitPlace L) {n : ℕ} (x g : GAf L n) (h : s.loc n x = s.loc n g)
    (i j : Fin n) :
    compAt L s.v (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) =
      compAt L s.v (((g : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) := by
  rw [← sub_eq_zero, ← map_sub]
  apply compAt_eq_zero_of_proj
  · rw [map_sub, sub_eq_zero, ← loc_apply, ← loc_apply, h]
  · have hinv : s.loc n x⁻¹ = s.loc n g⁻¹ := by rw [map_inv, map_inv, h]
    rw [map_sub, map_sub, sub_eq_zero, conj_entry, conj_entry, ← loc_apply, ← loc_apply, hinv]

theorem mat_ext {n : ℕ} (M N : Matrix (Fin n) (Fin n) (AL L))
    (h : ∀ w, M.map (compAt L w) = N.map (compAt L w)) : M = N := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt
  intro w
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun (h w) i) j

theorem ext_of_loc (s : SplitPlace L) {n : ℕ} (x y : GAf L n) (hx : TrivOutside {s.v} x)
    (hy : TrivOutside {s.v} y) (h : s.loc n x = s.loc n y) : x = y := by
  apply Subtype.ext; apply Units.ext
  apply mat_ext
  intro w
  obtain rfl | hw := eq_or_ne w s.v
  · ext i j
    exact compAt_entries_eq s x y h i j
  · rw [hx w hw, hy w hw]

theorem mul_coe {n : ℕ} (x y : GAf L n) :
    (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
        ((y : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    (∀ g : GAf L n, ∃ x y : GAf L n, TrivOutside {s.v} x ∧ TrivOutside {s.v}ᶜ y ∧ g = x * y) ∧
    (∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v}ᶜ y → Commute x y) ∧
    (∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      ∃! x : GAf L n, TrivOutside {s.v} x ∧ s.loc n x = A) := by
  intro L _ _ _ n s
  refine ⟨fun g => ?_, fun x y hx hy => ?_, fun A => ?_⟩
  · obtain ⟨x, hx, hxg⟩ := exists_trivOutside_loc_eq n s (s.loc n g)
    refine ⟨x, x⁻¹ * g, hx, ?_, (mul_inv_cancel_left x g).symm⟩
    intro w hw
    have hw' : w = s.v := by simpa using hw
    subst hw'
    rw [mul_coe, Matrix.map_mul]
    have hg : (((g : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L s.v) =
        (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L s.v) := by
      ext i j
      exact (compAt_entries_eq s x g hxg i j).symm
    rw [hg, ← Matrix.map_mul, ← mul_coe, inv_mul_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · show x * y = y * x
    apply Subtype.ext; apply Units.ext
    change (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (((y * x : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
    apply mat_ext
    intro w
    rw [mul_coe, mul_coe, Matrix.map_mul, Matrix.map_mul]
    obtain rfl | hw := eq_or_ne w s.v
    · rw [hy _ (by simp), mul_one, one_mul]
    · rw [hx w hw, mul_one, one_mul]
  · obtain ⟨x, hx, hxA⟩ := exists_trivOutside_loc_eq n s A
    exact ⟨x, ⟨hx, hxA⟩, fun y ⟨hy, hyA⟩ => ext_of_loc s y x hy hx (hyA.trans hxA.symm)⟩

end GlobalTheory.SplitAdelic
