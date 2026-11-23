import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactAdelesRationalPointsFiniteEventuallyZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDeterminantOpenImage
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IdeleSinglePlace

open GlobalTheory.EmbChart

theorem one_add_atPlace_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    (1 + atPlace v (x - 1)) * (1 + atPlace v (y - 1)) = 1 + atPlace v (x * y - 1) := by
  rw [add_mul, one_mul, atPlace_mul_right, map_add, map_one, evFin_atPlace, add_assoc, ← map_add]
  congr 2; ring

theorem one_add_atPlace_pow {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) (N : ℕ) :
    (1 + atPlace v (x - 1)) ^ N = 1 + atPlace v (x ^ N - 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, one_add_atPlace_mul, pow_succ]

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), ∃ (s : (AF F)ˣ) (ε : AF F),
    (∀ u : AF F, evFin F v u = 0 → u * (s : AF F) = u) ∧ Tendsto (fun N : ℕ => (s : AF F) ^ N) atTop (𝓝 ε) ∧
    ¬ IsUnit (algebraMap (AF F) (AE F E) ε) := by
  intro F E _ _ _ _ _ v
  obtain ⟨ϖ, h0, h1, hT⟩ : ∃ ϖ : Fv F v, ϖ ≠ 0 ∧ ϖ ≠ 0 ∧ Tendsto (fun N : ℕ => ϖ ^ N) atTop (𝓝 0) := by
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    obtain ⟨ϖ, hp, hl⟩ := NormedField.exists_norm_lt_one (v.adicCompletion F)
    exact ⟨ϖ, norm_pos_iff.1 hp, norm_pos_iff.1 hp, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hl⟩
  let s : (AF F)ˣ := ⟨1 + atPlace v (ϖ - 1), 1 + atPlace v (ϖ⁻¹ - 1),
    by rw [one_add_atPlace_mul, mul_inv_cancel₀ h0, sub_self, map_zero, add_zero],
    by rw [one_add_atPlace_mul, inv_mul_cancel₀ h0, sub_self, map_zero, add_zero]⟩
  refine ⟨s, 1 - atPlace v 1, fun u hu => ?_, ?_, ?_⟩
  · change u * (1 + atPlace v (ϖ - 1)) = u
    rw [mul_add, mul_one, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero, add_zero]
  · change Tendsto (fun N : ℕ => (1 + atPlace v (ϖ - 1)) ^ N) atTop _
    simp_rw [one_add_atPlace_pow]
    have hc : Continuous (fun x : Fv F v => (1 : AF F) + atPlace v (x - 1)) :=
      continuous_const.add (GlobalTheory.SkewLeviNear.continuous_atPlace.comp (continuous_id.sub continuous_const))
    have := (hc.tendsto 0).comp hT
    simpa [Function.comp_def, zero_sub, map_neg, sub_eq_add_neg] using this
  · intro hu
    have hinj : Function.Injective (algebraMap (AF F) (AE F E)) :=
      Algebra.TensorProduct.includeLeft_injective (S := AF F) (algebraMap F E).injective
    have hmul : (1 - atPlace v (1 : Fv F v)) * atPlace v 1 = 0 := by
      rw [sub_mul, one_mul, mul_comm, atPlace_mul_right, evFin_atPlace, one_mul, sub_self]
    have h2 : algebraMap (AF F) (AE F E) (atPlace v 1) = 0 := by
      have := congrArg (algebraMap (AF F) (AE F E)) hmul
      rw [map_mul, map_zero] at this
      exact (hu.mul_right_eq_zero).1 this
    have h3 : atPlace v (1 : Fv F v) = 0 := hinj (by rw [h2, map_zero])
    have h4 := congrArg (evFin F v) h3
    rw [evFin_atPlace, map_zero] at h4
    exact one_ne_zero h4

end GlobalTheory.IdeleSinglePlace

end
