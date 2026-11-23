import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRelationModelsMatrixSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEigenRelationSecondFormStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ExpandSummX

open scoped Classical

theorem summable_of_denom_decay' (E : Type) [Field E] [NumberField E] (n : ℕ) :
    ∃ K : ℕ, ∀ (N : ℕ) (h : (Fin n → E) → ℂ), 1 ≤ N → (∀ ξ, h ξ ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ∀ C : ℝ, (∀ ξ, ‖h ξ‖ * (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C) → Summable h := by
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice E (Fin n) one_pos
  set L := GlobalTheory.WeilM.denomLattice E (Fin n) 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  refine ⟨r, fun M h hM hsupp B hdec => ?_⟩
  have hB : 0 ≤ B := le_trans (by positivity) (hdec 0)
  let S : Set (Fin n → E) := {ξ | ∀ i, ∃ o : 𝓞 E, (M : E) * ξ i = o}
  let v : (Fin n → E) → (Fin n → mixedEmbedding.mixedSpace E) := fun ξ i => mixedEmbedding E ((M : E) * ξ i)
  have hmem : ∀ ξ ∈ S, v ξ ∈ L := by
    intro ξ hξ i
    obtain ⟨o, ho⟩ := hξ i
    rw [Nat.cast_one, one_smul]
    show mixedEmbedding E ((M : E) * ξ i) ∈ mixedEmbedding.integerLattice E
    rw [ho]
    exact ⟨o, rfl⟩
  let j : S → L := fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩
  have hMF : (M : E) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
    mul_left_cancel₀ hMF (mixedEmbedding_injective E (congrFun (congrArg Subtype.val hab) i)))
  let G : (Fin n → E) → ℝ := S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹
  have hGs : Summable G := by
    rw [← summable_subtype_iff_indicator]
    exact (hL.comp_injective hj).mul_left _
  have hbound : ∀ ξ : Fin n → E, ‖h ξ‖ ≤ G ξ := by
    intro ξ
    by_cases h0 : h ξ = 0
    · rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hξ : ξ ∈ S := hsupp ξ h0
    rw [show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]
    set s := ∑ i, ∑ w : InfinitePlace E, w (ξ i) with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
    have hv := GlobalTheory.RatPointSum.norm_mixedEmbedding_nat_mul_le M ξ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s) := by
      show 1 + ‖(fun i => mixedEmbedding E ((M : E) * ξ i))‖ ≤ _
      nlinarith
    have hpos : 0 < (1 + s) ^ r := by positivity
    have hvpos : 0 < (1 + ‖v ξ‖) ^ r := by positivity
    have h2 : ‖h ξ‖ ≤ B / (1 + s) ^ r := by
      rw [le_div_iff₀ hpos]; exact hdec ξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  exact Summable.of_norm_bounded hGs hbound

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ φ ∈ schA F (Fin n × Fin d₁), Summable (fun w : Fin d₁ → E => thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ))) := by
  intro hKP F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he hB hXW φ hφ
  obtain ⟨N, hN, hsupp⟩ := GlobalTheory.T.eigen_relation_models_matrix_set hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he hB hXW φ hφ
  obtain ⟨K, hA⟩ := summable_of_denom_decay' E d₁
  obtain ⟨C, hC⟩ := GlobalTheory.T.model_eigen_relation_second_form hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he hB hXW φ hφ N K hN
  have hz : ∀ w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) ≠ 0 →
      ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o := by
    intro w h0
    refine hsupp w fun h1 => h0 ?_
    rw [h1]
    simp [thetaSum]
  refine hA N _ hN hz (max C 0) fun w => ?_
  by_cases hw : ∀ i, ∃ o : 𝓞 E, (N : E) * w i = o
  · exact (hC w hw).trans (le_max_left _ _)
  · have h0 : thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ)) = 0 := by
      by_contra h
      exact hw (hz w h)
    rw [h0, norm_zero, zero_mul]
    exact le_max_right _ _

end GlobalTheory.ExpandSummX
