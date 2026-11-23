import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedHermitianModelsEigenExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewModelEigenTransferStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.ThetaMajorant

theorem sum_le_of_denom_decay (E : Type) [Field E] [NumberField E] (n : ℕ) :
    ∃ K : ℕ, ∀ N : ℕ, 1 ≤ N → ∃ A : ℝ, 0 ≤ A ∧ ∀ (h : (Fin n → E) → ℂ),
      (∀ ξ, h ξ ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ∀ C : ℝ, (∀ ξ, (∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) → ‖h ξ‖ * (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C) →
      ∀ S : Finset (Fin n → E), ∑ ξ ∈ S, ‖h ξ‖ ≤ A * C := by
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice E (Fin n) one_pos
  set L := GlobalTheory.WeilM.denomLattice E (Fin n) 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  refine ⟨r, fun M hM => ?_⟩
  set T := ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹ with hT
  refine ⟨(M : ℝ) ^ r * T, by positivity, fun h hsupp B hdec Sfin => ?_⟩
  have hB : 0 ≤ B := by
    have := hdec 0 (fun i => ⟨0, by simp⟩)
    exact le_trans (by positivity) this
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
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => Set.indicator_nonneg (fun ξ _ => by positivity) ξ
  have hbound : ∀ ξ : Fin n → E, ‖h ξ‖ ≤ G ξ := by
    intro ξ
    by_cases h0 : h ξ = 0
    · rw [h0, norm_zero]
      exact hG0 ξ
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
      rw [le_div_iff₀ hpos]; exact hdec ξ hξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  have htot : ∑' ξ, G ξ ≤ B * (M : ℝ) ^ r * T := by
    rw [← tsum_subtype S (fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹), tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hc : ∀ ξ : S, ((1 + ‖v ξ.1‖) ^ r)⁻¹ = (fun z : L => ((1 + ‖z‖) ^ r)⁻¹) (j ξ) := fun ξ => rfl
    simp_rw [hc]
    exact tsum_comp_le_tsum_of_inj hL (fun z => by positivity) hj
  calc ∑ ξ ∈ Sfin, ‖h ξ‖ ≤ ∑ ξ ∈ Sfin, G ξ := Finset.sum_le_sum fun ξ _ => hbound ξ
    _ ≤ ∑' ξ, G ξ := hGs.sum_le_tsum _ (fun ξ _ => hG0 ξ)
    _ ≤ B * (M : ℝ) ^ r * T := htot
    _ = (M : ℝ) ^ r * T * B := by ring

end GlobalTheory.ThetaMajorant

namespace GlobalTheory.ThetaMajorant

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (f : SInf F (Fin n × Fin d)) (S : Finset (Fin n → E)),
        ∑ ξ ∈ S, ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (pureA F f g)))‖ ≤
          C * (s.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW g hg
  obtain ⟨N, hN, hsupp⟩ := GlobalTheory.T.adapted_hermitian_models_eigen_exists hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW g hg
  obtain ⟨K, hK⟩ := sum_le_of_denom_decay E n
  obtain ⟨A, hA0, hA⟩ := hK N hN
  obtain ⟨s, C, hC0, hC⟩ := GlobalTheory.T.hermitian_skew_model_eigen_transfer hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he hB hM hXW g hg N K hN
  refine ⟨s, A * C, mul_nonneg hA0 hC0, fun f S => ?_⟩
  have hz : ∀ ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (pureA F f g))) ≠ 0 →
      ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o := by
    intro ξ h0
    refine hsupp f ξ fun h1 => h0 ?_
    rw [h1]
    simp [thetaSum]
  have := hA _ hz _ (fun ξ hξ => hC f ξ hξ) S
  rw [mul_assoc]
  exact this

end GlobalTheory.ThetaMajorant
