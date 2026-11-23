import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.ContractLinear

open Formalism.FourierDecayAlt.P

theorem norm_sq_contract_le {V V₂ : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] {k : ℕ} (a : Fin k → (V₂ →L[ℂ] V))
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) (l : Fin k → ℂ) :
    ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have h0 : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => by positivity
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans (le_of_sq_le_sq ?_ (by positivity))
    rw [mul_pow, Real.sq_sqrt h0]
    exact h3
  calc ‖∑ c, l c • a c‖ ^ 2 ≤ (Real.sqrt (∑ c, ‖l c‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt h0

theorem wigMap_contract : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) ω (B c) • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c₀) (B c) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha heq
  obtain ⟨hexp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((star (B c) ᵥ* Hpk k r) j) * MvPolynomial.X (Sum.inl j), a,
    fun c => ?_, fun ω => ?_⟩, fun h hh ω => ?_, fun t ω => ?_, fun ω hω hωz => ?_⟩, fun c₀ => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl]
    rw [herm, Matrix.dotProduct_mulVec]
    rfl
  · obtain ⟨hW, hpres, -⟩ := hU h hh
    ext y
    have key : ∀ d, herm (Hpk k r) ω (B d) =
        ∑ c, star (herm (Hpk k r) (h *ᵥ B d) (B c)) * herm (Hpk k r) (h *ᵥ ω) (B c) := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← HermitianFormSums.herm_rsum, ← hexp _ h1 h2, hpres]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      heq h hh, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [key d, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
  · simp only [Qx8.herm_smul_left', pow_one, Finset.smul_sum, smul_smul]
  · refine (norm_sq_contract_le a ha _).trans (le_of_eq ?_)
    have h1 := HermitianFormSums.herm_comb hB (fun c => herm (Hpk k r) ω (B c)) (fun c => herm (Hpk k r) ω (B c))
    rw [← hexp ω hω hωz] at h1
    rw [pow_one, h1, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · simp [hB.2.1]

end GlobalTheory.ContractLinear
