import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh.ContrPlus

theorem herm_sum_smul_left {ι κ : Type} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (l : κ → ℂ) (B : κ → ι → ℂ)
    (w : ι → ℂ) : herm H (∑ c, l c • B c) w = ∑ c, l c * herm H (B c) w := by
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_conj {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (v w : ι → ℂ) :
    herm H w v = star (herm H v w) := by
  unfold herm
  rw [← star_dotProduct_star, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem herm_real_smul_right {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (t : ℝ) (v w : ι → ℂ) :
    herm H v ((t : ℂ) • w) = (t : ℂ) * herm H v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  simp

theorem opNorm_sum_smul_sq_le {V V₂ κ : Type} [Fintype κ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (a : κ → (V₂ →L[ℂ] V)) (l : κ → ℂ)
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) : ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have hS : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans ?_
    have h4 := Real.le_sqrt_of_sq_le h3
    rwa [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg y)] at h4
  calc _ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := Real.sq_sqrt hS

theorem contraction_wigMap :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) (B c) ω • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c) (B c₀) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha hequi
  obtain ⟨hcomp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  have hH : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((Hpk k r *ᵥ B c) j) * MvPolynomial.X (Sum.inr j), a, ?_, ?_⟩,
    ?_, ?_, ?_⟩, ?_⟩
  · intro c
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · intro ω
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [herm, dotProduct, mul_comm]
  · intro h hh ω
    obtain ⟨hW, hiso, -⟩ := hU h hh
    ext y
    have key : ∀ d, ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) * herm (Hpk k r) (B c) (h *ᵥ ω)
        = herm (Hpk k r) (B d) ω := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2, hiso]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, hequi h hh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, ← key d]
    simp only [mul_comm]
  · intro t ω
    simp only [herm_real_smul_right, pow_one, Finset.smul_sum, smul_smul]
  · intro ω h1 h2
    rw [pow_one]
    refine (opNorm_sum_smul_sq_le a _ ha).trans (le_of_eq ?_)
    have h3 : herm (Hpk k r) ω ω = ∑ c, herm (Hpk k r) ω (B c) * herm (Hpk k r) (B c) ω := by
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2]
    rw [h3, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [herm_conj _ hH (B c) ω, Complex.star_def, Complex.conj_mul']
    norm_cast
  · intro c₀
    simp [hB.2.1]

end GlobalTheory.WigSh.ContrPlus
