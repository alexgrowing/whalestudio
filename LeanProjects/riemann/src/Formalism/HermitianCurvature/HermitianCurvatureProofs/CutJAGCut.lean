import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfWBOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfPoly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolynomialBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompactRegionEstimate
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.WeightBoundMultiplicative

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gcut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gcut_ckOn_smul {m : ℕ∞} {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn m (B.GV k r) F) :
    B.CkOn m (B.GV k r) (fun g => a g • F g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF g₀ hg₀
  refine ⟨U, fun g => a g • f' g, hU, hgU,
    ((ha.of_le (by exact_mod_cast le_top)).contDiffOn).smul hc, fun g hg hG => ?_⟩
  simp only [hff g hg hG]

theorem gcut_sum_const {X : Type*} (c : ℕ) (l : List X) :
    (((l.map (fun _ => c)).sum : ℕ) : ℝ) = (c : ℝ) * l.length := by
  have h : ∀ l : List X, (l.map (fun _ => c)).sum = c * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [h]; push_cast; ring

theorem gcut_leib {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) (c n : ℕ) (Ca : ℝ)
    (hWB : PI.UnitaryCorollaryDerivatives.WB (fun _ => c) a n Ca 0)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) {A Bg : ℝ} (hc : (c : ℝ) ≤ Bg)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.InCC (A - Bg * n) n (fun g => a g • F g) := by
  choose cF hcF using hFg
  set K : ℝ := ∑ j ∈ Finset.range (n + 1), |cF j| with hK
  have hKj : ∀ j ≤ n, |cF j| ≤ K := fun j hj =>
    Finset.single_le_sum (f := fun j => |cF j|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBg : 0 ≤ Bg := le_trans (Nat.cast_nonneg c) hc
  refine ⟨2 ^ n * (|Ca| * K), gcut_ckOn_smul ha (sCkOn_mono le_top hF), fun u v hu hv hl g hg => ?_⟩
  set L : ℂ →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) with hL
  set a' : B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun h => L (a h) with ha'
  have hfun : (fun g => a g • F g) = ap a' F := by funext h; simp [ap, ha', hL]
  have hlie := lie_LR (unit_lie hu) (unit_lie hv)
  have hca : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a' := (L.restrictScalars ℝ).contDiff.comp ha
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) ((wL u ++ wR v).length : ℕ) a' F :=
    ⟨PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff hca, sCkOn_mono le_top hF, fun _ _ h => absurd h (Set.notMem_empty _)⟩
  have hp := gN_pos hg
  have hg1 := gN_ge_one hg
  have hLn : ∀ x : ℂ, ‖L x‖ ≤ ‖x‖ := by
    intro x
    have : L x = x • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by simp [hL]
    rw [this, norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le)
  have hw : (wL u ++ wR v).length = u.length + v.length := len_LR u v
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg
    (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) (wL u ++ wR v) a' F hlie hP (by
      intro w₁ w₂ hs₁ hs₂ hl₁₂
      obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR hs₁
      obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR hs₂
      rw [len_LR, len_LR] at hl₁₂
      have hl₁ : u₁.length + v₁.length ≤ n := by
        have := hu₁.length_le; have := hv₁.length_le; omega
      have hl₂ : u₂.length + v₂.length ≤ n := by
        have := hu₂.length_le; have := hv₂.length_le; omega
      have hu₁' : ∀ X ∈ u₁, B.unitLie k r X := fun X hX => hu X (hu₁.subset hX)
      have hv₁' : ∀ X ∈ v₁, B.unitLie k r X := fun X hX => hv X (hv₁.subset hX)
      have hu₂' : ∀ X ∈ u₂, B.unitLie k r X := fun X hX => hu X (hu₂.subset hX)
      have hv₂' : ∀ X ∈ v₂, B.unitLie k r X := fun X hX => hv X (hv₂.subset hX)
      have ea : Dw (wL u₁ ++ wR v₁) a' g = L (Dw (wL u₁ ++ wR v₁) a g) :=
        PI.UnitaryCorollaryDerivatives.Dw_clm L _ (lie_LR (unit_lie hu₁') (unit_lie hv₁'))
          (PI.UnitaryCorollaryDerivatives.ckOn_of_contDiff ha) g hg
      set L₁ : ℝ := ((u₁.length + v₁.length : ℕ) : ℝ) with hL₁
      set L₂ : ℝ := ((u₂.length + v₂.length : ℕ) : ℝ) with hL₂
      have b1 : ‖Dw (wL u₁ ++ wR v₁) a' g‖ ≤ |Ca| * B.gN g ^ (Bg * L₁) := by
        rw [ea]
        refine (hLn _).trans ?_
        rw [← dLR_eq]
        have h1 := hWB u₁ v₁ hu₁' hv₁' hl₁ g hg
        rw [gcut_sum_const, List.length_append, zero_add] at h1
        have h1' : ‖B.dLR u₁ v₁ a g‖ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := by
          rw [hL₁]; exact h1
        have h2 : B.gN g ^ ((c : ℝ) * L₁) ≤ B.gN g ^ (Bg * L₁) :=
          Real.rpow_le_rpow_of_exponent_le hg1 (mul_le_mul_of_nonneg_right hc (by rw [hL₁]; positivity))
        calc _ ≤ Ca * B.gN g ^ ((c : ℝ) * L₁) := h1'
          _ ≤ |Ca| * B.gN g ^ ((c : ℝ) * L₁) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hp.le _)
          _ ≤ |Ca| * B.gN g ^ (Bg * L₁) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      have b2 : ‖Dw (wL u₂ ++ wR v₂) F g‖ ≤ K * B.gN g ^ (Bg * L₂ - A) := by
        rw [← dLR_eq]
        have h1 := (hcF (u₂.length + v₂.length)).2 u₂ v₂ hu₂' hv₂' le_rfl g hg
        have e : B.gN g ^ (Bg * L₂ - A) * B.gN g ^ (A - Bg * L₂) = 1 := by
          rw [← Real.rpow_add hp]; simp
        have h4 : ‖B.dLR u₂ v₂ F g‖ = B.gN g ^ (Bg * L₂ - A) * (B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖) := by
          rw [← mul_assoc, e, one_mul]
        rw [h4]
        have h5 : B.gN g ^ (A - Bg * L₂) * ‖B.dLR u₂ v₂ F g‖ ≤ K := by
          refine le_trans ?_ (hKj _ hl₂)
          refine le_trans ?_ (le_abs_self _)
          simpa [hL₂] using h1
        calc _ ≤ B.gN g ^ (Bg * L₂ - A) * K := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hp.le _)
          _ = K * B.gN g ^ (Bg * L₂ - A) := mul_comm _ _
      have hsum : Bg * L₁ + (Bg * L₂ - A) = Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A := by
        rw [← hl₁₂, hL₁, hL₂]; push_cast; ring
      calc ‖Dw (wL u₁ ++ wR v₁) a' g‖ * ‖Dw (wL u₂ ++ wR v₂) F g‖
          ≤ (|Ca| * B.gN g ^ (Bg * L₁)) * (K * B.gN g ^ (Bg * L₂ - A)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hp.le _))
        _ = |Ca| * K * (B.gN g ^ (Bg * L₁) * B.gN g ^ (Bg * L₂ - A)) := by ring
        _ = |Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) := by
            rw [← Real.rpow_add hp, hsum])
  rw [hfun, dLR_eq]
  have hlen : ((wL u ++ wR v).length : ℕ) ≤ n := by rw [hw]; exact hl
  have e2 : B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A) ≤ 1 := by
    rw [← Real.rpow_add hp]
    refine Real.rpow_le_one_of_one_le_of_nonpos hg1 ?_
    have : (((wL u ++ wR v).length : ℕ) : ℝ) ≤ n := by exact_mod_cast hlen
    nlinarith
  have e3 : (2 : ℝ) ^ (wL u ++ wR v).length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hlen
  have hCK : 0 ≤ |Ca| * K := mul_nonneg (abs_nonneg _) hK0
  calc B.gN g ^ (A - Bg * n) * ‖Dw (wL u ++ wR v) (ap a' F) g‖
      ≤ B.gN g ^ (A - Bg * n) * (2 ^ (wL u ++ wR v).length *
          (|Ca| * K * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)
    _ = 2 ^ (wL u ++ wR v).length * (|Ca| * K) *
          (B.gN g ^ (A - Bg * n) * B.gN g ^ (Bg * (((wL u ++ wR v).length : ℕ) : ℝ) - A)) := by ring
    _ ≤ 2 ^ (wL u ++ wR v).length * (|Ca| * K) * 1 :=
        mul_le_mul_of_nonneg_left e2 (mul_nonneg (by positivity) hCK)
    _ ≤ 2 ^ n * (|Ca| * K) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right e3 hCK

theorem gcut_graded (z z' : Fin (2 * r + k + 1) → ℂ) (h : ℝ → ℝ) (ε : ℝ) (hh : U.IsCutG ε h) {A Bg : ℝ}
    (hBg : 2 * ((r : ℝ) + 1) ≤ Bg) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F)
    (hFg : ∀ m : ℕ, B.InCC (A - Bg * m) m F) :
    B.CkOn ⊤ (B.GV k r) (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) ∧
      ∀ m : ℕ, B.InCC (A - Bg * m) m (fun g => ((h (Gf k r z z' g) : ℝ) : ℂ) • F g) := by
  have hW := PI.UnitaryCorollaryDerivatives.gfWB_of PI.UnitaryCorollaryDerivatives.generating_function_polynomial PI.UnitaryCorollaryDerivatives.polynomial_bound PI.UnitaryCorollaryDerivatives.compact_region_estimate
  have hcd := (hW k r z z' h ε 0 hh).1
  refine ⟨gcut_ckOn_smul hcd hF, fun m => ?_⟩
  obtain ⟨C, hC⟩ := (hW k r z z' h ε m hh).2
  exact gcut_leib hcd (2 * (r + 1)) m C hC hF (by push_cast; linarith) hFg

end gcut

end Formalism.FourierDecayAlt.P.CutMP.JA

end
