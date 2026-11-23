import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmu

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def Present (F : JFam P.k P.r Wp Wq) (μ : Fin (2 * P.r + P.k + 1) → ℤ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ) ∧ (F.A μ).l (F.A μ).w0 ≠ 0 ∧ (F.A μ).l' (F.A μ).w0 ≠ 0

theorem J_eq_zero_of_not_present (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : JFam P.k P.r Wp Wq)
    (μ : Fin (2 * P.r + P.k + 1) → ℤ) (h : ¬ Present F μ) : F.J Bs μ = 0 := by
  by_cases hc : Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ)
  · rw [JFam.J_of_hc Bs F μ hc]
    apply coef_eq_zero_of
    by_contra h'
    push Not at h'
    exact h ⟨hc, h'.1, h'.2⟩
  · exact JFam.J_of_not_hc Bs F μ hc

theorem norm_sq_zero_function (p : KB.Pl P Wp Wq) : TBB.jN2 p (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = 0 := by
  have e : (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = fun g => (0 : ℂ) • (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) g := by
    funext g
    simp
  rw [e, norm_sq_const_smul]
  simp

theorem V_zero_fun (p : KB.Pl P Wp Wq) (γ : C.LPt) : p.V (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) γ = 0 := by
  have e : (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = fun g => (0 : ℂ) • (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) g := by
    funext g
    simp
  rw [e, V_csmul]
  simp

def NormDeg (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ →
    TBB.jN2 p (F.J p.T.base μ) = ENNReal.ofReal (c * (F.A μ).deg p.T.base.μG)

def DegPos (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ → 0 < (F.A μ).deg p.T.base.μG

def DegRatio (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ (I : Finset (Fin (2 * P.r + P.k + 1))), I.card = P.r + 1 → LatticeNorms.N1 (μ - lam0) ≤ q0 →
    LatticeNorms.N1 (μ + LatticeNorms.eI I - lam0) ≤ q0 → Present F μ → Present F (μ + LatticeNorms.eI I) →
    (F.A (μ + LatticeNorms.eI I)).deg p.T.base.μG ≤
      (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) * (F.A μ).deg p.T.base.μG

theorem pieri_degree_of_family (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ)
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) (c0 q0 : ℕ) (H : ℝ)
    (hc0 : P.r + 1 ≤ c0) (hN : NormDeg p F lam0 q0) (hpos : DegPos p F lam0 q0) (hR : DegRatio p F lam0 q0)
    (hP0 : Present F lam0) : PieriDegreeConditions p (pieriDataOfFamily p F lam0 tau c0 q0 H) := by
  obtain ⟨c, hc, hN⟩ := hN
  have hz := J_eq_zero_of_not_present p.T.base F
  refine ⟨?_, fun μ hμ => ⟨?_, ?_⟩, ?_⟩
  · show 0 < TBB.jN2 p (F.J p.T.base lam0)
    have h0 : LatticeNorms.N1 (lam0 - lam0) ≤ q0 := by rw [sub_self, LatticeNorms.n1_zero]; exact Nat.zero_le _
    rw [hN lam0 h0 hP0]
    exact ENNReal.ofReal_pos.2 (mul_pos hc (hpos lam0 h0 hP0))
  · show TBB.jN2 p (F.J p.T.base μ) < ⊤
    by_cases hp : Present F μ
    · rw [hN μ hμ hp]
      exact ENNReal.ofReal_lt_top
    · rw [hz μ hp, norm_sq_zero_function]
      exact ENNReal.zero_lt_top
  · intro h0 cc _ _
    show p.V (F.J p.T.base μ) _ = 0
    by_cases hp : Present F μ
    · exfalso
      change TBB.jN2 p (F.J p.T.base μ) = 0 at h0
      rw [hN μ hμ hp] at h0
      exact (ENNReal.ofReal_pos.2 (mul_pos hc (hpos μ hμ hp))).ne' h0
    · rw [hz μ hp]
      exact V_zero_fun p _
  · show ∀ μ : Fin (2 * P.r + P.k + 1) → ℤ, LatticeNorms.N1 (μ - lam0) + c0 ≤ q0 → TBB.jN2 p (F.J p.T.base μ) ≠ 0 →
      ∀ I ∈ powersetCard (P.r + 1) (univ : Finset (Fin (2 * P.r + P.k + 1))),
        TBB.jN2 p (F.J p.T.base (μ + LatticeNorms.eI I)) ≤
          ENNReal.ofReal ((Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1)) * TBB.jN2 p (F.J p.T.base μ)
    intro μ hμ hne I hI
    have hp : Present F μ := by
      by_contra hp
      rw [hz μ hp, norm_sq_zero_function] at hne
      exact hne rfl
    have hcard : I.card = P.r + 1 := (mem_powersetCard.1 hI).2
    have hμ' : LatticeNorms.N1 (μ - lam0) ≤ q0 := by omega
    have hI' : LatticeNorms.N1 (μ + LatticeNorms.eI I - lam0) ≤ q0 := by
      have e : μ + LatticeNorms.eI I - lam0 = (μ - lam0) + LatticeNorms.eI I := by abel
      have h1 := LatticeNorms.n1_add_le (μ - lam0) (LatticeNorms.eI I)
      rw [LatticeNorms.n1_eI_eq_card, hcard] at h1
      rw [e]
      omega
    by_cases hq : Present F (μ + LatticeNorms.eI I)
    · have hd := hR μ I hcard hμ' hI' hp hq
      have hE : 0 ≤ (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) := by positivity
      rw [hN _ hI' hq, hN μ hμ' hp, ← ENNReal.ofReal_mul hE]
      apply ENNReal.ofReal_le_ofReal
      calc c * (F.A (μ + LatticeNorms.eI I)).deg p.T.base.μG
          ≤ c * ((Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) * (F.A μ).deg p.T.base.μG) :=
            mul_le_mul_of_nonneg_left hd hc.le
        _ = _ := by ring
    · rw [hz _ hq, norm_sq_zero_function]
      exact bot_le

end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
