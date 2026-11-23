import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def Ann (P : M.Par) : Set ℂ := {ζ : ℂ | P.TT < Complex.normSq ζ}

def fnZ (P : M.Par) (f : ℂ → ℂ) : MA.SmQ P.r P.TT := MA.toSm P (fun q => f q.1.2)

def dzQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzP).1 f

def dzbQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzbP).1 f

def modA (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * star ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))

def modB (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))

def ConnF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P),
    trR P Bs e (d.L.nab.1 Φ) ρ = dzQ P (trR P Bs e Φ ρ) + fnZ P (A ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e (d.L.nabs.1 Φ) ρ = -dzbQ P (trR P Bs e Φ ρ) + fnZ P (B ρ) * trR P Bs e Φ ρ

def SmAB (P : M.Par) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A ρ) (Ann P) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B ρ) (Ann P)

def PhaseEq (P : M.Par) (A B u : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 ∧
    A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ = modA P ρ ζ ∧ B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ = modB P ρ ζ

end preds

def GTCLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ A B : M.Ty P → ℂ → ℂ, SmAB P A B ∧ ConnF P Bs d e A B

def GTCReal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)

def GTCCurv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0

def GTCHol : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A ρ w) 0 R).im = Real.pi * n

def GTCAnnulus : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ), 0 ≤ TT → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (NF.dZb α ζ).re = 0) →
    (∀ R : ℝ, 0 < R → TT < R ^ 2 → ∃ n : ℤ, (circleIntegral α 0 R).im = Real.pi * n) →
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = α ζ ∧ star (u ζ) * NF.dZb u ζ = -star (α ζ)

def GTCGauge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B u : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → PhaseEq P A B u →
        IsFrameB P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) ∧ KapF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) ∧
          NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ)

def GTCTT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → 0 ≤ P.TT

def GTCPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∃ u, PhaseEq P A B u

theorem modA_smooth (P : M.Par) (ρ : M.Ty P) (hTT : 0 ≤ P.TT) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'

theorem star_modA (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : star (modA P ρ ζ) = modB P ρ ζ := by
  simp only [modA, modB]
  first
  | (rw [star_div₀, star_mul', star_sub, star_star]; simp [Complex.conj_ofReal]; done)
  | (simp [map_div₀, Complex.conj_ofReal]; done)
  | (rw [star_div₀, star_mul', star_sub, star_star]
     simp only [Complex.star_def, Complex.conj_ofReal]; done)

def GTCPhaseOfCut : Prop := GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTCTT → GTCPhase

theorem gTCPhase_of_cut : GTCPhaseOfCut := by
  intro hR hC hH hA hT Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn
  have hTT := hT Wp Wq P Bs X d hyp
  have hex : ∀ ρ : M.Ty P, ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | P.TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = modA P ρ ζ - A ρ ζ ∧
          star (u ζ) * NF.dZb u ζ = -star (modA P ρ ζ - A ρ ζ) := by
    intro ρ
    refine hA P.TT (fun w => modA P ρ w - A ρ w) hTT ((modA_smooth P ρ hTT).sub (hAB ρ).1) ?_ ?_
    · intro ζ hζ
      exact hC Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
    · intro R hR0 hR2
      exact hH Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR2
  choose u hu using hex
  refine ⟨u, fun ρ => ⟨(hu ρ).1, fun ζ hζ => ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := (hu ρ).2 ζ hζ
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]; ring
  · rw [h3, hR Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ, star_sub, star_modA]; ring

def GTConnOfCut : Prop := GTCLocal → GTCPhase → GTCGauge → GTConn

theorem gTConn_of_cut : GTConnOfCut := by
  intro hL hP hG Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk
  obtain ⟨A, B', hAB, hC⟩ := hL Wp Wq P Bs X d hH e he hk
  obtain ⟨u, hu⟩ := hP Wp Wq P Bs X d hH e he hk A B' hAB hC
  exact ⟨_, hG Wp Wq P Bs X d hH e he hk A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
