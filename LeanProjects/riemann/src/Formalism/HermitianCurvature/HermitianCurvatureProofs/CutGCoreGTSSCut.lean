import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SSLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
    trR P Bs e ((d.SS l).1 Φ) ρ' = ∑ ρ, fnZ P (s l ρ' ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e ((star (d.SS l)).1 Φ) ρ' = ∑ ρ, fnZ P (t l ρ' ρ) * trR P Bs e Φ ρ

def SmST (P : M.Par) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s l ρ' ρ) (Ann P) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t l ρ' ρ) (Ann P)

end preds

def GTSSLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

def GTRadAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (Y : ℂ) (a b : Fin 2) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∃ K : Set ℂ, IsCompact K ∧ K ⊆ Ann P ∧ ∀ ζ ∈ Ann P, ζ ∉ K →
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0 ∧
          (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0) →
      ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((X.t Y a b Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) =
        ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((X.t (star Y) b a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))

def GTSSAdjPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, ∀ ζ ∈ Ann P, t l ρ ρ' ζ = star (s l ρ' ρ ζ)

def GTSSConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ' ρ : M.Ty P, ∃ C D : ℂ, ∀ ζ ∈ Ann P, s l ρ' ρ ζ = C ∧ t l ρ' ρ ζ = D

def GTSSPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ, SSLoc P Bs d e (fun l ρ' ρ _ => s l ρ' ρ) (fun l ρ' ρ _ => t l ρ' ρ) →
        (∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, t l ρ ρ' = star (s l ρ' ρ)) →
        ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'

theorem fnZ_congr (P : M.Par) {f g : ℂ → ℂ} (h : ∀ ζ ∈ Ann P, f ζ = g ζ) : fnZ P f = fnZ P g := by
  unfold fnZ
  congr 1
  funext q
  exact h _ q.2.2

theorem ann_pt (P : M.Par) (hTT : 0 < P.TT) : ((Real.sqrt P.TT + 1 : ℝ) : ℂ) ∈ Ann P := by
  show P.TT < Complex.normSq (((Real.sqrt P.TT + 1 : ℝ)) : ℂ)
  rw [Complex.normSq_ofReal]
  have h1 := Real.sq_sqrt hTT.le
  have h2 := Real.sqrt_nonneg P.TT
  nlinarith

def GTSSOfCut : Prop := GTSSLocal → GTSSAdjPt → GTSSConst → GTSSPhase → GTSS

theorem gTSS_of_cut : GTSSOfCut := by
  intro hL hA hC hP
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hn
  obtain ⟨s, t, hst, hSL⟩ := hL Wp Wq P Bs X d hH e he hk
  have hc := hC Wp Wq P Bs X d hH e he hk hn s t hst hSL
  choose! C D hCD using hc
  have hζ0 : (((|P.TT| + 1 : ℝ)) : ℂ) ∈ Ann P := by
    show P.TT < Complex.normSq (((|P.TT| + 1 : ℝ)) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  apply hP Wp Wq P Bs X d hH e he hk hn C D
  · intro l hl Φ ρ'
    obtain ⟨h1, h2⟩ := hSL l hl Φ ρ'
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := s l ρ' ρ) (g := fun _ => C l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).1)]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := t l ρ' ρ) (g := fun _ => D l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).2)]
  · intro l hl ρ ρ'
    have h := hA Wp Wq P Bs X d hH e he hk s t hst hSL l hl ρ ρ' _ hζ0
    rw [(hCD l hl ρ ρ' _ hζ0).2, (hCD l hl ρ' ρ _ hζ0).1] at h
    exact h

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
