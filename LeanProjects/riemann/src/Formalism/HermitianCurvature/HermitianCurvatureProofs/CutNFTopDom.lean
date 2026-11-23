import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def NFOpOK (C : ℝ) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq) : Prop :=
  B.SmoothCoef (B.GPos p.T.base) Th ∧ B.Commutes p.T.base (B.GPos p.T.base) Th ∧
    CutMP.GlobCoef Th (C * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) ∧
    (B.opOrder Th : ℝ) ≤ C * CutMP.nDim P.k P.r * ((N : ℝ) + 1)

def NFDomZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ),
    ¬ (D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)) → topD p H w c = 0

def NFDomPtw : Prop :=
  ∀ Cb : ℝ, ∃ Cc C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ) (w : List C.Letter), TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∃ (m : ℕ) (Th : Fin m → B.DiffOp P.k P.r Wp Wq) (Mb : ℝ), 0 ≤ Mb ∧ (∀ t, NFOpOK C₁ p N (Th t)) ∧
        ∀ (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ), NFHyp Cb Cc p f A₀ p₀ χ N →
        ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) →
          0 < TBB.Gp p (TBB.bigPt P.r c) →
          ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c‖ ≤
            Mb * ∑ t, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
              TBB.Ew p (fun _ => 1) (B.opApply (Th t) f) (P.r + 1) [] (TBB.bigPt P.r c)

def DominatedL2OperatorBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      Integrable (fun c : Fin (P.r + 1) → ℂ => ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (B.opApply Th f) (P.r + 1) [] (TBB.bigPt P.r c))

def NFDomMeas : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      AEStronglyMeasurable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w)
        volume

theorem domination_at_zero_holds : NFDomZero := by
  intro Wp Wq _ _ _ _ _ _ P p H w c hc
  unfold topD TBB.Ew TBB.NP KB.Pl.RR
  generalize TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) = a
  generalize TBB.normC (fun x => 1) w = b
  generalize TBB.bigPt P.r c = x at hc ⊢
  unfold D.RRplace
  by_cases hl : D.IsLocPt x (P.r + 1)
  · have hG : ¬ 0 < TBB.Gp p x := fun h => hc ⟨hl, h⟩
    rw [dif_pos ⟨hl, hl⟩, dif_neg (by omega)]
    have hv : ∀ H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp), D.vecV p.T.base p.ν' p.m₀ H' x = 0 := by
      intro H'
      unfold D.vecV
      rw [dif_neg]
      rintro ⟨-, h⟩
      apply hG
      unfold TBB.Gp
      exact h
    have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    have hi0 : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
      simp [B.hsInner, h0]
    simp [hv]
    split_ifs with hw
    · simp [hi0]
    · unfold Top.topOf
      simp [hv, hi0]
  · simp [hl]

end

end Formalism.FourierDecayAlt.P.CutBP
