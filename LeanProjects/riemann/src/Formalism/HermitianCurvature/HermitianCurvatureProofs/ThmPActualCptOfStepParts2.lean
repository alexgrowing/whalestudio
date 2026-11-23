import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfOuter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousExtensionOfFourierDecay

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

def DecayData (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable D ∧ Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def DerivComb (f : ℂ → ℂ) : Prop :=
  ∃ (n K : ℕ) (C : ℝ) (Dd : Fin K → ℂ → ℂ) (j : Fin K → ℕ) (v : ∀ i, Fin (j i) → ℂ) (a : Fin K → ℂ),
    (∀ i, j i ≤ n) ∧ (∀ i, DecayData n C (Dd i)) ∧
    ∀ t, t ≠ 0 → f t = ∑ i, a i * iteratedFDeriv ℝ (j i) (Dd i) t (v i)

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Gen

def StepPartsCpt2 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r,
      form μ l.castSucc (act (star (bTl L l w) * (RRi L st l.succ w * bTl L l w)) x) y c =
        form μ l.castSucc (act (RRi L st l.succ w * bTl L l w) x) (act (bTl L l w) y) c ∧
      Integrable (fun c' : Cf P.r l.castSucc => ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (act (RRi L st l.succ w * bTl L l w) x a) (act (bTl L l w) y a) (glue l.castSucc c c')) ∧
      DerivComb (ph L st μ l w x y c)

end Formalism.FourierDecayAlt.P5.HerC
