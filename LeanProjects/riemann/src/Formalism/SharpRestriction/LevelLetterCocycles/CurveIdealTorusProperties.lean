import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.BlochKatoReduction

namespace Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X)

theorem partA_of_partAT (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) (h : partAT bkP i Q k' ψ' eps') :
    partA bkP i Q k' ψ' eps' := by
  obtain ⟨epsT, h0, hs, hb⟩ := h
  unfold partA
  calc ∑ s ∈ SigG bkP i, sLen bkP i s k' Q (psiAt (X.side i s) (ψ'.comp (X.art i Q)))
      ≤ ∑ s ∈ SigG bkP i, ENNReal.ofReal ((nu X i : ℝ) + epsT s) :=
        Finset.sum_le_sum (fun s hs' => hb s ((mem_SigG bkP i s).1 hs'))
    _ = ENNReal.ofReal (∑ s ∈ SigG bkP i, ((nu X i : ℝ) + epsT s)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun s _ => add_nonneg (Nat.cast_nonneg _) (h0 s))).symm
    _ ≤ ENNReal.ofReal (eps' + (nu X i : ℝ) * (SigG bkP i).card) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        linarith

def ReducedLevelRaisingAt (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partAT bkP i Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def ReducedMainClauses (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partAT bkP i Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def ReducedBaseClausesAt (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.E)),
  ∃ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    PsiOk i A Q k' ψ' ∧ partAT bkP i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

end Gen

variable (D : Formalism.BasicNotions.D7)

def CurveIdealTorusProperties (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.ReducedLevelRaisingAt (pin bkP) N0 i

def ReducedMainClausesAll (bkP : BK D) (N0 : D.ntw.Tw → ℕ) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.ReducedMainClauses (pin bkP) N0 i

def ReducedBaseClauses (bkP : BK D) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → Gen.ReducedBaseClausesAt (pin bkP) i

end Formalism.MainNotions.BlochKatoReduction

end
