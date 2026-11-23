import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionCompatibleMeanSquare
import Formalism.SizeWindowBrackets.Losses5OfLossHypD
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainAnalyticVariantOfTop
import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied
import Formalism.SizeWindowBrackets.FixedEpsilonConcreteGrowthBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ErrorExponentBelowOnesFalse
import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBridge

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.MergeGL2c

open Formalism.LFunctionChainParameters Formalism.HermitianLattices Formalism.L2.GlobalTheoryTheory.MergeGL2 Formalism.L2.GlobalTheoryTheory.MergeGL2b

def AnalyticEndUncond : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x)

def AnalyticEndUncondTied : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d

def Chain6AtUncond : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

section Part2

open Formalism Formalism.D5 Formalism.HN Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7

def CoreAt7 (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    Inputs6d (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂

def CoreAt7' (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Fc : ∀ u0, FamC (W u0) m) (Rw : ∀ u0, Rows (Fc u0).toFam) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (fun u0 => (Fc u0).toFam) Lp P cand PR
      BAD Sig Cord eW KW ∧
    (∀ u0, Fam6.GainIn (Fc u0).toFam (inertPs (hostData e q d) N) (Lp u0).cl (TT.card : ℝ) (aTx x ε)) ∧
    Inputs6d' (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Fc Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂

def Chain6At7Uncond : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt7 (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

def Chain6At7'Uncond : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt7' (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

def PublishedFormSixPair : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          CoreAt (q1At ε x) (dAt ε x) A Cord 2 0 K cHH eK eW KW ε x) → LTop7.GrowthBoundAndRiemannHypothesis)

def RHConclusionsOfPrimePairCore : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          CoreAt7 (q1At ε x) (dAt ε x) A Cord 2 0 K cHH eK eW KW ε x) → LTop7.GrowthBoundAndRiemannHypothesis)

def RHConclusionsOfPrimePairCore' : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          CoreAt7' (q1At ε x) (dAt ε x) A Cord 2 0 K cHH eK eW KW ε x) → LTop7.GrowthBoundAndRiemannHypothesis)

end Part2

section Proofs

open Formalism Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6 Formalism.LFunctionChainParameters.LChain7 Formalism.LFunctionChainParameters.LTop7 Formalism.LFunctionChainParameters.LBr2

end Proofs

section Part5

example : PrimeNumberTheoremConsequences.PNTAPRelW := Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak

end Part5

end Formalism.L2.GlobalTheoryTheory.MergeGL2c
