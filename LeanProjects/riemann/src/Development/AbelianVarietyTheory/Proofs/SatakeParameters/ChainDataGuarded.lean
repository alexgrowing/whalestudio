import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

noncomputable section

namespace GlobalTheory.LastSteps

def ChainDataGuarded : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ), Pr.Ok → cst.Ok → R.m = m2 + 2 →
    ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
      (∀ hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1), SplitAt Ch sel mu cst m2 P hal) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → DualFn P.1 (fhat sel mu cst P f)) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → FnMod P.1 (topDatum Ch sel mu cst m2 P f)) ∧
      (∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (al : L.β m2),
        L.h m2 al P ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1) →
        ∀ (u : Pr.Word) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p₀.deco.1.N p.deco.1.N (facPen Ch sel mu cst L m2 al p₀ p Y P)) ∧
      (∀ (u : Pr.Word), (∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal) →
        ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P))

def LastTwoStepsGuarded : Prop := FourierLattice ∧ ChainDataGuarded

end GlobalTheory.LastSteps
