import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LetterSumEqTauSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.letter_sum_eq_tau_sum : ∀ (D : D7) (O : Setup D) (g : (D.host.E →+* ℂ) × ℕ → ℝ),
    ∑ j : Fin (letters O.S.Dw).length, g (((letters O.S.Dw).get j).1, (((letters O.S.Dw).get j).2 : ℕ)) =
      ∑ τ : D.what₂.Tau, ((∑ i ∈ Finset.range O.j, g (DV.tauEmb D τ, i)) +
        ∑ i ∈ Finset.range (O.N - O.j), g (conjEmb (DV.tauEmb D τ), i)) := by
  first | exact @GlobalTheory.LieLetters.sum_letters_eq_sum_tau | exact GlobalTheory.LieLetters.sum_letters_eq_sum_tau | (intros; apply GlobalTheory.LieLetters.sum_letters_eq_sum_tau <;> assumption)
