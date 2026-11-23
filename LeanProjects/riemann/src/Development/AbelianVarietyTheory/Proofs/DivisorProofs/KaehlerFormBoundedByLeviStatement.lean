import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFormBoundedByLevi
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_form_bounded_by_levi : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y),
    Y.dim = e → ∀ (a : Fin (M.n + 1)) (om : ChartForm Y.str (I.ε a) Y.dim), IsKaehlerForm (Y.an (I.ε a)) om →
    ∃ K : ℝ, 0 < K ∧ ∀ (c : AlgChart Y.str (I.ε a) Y.dim), ∀ y ∈ c.e.source, ∀ x, (I.pt a).symm y ∈ (M.Om a).U x →
      ∀ ξ, 0 ≤ c.levi (fun z => (M.Om a).φ x ((I.pt a).symm z)) y ξ ∧
        om c y ξ ≤ K * c.levi (fun z => (M.Om a).φ x ((I.pt a).symm z)) y ξ := by
  first | exact @GlobalTheory.KaehlerCmp.kaehler_le_levi_Om | exact GlobalTheory.KaehlerCmp.kaehler_le_levi_Om | (intros; apply GlobalTheory.KaehlerCmp.kaehler_le_levi_Om <;> assumption)
