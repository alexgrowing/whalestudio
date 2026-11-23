import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothBoundKappa
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
theorem _root_.GlobalTheory.T.potential_smooth_bound_kappa : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y),
    Y.dim = e → ∀ (a : Fin (M.n + 1)) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)), (∀ i, Y.mSmooth (I.ε a) (Δ i) (m i (I.ε a))) →
    ∀ (t : ι → ℝ) {P : M.Pot}, I.FormOf m t P → IsPotential (M.A a) (P a) →
    ∀ (g : Pts Y (I.ε a) → ℝ), (Y.an (I.ε a)).SmoothOn Set.univ g → ∀ (κ : ℝ),
    (∀ (c : AlgChart Y.str (I.ε a) Y.dim), ∀ y ∈ c.e.source, ∀ x, (I.pt a).symm y ∈ (M.Om a).U x → ∀ ξ,
      0 ≤ ∑ i, t i * (Real.pi / 2 * curvMet (m i (I.ε a)) c y ξ) + c.levi g y ξ +
        κ * c.levi (fun z => (M.Om a).φ x ((I.pt a).symm z)) y ξ) →
    IsPsh (M.A a) (P a + LocPot.ofFun (fun z => g (I.pt a z)) + (M.Om a).rsmul κ) := by
  first | exact @GlobalTheory.PshTrans.isPsh_of_levi_algChart | exact GlobalTheory.PshTrans.isPsh_of_levi_algChart | (intros; apply GlobalTheory.PshTrans.isPsh_of_levi_algChart <;> assumption)
