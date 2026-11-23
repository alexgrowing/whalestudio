import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedByBadPrimes
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bounded_by_bad_primes : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) [IsLocallyNoetherian V.X] (M : HermLB V.p)
    (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg →
    ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ l ∈ S, l.Prime ∧ 0 ≤ a l) →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y),
      |lg v e y| ≤ (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) →
    ∃ (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r),
      (∀ σ, ∀ y ∈ offSupp V.p σ (M.div hr), logNorm (M.φ σ) r y = 0) ∧
      (∀ z, |((M.div hr).mult z : ℝ)| ≤ ∑ l ∈ S, a l * (Scheme.ord ((l : V.X.functionField)) z : ℝ)) ∧
      RatNorms V M r lg := by
  first | exact @GlobalTheory.PairTerm.exists_ratSec_orders_le_ratNorms | exact GlobalTheory.PairTerm.exists_ratSec_orders_le_ratNorms | (intros; apply GlobalTheory.PairTerm.exists_ratSec_orders_le_ratNorms <;> assumption)
