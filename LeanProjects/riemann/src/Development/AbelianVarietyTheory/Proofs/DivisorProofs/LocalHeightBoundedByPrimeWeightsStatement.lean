import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_height_bounded_by_prime_weights : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) [IsLocallyNoetherian V.X] (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ l ∈ S, l.Prime ∧ 0 ≤ a l) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y), |lg v e y| ≤ (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) → ∃ (r : M.B.ι → V.X.functionFieldˣ) (hr : IsRatSec M.B r), (∀ σ, ∀ y ∈ offSupp V.p σ (M.div hr), logNorm (M.φ σ) r y = 0) ∧ ∀ z, |((M.div hr).mult z : ℝ)| ≤ ∑ l ∈ S, a l * (Scheme.ord ((l : V.X.functionField)) z : ℝ) := by
  first | exact @GlobalTheory.VertOrd.exists_ratSec_orders_le | exact GlobalTheory.VertOrd.exists_ratSec_orders_le | (intros; apply GlobalTheory.VertOrd.exists_ratSec_orders_le <;> assumption)
