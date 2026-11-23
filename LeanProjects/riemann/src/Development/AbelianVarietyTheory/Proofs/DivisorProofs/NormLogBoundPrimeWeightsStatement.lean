import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLogBoundPrimeWeights
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_log_bound_prime_weights : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (D : ℕ), Y.dim = D → ∀ num : Form (Cl V.p) D, IsArForm D num → ∀ (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ l ∈ S, l.Prime ∧ 0 ≤ a l) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y), |lg v e y| ≤ (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) → ∀ N : Fin D → HermLB V.p, (∀ j, ∀ l ∈ S, NefOver (N j) l) → |num (Fin.cons (cl M) fun j => cl (N j))| ≤ (∑ l ∈ S, a l * Real.log l) * num (Fin.cons (cl (oneB V.p)) fun j => cl (N j)) := by
  first | exact @GlobalTheory.VertBound.abs_num_le | exact GlobalTheory.VertBound.abs_num_le | (intros; apply GlobalTheory.VertBound.abs_num_le <;> assumption)
