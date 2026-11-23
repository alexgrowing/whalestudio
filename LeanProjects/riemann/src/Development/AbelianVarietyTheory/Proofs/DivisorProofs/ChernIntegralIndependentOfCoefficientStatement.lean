import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_independent_of_coefficient : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (D : ℕ), Y.dim = D → ∀ (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : ι → HermLB V.p) (i : ι), L i = M → ∀ (n : ι → ℤ) (σ : 𝓞 F →+* ℂ), ((comb L n).φ σ).chernInt D Set.univ (fun _ => 1) = ((comb L (Function.update n i 0)).φ σ).chernInt D Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.FlatMass.chernInt_comb_update_of_norms | exact GlobalTheory.FlatMass.chernInt_comb_update_of_norms | (intros; apply GlobalTheory.FlatMass.chernInt_comb_update_of_norms <;> assumption)
