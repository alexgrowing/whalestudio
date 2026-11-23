import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O GlobalTheory.TrueGeo GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_of_combined_metrics : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : GlobalTheory.ProjVar.Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (ι : Type) [Fintype ι] (Δ : ι → Y.Dv) (m : ∀ i (σ : F →+* ℂ), (cxSt F).Met Y σ (Δ i)) (b : ι → ℤ) (Q : ι → LocPot (M.X a)), Y.dim = e → (∀ i σ, (cxSt F).mSmooth Y σ (Δ i) (m i σ)) → (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) → mInt (M.A a) (fun _ => InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)) (fun _ => 1) = (Y.inter (fun _ => ∑ i, b i • Δ i) : ℝ) := by
  first | exact @GlobalTheory.CombChern.mInt_combPot_eq_inter | exact GlobalTheory.CombChern.mInt_combPot_eq_inter | (intros; apply GlobalTheory.CombChern.mInt_combPot_eq_inter <;> assumption)
