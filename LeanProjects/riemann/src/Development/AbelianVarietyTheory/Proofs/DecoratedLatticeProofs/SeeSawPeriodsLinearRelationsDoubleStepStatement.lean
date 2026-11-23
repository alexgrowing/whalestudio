import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawPeriodsLinearRelationsDoubleStep
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_periods_linearRelations_doubleStep : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (f : I → GA D (c.V (j + 1 + 1)) → ℂ), (∀ i a, IsContAut (c.X j) (φ i a)) → (∀ i, RapidDec _ (f i)) → (∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂))) → (∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∃ v : I → ℂ, (∀ i, Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) (a * q₁.1) (a' * q₂.1)) (v i)) ∧ ∑ i, α i * v i = 0) → ∑ i, α i * (t (s i)).perF j (σ + 1) h (φ i) (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂)) ((t (s i)).pt j P₁)) = 0 := by
  first | exact @GlobalTheory.SeeSaw.VanMany.vanMany | exact GlobalTheory.SeeSaw.VanMany.vanMany | (intros; apply GlobalTheory.SeeSaw.VanMany.vanMany <;> assumption)
