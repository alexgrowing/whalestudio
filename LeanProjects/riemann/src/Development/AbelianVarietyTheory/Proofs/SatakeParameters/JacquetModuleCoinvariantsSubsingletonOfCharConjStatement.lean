import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConj
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModuleCoinvariants_subsingleton_of_char_conj : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible → ∀ (N H : Subgroup G) (χ : H →* ℂˣ) (v : V), v ≠ 0 → (∀ h : H, π h v = (χ h : ℂ) • v) → (∀ g : G, ∃ h : H, g * h * g⁻¹ ∈ N ∧ χ h ≠ 1) → Subsingleton (Jacquet π N) := by
  first | exact @GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj | exact GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj | (intros; apply GlobalTheory.jacquet_subsingleton_of_char_nontrivial_on_conj <;> assumption)
