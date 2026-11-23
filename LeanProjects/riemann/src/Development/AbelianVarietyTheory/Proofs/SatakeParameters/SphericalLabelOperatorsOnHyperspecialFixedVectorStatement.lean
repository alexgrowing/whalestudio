import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), (∀ d R, SphOp V P d R → R.card = (rep V P d).card ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → ∑ γ ∈ R, π γ u = opOf π P (Finsupp.single d 1) u) ∧ (∀ c, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → ∀ k ∈ hyp V P, π k (opOf π P c u) = opOf π P c u) ∧ (IsLab V P (List.replicate V.rank 0) ∧ ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P (Finsupp.single (List.replicate V.rank 0) 1) u = u) ∧ (∀ d, (IsLab V P d ↔ IsLab V P (dualLab d)) ∧ (rep V P (dualLab d)).card = (rep V P d).card) ∧ ∀ e f g, IsPrimeIdem P e f → SuppF V f g → ∃ d, IsLab V P d ∧ (∀ γ ∈ rep V P d, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * g * k₂) ∧ ∀ γ ∈ rep V P (dualLab d), ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * g⁻¹ * k₂ := by
  first | exact @GlobalTheory.SphLabelOps.label_operators | exact GlobalTheory.SphLabelOps.label_operators | (intros; apply GlobalTheory.SphLabelOps.label_operators <;> assumption)
