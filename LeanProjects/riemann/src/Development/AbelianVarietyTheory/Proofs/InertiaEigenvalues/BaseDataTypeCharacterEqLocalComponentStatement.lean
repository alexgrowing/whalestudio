import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseDataTypeCharacterEqLocalComponent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_data_type_character_eq_local_component : ∀ (D : D7) (S T : HSp D) (B : GlobalTheory.ExportSeries.Base S T), B.Good → ∀ χ : HChar D.host.E, ChrEq B.mu0 χ → ∀ PP ∈ B.G.Pg, ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0) (z : (kP PP)ˣ), (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.G.muC PP z : ℂˣ) : ℂ) = ((χ.locK PP (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TypeCharUnits.muC_eq_locK | exact GlobalTheory.TypeCharUnits.muC_eq_locK | (intros; apply GlobalTheory.TypeCharUnits.muC_eq_locK <;> assumption)
