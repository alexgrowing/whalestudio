import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteFormReadingInjectiveLatticeIntegralForms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteFormReading_injective_lattice_integralForms : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)) (T : CellTie hρ D.nexp rd) (ε : KE c w →+* ℂ) (hε : Extends ρ ε), TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) →
  Function.Injective (rdE T hε) ∧ ∀ F : Amb D j, F ∈ (ρ.B (c.twI w) j (c.sd w)).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia ρ ε) ↔ ∃ y ∈ latT c w (j.1 + 1), rdE T hε y = F := by
  first | exact @GlobalTheory.PlaceExp.rdE_injective_lattice | exact GlobalTheory.PlaceExp.rdE_injective_lattice | (intros; apply GlobalTheory.PlaceExp.rdE_injective_lattice <;> assumption)
