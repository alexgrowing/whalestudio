import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGood
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ → (ρ.tw i b k Q ψ).Good ∧ (ρ.B i j b).admitted (ρ.tw i b k Q ψ).Q ∧ ∀ x, ∃ u : (X.Ok i k)ˣ, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k u := by
  first | exact @GlobalTheory.TwistGood.tw_good | exact GlobalTheory.TwistGood.tw_good | (intros; apply GlobalTheory.TwistGood.tw_good <;> assumption)
