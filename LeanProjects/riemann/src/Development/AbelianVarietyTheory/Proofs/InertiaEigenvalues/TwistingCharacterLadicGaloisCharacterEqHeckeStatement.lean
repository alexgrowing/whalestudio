import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHecke
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingCharacter_ladicGaloisCharacter_eq_hecke : ∀ (D : D7) (a : Recip D D.nd.Om) (i : D.ntw.Tw) (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ) (χ : Formalism.L2.Host.HChar D.host.E) (r : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ) (b : Bool), a.Good → IsOpen (r.ker : Set (G D.host.E D.nd.Om)) → GlobalTheory.GalChar.IsGal a.art κ ι χ (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r) → ∀ (f : D.ntw.O0 i →+* ℂ), (∀ y, IsIntegral ℤ y → f y = ι (κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y))) → ∀ (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)), ChrEq (twistOf a f ch Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r)).chi χ := by
  first | exact @GlobalTheory.SeriesTie.charOf_psiAt_chrEq | exact GlobalTheory.SeriesTie.charOf_psiAt_chrEq | (intros; apply GlobalTheory.SeriesTie.charOf_psiAt_chrEq <;> assumption)
