import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesTranslationLatticeBoundedNorm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaces_translation_lattice_bounded_norm : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)), SplitSet Q → SuppAt (idem Q) (Vc D j) hQ → ∃ c : ℕ, (∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) ∧ ∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ)), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h) := by
  first | exact @GlobalTheory.LatCmpQ.latAt_translate_bounded | exact GlobalTheory.LatCmpQ.latAt_translate_bounded | (intros; apply GlobalTheory.LatCmpQ.latAt_translate_bounded <;> assumption)
