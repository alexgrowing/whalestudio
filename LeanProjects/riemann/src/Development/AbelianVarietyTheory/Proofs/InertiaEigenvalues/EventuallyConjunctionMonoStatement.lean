import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_conjunction_mono : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (EvO A M C tup P₁ → EvO A M C tup P₂ → EvO A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → EvO A M C tup P₁ → EvO A M C tup P₂) ∧ (BuiltEx A M C tup → EvO A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ Built A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → Built A M C tup big' L → Built A M C tup big L := by
  first | exact @GlobalTheory.CoefDuty.LargeRing.evO_laws | exact GlobalTheory.CoefDuty.LargeRing.evO_laws | (intros; apply GlobalTheory.CoefDuty.LargeRing.evO_laws <;> assumption)
