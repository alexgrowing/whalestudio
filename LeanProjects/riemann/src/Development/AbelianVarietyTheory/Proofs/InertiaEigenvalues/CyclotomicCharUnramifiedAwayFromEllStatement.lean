import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_unramified_away_from_ell : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  first | exact @GlobalTheory.CycUnram.main | exact GlobalTheory.CycUnram.main | (intros; apply GlobalTheory.CycUnram.main <;> assumption)
