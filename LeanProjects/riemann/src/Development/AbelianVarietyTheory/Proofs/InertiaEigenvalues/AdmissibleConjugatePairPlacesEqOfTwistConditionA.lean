import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmAll

theorem admissibleConjugatePairPlaces_eq_of_twist_condition : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X),
  GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X Y hY i k Q M χ hT
  classical
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun v hv => ?_
  by_contra hna
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v
  obtain ⟨σ, hσ, hne⟩ := (hT.2.2.2.2.2.1 v A hA).2 hv
  apply hne
  have h1 : Y.delU i Q M σ = 1 := by
    apply Multiplicative.toAdd.injective
    funext w
    by_cases hw : w.1 ∈ admissibleConjugatePairPlaces X i Q M
    · rw [delU_on hY σ w hw]
      have hvp : v ∉ GalChar.pair D.host w.1 := by
        rintro (h | hc)
        · exact hna (h ▸ hw)
        · exact hna (conj_mem_admissibleConjugatePairPlaces hw hc)
      rw [(GalChar.delOf_laws D.host X.cc (X.l i) M _).2.2.2 v hvp A hA σ hσ]
      rfl
    · rw [delU_off hY (twSet_of_twOK hT) σ w hw]
      rfl
  rw [MonoidHom.comp_apply, h1, map_one]

end GlobalTheory.AdmAll
