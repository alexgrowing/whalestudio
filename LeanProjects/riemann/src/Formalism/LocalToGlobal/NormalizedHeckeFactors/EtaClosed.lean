import Formalism.LocalToGlobal.NormalizedHeckeFactors.HostConj
import ReciprocityTheory.ReductiveGroups.LocalHeights.Imports

open Formalism.BasicNotions NumberField

namespace Formalism.L2

theorem linkEtaTw_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i) :=
  locs_cover_twists_of_hecke Fm ReciprocityTheory.ChartRestriction.L3H.heckeStd hfam

theorem linkEta_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    Formalism.MainNotions.LinkEta Fm := by
  exact linkEtaTw_closed Fm hfam

theorem etaN_eq_etaJ' {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) (HT : HeckeTied D M) {j : ℕ}
    {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    etaN T j w = D.what₂.etaJ j w :=
  etaN_eq_etaJ_of_muAt_ne T ReciprocityTheory.ChartRestriction.L3H.heckeStd HT h1 h2 hw

end Formalism.L2
