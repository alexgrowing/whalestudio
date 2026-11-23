import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverMain

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

namespace Formalism.L2

theorem hostConj_eq_restrict (D : D7) :
    D.host.conj = (IsCMField.complexConj D.host.E).restrictScalars ℚ := by
  symm
  refine (D.host.toHostAx.eq_conjE_iff _).mpr ?_
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  exact (D.host.isConj_iff_galE φ _).mp
    (fun x => IsCMField.complexEmbedding_complexConj D.host.E φ x)

theorem hostConj_eq_complexConj (D : D7) :
    ∀ z : D.host.E, D.host.conj z = IsCMField.complexConj D.host.E z := by
  intro z
  rw [hostConj_eq_restrict D]
  rfl

theorem locs_cover_twists_of_hecke {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := hfam
  refine linkEtaTw_main Fm h ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT⟩ := hx x hx' i
  exact ⟨M, T, HT, hostConj_eq_complexConj (Fm.D x i)⟩

theorem link_eta_of_hecke_standard {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    Formalism.MainNotions.LinkEta Fm :=
  (linkEta_iff_tw Fm).2 (locs_cover_twists_of_hecke Fm h hfam)

theorem etaN_eq_etaJ_of_muAt_ne {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M)
    (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) (HT : HeckeTied D M) {j : ℕ}
    {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) :
    etaN T j w = D.what₂.etaJ j w :=
  etaN_eq_etaJ_main T h HT (hostConj_eq_complexConj D) h1 h2 hw

example (D : D7) (z : D.host.E) :
    letI : IsCMField D.host.E := hostCM D.host
    D.host.conj z = IsCMField.complexConj D.host.E z :=
  hostConj_eq_complexConj D z

example (K : Type) [Field K] [NumberField K] (i₁ i₂ : IsCMField K) : i₁ = i₂ := rfl

end Formalism.L2
