import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverF

open Formalism.BasicNotions

namespace Formalism.L2

theorem locsCoverTw_of_plain {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) (hP : HeckeStdPlain) (HT : HeckeTied D M)
    (hex : SplitEx D) : Formalism.MainNotions.N.LocsCoverTw D :=
  locsCoverTw_of_tie T (heckeStd_of_plain T hP HT hex (genOutBad_of T))

theorem linkEtaTw_of_plain {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hP : HeckeStdPlain)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := h
  refine locsCoverTwF_of Fm ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT, hex⟩ := hx x hx' i
  exact ⟨M, T, heckeStd_of_plain T hP HT hex (genOutBad_of T)⟩

theorem linkEta_of_plain {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hP : HeckeStdPlain)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    Formalism.MainNotions.LinkEta Fm :=
  (linkEta_iff_tw Fm).2 (linkEtaTw_of_plain Fm hP h)

theorem etaN_eq_etaJ_of_plain {D : D7} {M : MtFam D} (T : NormalizedLocalCompatibility D M) (hP : HeckeStdPlain) (HT : HeckeTied D M)
    (hex : SplitEx D) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) : etaN T j w = D.what₂.etaJ j w :=
  etaN_eq_etaJ T (heckeStd_of_plain T hP HT hex (genOutBad_of T)) HT hex h1 h2 hw

end Formalism.L2
