import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace PositivityTheory.Resplug.ResolutionBlowup

def TopRes : Prop := FunctorialResolution.FunctorialResolutionCharZero.{0}

theorem blowup_top_of_iso {X Y : Scheme.{0}} (e : Y ≅ X) :
    ReciprocityTheory.AnForm.R.FinalTheorems.Blowup e.hom (⊤ : X.IdealSheafData) := by
  refine ⟨?_, fun W g _ => ⟨g ≫ e.inv, by simp, fun h hh => by rw [← hh]; simp⟩⟩
  rw [Scheme.IdealSheafData.comap_top]
  intro y
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  exact ⟨⟨U, hU⟩, 1, hyU, one_mem _, by simp⟩

theorem structMap_zero {X : Scheme.{0}} (s : FunctorialResolution.BlowupSequence X) :
    s.structMap 0 = s.isoZero.hom := by
  simp [FunctorialResolution.BlowupSequence.structMap, FunctorialResolution.BlowupSequence.down]

theorem isBlowupSeq_structMap {X : Scheme.{0}} (s : FunctorialResolution.BlowupSequence X) :
    ∀ i, i ≤ s.length → GlobalTheory.CompanionTheory.Hypotheses₂.Resolution.IsBlowupSeq (s.structMap i)
  | 0, _ => by
      rw [structMap_zero]
      exact GlobalTheory.CompanionTheory.Hypotheses₂.Resolution.IsBlowupSeq.single ⊤ _ (blowup_top_of_iso _)
  | i + 1, hi => by
      have hlt : i < s.length := hi
      rw [← s.structMap_down (Nat.le_succ i)]
      exact GlobalTheory.CompanionTheory.Hypotheses₂.Resolution.IsBlowupSeq.step (s.center i) (s.down (Nat.le_succ i))
        (isBlowupSeq_structMap s i hlt.le) (s.isBlowup i hlt)

theorem isBlowupSeq_topMap {X : Scheme.{0}} (s : FunctorialResolution.BlowupSequence X) :
    GlobalTheory.CompanionTheory.Hypotheses₂.Resolution.IsBlowupSeq s.topMap :=
  isBlowupSeq_structMap s s.length le_rfl

theorem resolutionCharZero_of_top (h : TopRes) : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero := by
  obtain ⟨R, hR, -, -⟩ := h
  intro k _ _ X g _ hqc _ hred
  have := hqc
  have := hred
  obtain ⟨h1, -, h3, -, -, h6⟩ := hR k X g
  exact ⟨_, (R k X g).topMap, isBlowupSeq_topMap _, h1, h3, h6⟩

end PositivityTheory.Resplug.ResolutionBlowup
