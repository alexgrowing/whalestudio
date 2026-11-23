import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue

open Formalism.BasicNotions

namespace Formalism.L2

def LocsCoverTwF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i)

theorem linkEta_iff_tw {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.LinkEta Fm ↔ LocsCoverTwF Fm := by
  rw [Formalism.MainNotions.N.linkEta_iff]
  exact Iff.rfl

theorem locsCoverTwF_of {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M), HeckeStdTw T.B) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨M, T, hT⟩ := hx0 x hx i
  exact locsCoverTw_of_tie T hT

end Formalism.L2
