import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.DataRows

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness

open Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem eachRowHasThetaLift_iff :
    EachRowHasThetaLift N A ↔
      ∀ (i : N.Loc) (σ : what₂.FT), (∃ f ∈ what₂.isot (N.j i) σ, f ≠ 0) → ∃ P : A.AV i,
        (∃ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ≠ 0) ∧
        ∀ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ∈ A.typeV i P := by
  unfold EachRowHasThetaLift thetaOf
  refine forall_congr' fun i => forall_congr' fun σ => ?_
  rw [Submodule.ne_bot_iff]
  refine imp_congr_right fun _ => exists_congr fun P => and_congr ?_ ?_
  · rw [Submodule.ne_bot_iff]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, h⟩
      exact ⟨f, hf, h⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨_, ⟨f, hf, rfl⟩, h⟩
  · rw [Submodule.map_le_iff_le_comap]
    rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness
