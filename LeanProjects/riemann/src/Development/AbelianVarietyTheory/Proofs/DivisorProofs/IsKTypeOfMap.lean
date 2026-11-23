import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra

namespace GlobalTheory.KTypeUnderMaps

open Formalism.MainNotions.S

theorem isKTypeOf_map {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H} {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) (L : H →ₗ[ℂ] H)
    (hL : ∀ k ∈ Formalism.REAL.Kset ε, ∀ (w : H), σ k (L w) = L (σ k w))
    {v : H} (hv : v ∈ S) (hLv : L v ≠ 0) :
    Formalism.MainNotions.S.IsKTypeOf ε σ Λ (Submodule.map L S) := by
  obtain ⟨hfd, hst, hirr, ⟨u, huS, hu0, huw⟩, hdom⟩ := hS
  have hpull : ∀ T : Submodule ℂ H, IsKStableOn ε σ T →
      S ⊓ T.comap L = ⊥ ∨ S ⊓ T.comap L = S := by
    intro T hT
    refine hirr _ inf_le_left ?_
    intro g hg x hx
    refine ⟨hst g hg x hx.1, ?_⟩
    have h2 : L x ∈ T := hx.2
    change L (σ g x) ∈ T
    rw [← hL g hg]
    exact hT g hg _ h2
  have hinj : ∀ x ∈ S, L x = 0 → x = 0 := by
    intro x hx hx0
    have hbot : IsKStableOn ε σ (⊥ : Submodule ℂ H) := by
      intro g _ y hy
      rw [Submodule.mem_bot] at hy ⊢
      rw [hy, map_zero]
    rcases hpull ⊥ hbot with h | h
    · have : x ∈ S ⊓ (⊥ : Submodule ℂ H).comap L := ⟨hx, by simpa using hx0⟩
      rw [h] at this
      simpa using this
    · have : v ∈ S ⊓ (⊥ : Submodule ℂ H).comap L := by rw [h]; exact hv
      exact absurd (by simpa using this.2) hLv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := hfd
    infer_instance
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst g hg x hx, (hL g hg x).symm⟩
  · intro T hTle hT
    rcases hpull T hT with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hTle hy
      have : x ∈ S ⊓ T.comap L := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hTle ?_
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ S ⊓ T.comap L := by rw [h]; exact hx
      exact this.2
  · refine ⟨L u, ⟨u, huS, rfl⟩, fun h => hu0 (hinj u huS h), ?_⟩
    intro θ hθ
    rw [hL _ hθ, huw θ hθ, map_smul]
  · rintro μ _ ⟨x, hx, rfl⟩ hx0 hw
    refine hdom μ x hx (fun h => hx0 (by rw [h, map_zero])) ?_
    intro θ hθ
    rw [← sub_eq_zero]
    refine hinj _ (S.sub_mem (hst _ hθ x hx) (S.smul_mem _ hx)) ?_
    rw [map_sub, map_smul, ← hL _ hθ, hw θ hθ, sub_self]

end GlobalTheory.KTypeUnderMaps
