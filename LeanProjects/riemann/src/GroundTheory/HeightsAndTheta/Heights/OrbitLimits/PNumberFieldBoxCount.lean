import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNumberFieldBoxCount
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeImageZLattice
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCovolumeRelIndex
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsEmbeddingSumPlaces
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMixedBoxCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory

namespace NumberFieldBoxCount

theorem inf_full {F : Type*} [Field F] {L B : AddSubgroup F}
    (hL : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) (hB : ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ B) :
    ∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L ⊓ B := by
  intro x
  obtain ⟨n, hn, hnx⟩ := hL x
  obtain ⟨m, hm, hmx⟩ := hB x
  refine ⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩
  · have h := L.nsmul_mem hnx m
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa using h
  · have h := B.nsmul_mem hmx n
    rw [nsmul_eq_mul, ← mul_assoc] at h
    simpa [mul_comm] using h

theorem fg_of_le {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (hK : K.FG) (hHK : H ≤ K) : H.FG := by
  obtain ⟨S, hS⟩ := hK
  have hK' : (AddSubgroup.toIntSubmodule K).FG := ⟨S, by rw [← AddSubgroup.toIntSubmodule_closure, hS]⟩
  obtain ⟨T, hT⟩ := hK'.of_le (S := AddSubgroup.toIntSubmodule H) hHK
  exact ⟨T, AddSubgroup.toIntSubmodule.injective (by rw [AddSubgroup.toIntSubmodule_closure, hT])⟩

theorem forall_le_iff {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (x : F) :
    (∀ σ : F →+* ℂ, ‖σ x‖ ≤ ρ σ) ↔ ∀ w : InfinitePlace F, normAtPlace w (mixedEmbedding F x) ≤ ρ w.embedding := by
  refine ⟨fun h w => ?_, fun h σ => ?_⟩
  · rw [normAtPlace_apply, ← norm_embedding_eq]
    exact h _
  · have h' := h (InfinitePlace.mk σ)
    rw [normAtPlace_apply, InfinitePlace.apply] at h'
    rcases embedding_mk_eq σ with e | e
    · rwa [e] at h'
    · rwa [e, hρc] at h'

theorem card_eq {F : Type*} [Field F] [NumberField F] (ρ : (F →+* ℂ) → ℝ)
    (hρc : ∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) (L : AddSubgroup F) :
    Nat.card {x : L // ∀ σ : F →+* ℂ, ‖σ (x : F)‖ ≤ ρ σ} =
      {y : mixedSpace F | y ∈ latticeImage F L ∧ ∀ w, normAtPlace w y ≤ ρ w.embedding}.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_eq_of_bijective (fun x => ⟨mixedEmbedding F x.1,
    (mem_latticeImage _ _).2 ⟨x.1, x.1.2, rfl⟩, (forall_le_iff ρ hρc _).1 x.2⟩) ⟨?_, ?_⟩
  · intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (mixedEmbedding_injective F h'))
  · rintro ⟨y, hy, hyb⟩
    obtain ⟨x, hx, rfl⟩ := (mem_latticeImage _ _).1 hy
    exact ⟨⟨⟨x, hx⟩, (forall_le_iff ρ hρc x).2 hyb⟩, rfl⟩

theorem relIndex_latticeImage {F : Type*} [Field F] [NumberField F] (H K : AddSubgroup F) :
    (latticeImage F H).toAddSubgroup.relIndex (latticeImage F K).toAddSubgroup = H.relIndex K := by
  simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding_injective F)

open scoped Classical in

theorem proof (h1 : LatticeImageZLattice.Statement) (h2 : CovolumeRelIndex.Statement)
    (h4 : EmbeddingSumPlaces.Statement) (h5 : MixedBoxCount.Statement) : NumberFieldBoxCount.Statement := by
  intro F _ _ B hB hBf
  obtain ⟨_, _⟩ := h1 F B hB hBf
  refine ⟨Module.finrank ℚ F * Real.log 2 + Real.log (ZLattice.covolume (latticeImage F B)) -
    Real.log (convexBodyLTFactor F : ℝ), ?_⟩
  intro L hL hLf ρ hρ hρc
  obtain ⟨_, _⟩ := h1 F L hL hLf
  obtain ⟨_, _⟩ := h1 F (L ⊓ B) (fg_of_le hL inf_le_left) (inf_full hLf hBf)
  have mono : ∀ {H K : AddSubgroup F}, H ≤ K → latticeImage F H ≤ latticeImage F K := by
    intro H K hHK
    refine (Submodule.toAddSubgroup_le _ _).1 ?_
    simp only [latticeImage, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.map_mono hHK
  have cL := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F L) (mono inf_le_left)
  have cB := h2 _ volume (latticeImage F (L ⊓ B)) (latticeImage F B) (mono inf_le_right)
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_left] at cL
  rw [relIndex_latticeImage, AddSubgroup.inf_relIndex_right] at cB
  have p0 := ZLattice.covolume_pos (latticeImage F (L ⊓ B)) volume
  have pL := ZLattice.covolume_pos (latticeImage F L) volume
  have pB := ZLattice.covolume_pos (latticeImage F B) volume
  have r1 : (0 : ℝ) < B.relIndex L := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have r2 : (0 : ℝ) < L.relIndex B := by
    by_contra hc; have hc' := not_lt.1 hc; nlinarith
  have hgen : genIndex L B = ZLattice.covolume (latticeImage F B) / ZLattice.covolume (latticeImage F L) := by
    rw [genIndex, div_eq_div_iff r2.ne' pL.ne']
    linarith
  obtain ⟨-, hcount⟩ := h5 F (latticeImage F L) (fun w => ρ w.embedding) (fun w => hρ _)
  have hsum := h4 F (fun σ => Real.log (ρ σ)) (fun σ => by simp only [hρc])
  rw [card_eq ρ hρc L, hsum, hgen, Real.log_div pB.ne' pL.ne']
  linarith

end NumberFieldBoxCount

end GroundTheory.Heights₂.Heights.Targets
