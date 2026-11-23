import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver mConeMapOver)

theorem ne_zero_of_mIdealOver_le {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω Ω' : Type} [Field Ω]
    [Field Ω'] [Algebra S Ω] [Algebra S Ω'] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → Ω'}
    (h : mIdealOver S y ≤ mIdealOver S y') (p : Σ k, ι k) (hp : y' p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hmem : (X p : MvPolynomial (Σ k, ι k) S) ∈ mIdealOver S y := by
    simp [mIdealOver, RingHom.mem_ker, mConeMapOver, h0]
  have h' := h hmem
  simpa [mIdealOver, RingHom.mem_ker, mConeMapOver] using h'

theorem mem_chartRing_blockVec_iff {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra S Ω] (z : (Σ k, ι k) → Ω) (k₀ : K) (j : ι k₀) (u : Ω) :
    u ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k₀)) (fun _ => j) ↔
      ∃ P : MvPolynomial (Σ _ : Unit, ι k₀) S,
        aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, j⟩) P = u := by
  unfold chartRingOver
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]
  rfl

theorem aeval_rename_blockRatio {S : Type} [CommRing S] {K : Type} {ι : K → Type} {L : Type} [Field L]
    [Algebra S L] (z : (Σ k, ι k) → L) (k₀ : K) (c : ∀ k, ι k) (P : MvPolynomial (Σ _ : Unit, ι k₀) S) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩)
        (rename (fun v : (Σ _ : Unit, ι k₀) => (⟨k₀, v.2⟩ : Σ k, ι k)) P) =
      aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, c k₀⟩) P := by
  rw [aeval_rename]
  rfl

theorem BlockGenTransfer.proof (hk : ChartKernel.Statement) : BlockGenTransfer.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ hB Ω' _ _ y' hne hle j hj k
  have hy := ne_zero_of_mIdealOver_le hle
  obtain ⟨c, hck₀, hc⟩ : ∃ c : ∀ k, ι k, c k₀ = j ∧ ∀ k, y' ⟨k, c k⟩ ≠ 0 := by
    choose c₀ hc₀ using hne
    refine ⟨Function.update c₀ k₀ j, Function.update_self _ _ _, fun k' => ?_⟩
    by_cases h : k' = k₀
    · cases h
      rw [Function.update_self]
      exact hj
    · rw [Function.update_of_ne h]
      exact hc₀ k'
  have hb₀ : y ⟨k, c k⟩ ≠ 0 := hy _ (hc k)
  obtain ⟨w, hw, hsum⟩ := hB j (hy _ hj) k
  choose P hP using fun a b => (mem_chartRing_blockVec_iff y k₀ j _).1 (hw a b)
  let φ : (Σ _ : Unit, ι k₀) → (Σ k, ι k) := fun v => ⟨k₀, v.2⟩
  have hR1 : ∀ a b, aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (X ⟨k, a⟩ * rename φ (P (c k) b) - rename φ (P a b)) = 0 := by
    intro a b
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    field_simp
    ring
  have hR2 : aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (∑ b, X ⟨k, b⟩ * rename φ (P (c k) b) - 1) = 0 := by
    simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    rw [sub_eq_zero, ← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  refine ⟨fun b => aeval (fun v : (Σ _ : Unit, ι k₀) => y' ⟨k₀, v.2⟩ / y' ⟨k₀, j⟩) (P (c k) b) / y' ⟨k, c k⟩,
    fun a b => ?_, ?_⟩
  · have h1 := hk S K ι Ω y Ω' y' hle c hc _ (hR1 a b)
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, sub_eq_zero] at h1
    rw [mem_chartRing_blockVec_iff]
    refine ⟨P a b, ?_⟩
    rw [← h1]
    ring
  · have h2 := hk S K ι Ω y Ω' y' hle c hc _ hR2
    simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀,
      sub_eq_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
