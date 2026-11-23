import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

theorem HermitianBundle.degree_top_eq_arithDegree {K : Type*} [Field K] [NumberField K]
    (E : HermitianBundle K) : E.degree ⊤ = E.arithDegree := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E.carrier)
  let s' : Fin (Module.finrank (𝓞 K) E.carrier) → (⊤ : Submodule (𝓞 K) E.carrier) :=
    fun i ↦ ⟨s i, Submodule.mem_top⟩
  have hs' : LinearIndependent (𝓞 K) s' :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 K) E.carrier).subtype hs
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) E.carrier)) = E.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top]
  rw [E.degree_eq_of_linearIndependent ⊤ hs' hcard, HermitianBundle.arithDegree,
    arithDegree_eq E.metric hs (Fintype.card_fin _), GroundTheory.Heights₂.Heights.degreeWith]
  have hmap : (Submodule.span (𝓞 K) (Set.range s')).map
      (Submodule.topEquiv : (⊤ : Submodule (𝓞 K) E.carrier) ≃ₗ[𝓞 K] E.carrier).toLinearMap =
      Submodule.span (𝓞 K) (Set.range s) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ Submodule.topEquiv hmap).toEquiv]

theorem HermitianBundle.normDegree_le_rank_mul {K : Type} [Field K] [NumberField K]
    (E : HermitianBundle.{0} K) (G : Submodule (𝓞 K) E.carrier) (m : ℝ)
    (hm : E.slopeMax ≤ (m : EReal)) : E.normDegree G ≤ E.rank G * m := by
  by_cases hr : E.rank G = 0
  · have hbot : G = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := G)).mp hr
    rw [hr, HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot]
    simp
  · have hne : G ≠ ⊥ := by
      rintro rfl
      apply hr
      simp [HermitianBundle.rank]
    have hle : ((E.slope G : ℝ) : EReal) ≤ E.slopeMax := le_iSup₂_of_le G hne le_rfl
    have hs : E.slope G ≤ m := EReal.coe_le_coe_iff.mp (hle.trans hm)
    have hrpos : (0 : ℝ) < E.rank G := by exact_mod_cast Nat.pos_of_ne_zero hr
    have heq : E.normDegree G = E.rank G * E.slope G := by
      unfold HermitianBundle.slope
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hs hrpos.le

theorem slopeMaxExtension : SlopeMaxExtension.Statement := by
  intro K _ _ E' E E'' X
  show (⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((E.slope F : ℝ) : EReal)) ≤ _
  refine iSup₂_le fun F hF ↦ ?_
  rcases eq_or_ne (max E'.slopeMax E''.slopeMax) ⊤ with hM | hM
  · rw [hM]
    exact le_top
  have hrank := X.rank_sub_eq F
  have hpos : 0 < E.rank F := by
    rcases Nat.eq_zero_or_pos (E.rank F) with h | h
    · exact absurd ((Submodule.finrank_eq_zero (R := 𝓞 K) (S := F)).mp h) hF
    · exact h
  have hMbot : max E'.slopeMax E''.slopeMax ≠ ⊥ := by
    have : 0 < E'.rank (F.comap X.incl) ∨ 0 < E''.rank (F.map X.proj) := by omega
    rcases this with h | h
    · have hne : F.comap X.incl ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E'.slope (F.comap X.incl) : ℝ) : EReal) ≤ E'.slopeMax :=
        le_iSup₂_of_le (F.comap X.incl) hne le_rfl
      have hle := h0.trans (le_max_left _ E''.slopeMax)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
    · have hne : F.map X.proj ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E''.slope (F.map X.proj) : ℝ) : EReal) ≤ E''.slopeMax :=
        le_iSup₂_of_le (F.map X.proj) hne le_rfl
      have hle := h0.trans (le_max_right E'.slopeMax _)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
  set m := (max E'.slopeMax E''.slopeMax).toReal
  have hMm : max E'.slopeMax E''.slopeMax = (m : EReal) := (EReal.coe_toReal hM hMbot).symm
  have h1 := E'.normDegree_le_rank_mul (F.comap X.incl) m ((le_max_left _ _).trans_eq hMm)
  have h2 := E''.normDegree_le_rank_mul (F.map X.proj) m ((le_max_right _ _).trans_eq hMm)
  have hdeg := X.degree_submodule_le F
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hnd : E.normDegree F ≤ E'.normDegree (F.comap X.incl) + E''.normDegree (F.map X.proj) := by
    simp only [HermitianBundle.normDegree]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hdeg hd.le
  have hrpos : (0 : ℝ) < E.rank F := by exact_mod_cast hpos
  have hr : (E.rank F : ℝ) = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj) := by
    exact_mod_cast hrank
  have hs : E.slope F ≤ m := by
    unfold HermitianBundle.slope
    rw [div_le_iff₀ hrpos, hr]
    calc E.normDegree F ≤ E'.rank (F.comap X.incl) * m + E''.rank (F.map X.proj) * m := by linarith
      _ = m * (E'.rank (F.comap X.incl) + E''.rank (F.map X.proj)) := by ring
  rw [hMm]
  exact EReal.coe_le_coe_iff.mpr hs

end

end GroundTheory.Heights₂.Heights
