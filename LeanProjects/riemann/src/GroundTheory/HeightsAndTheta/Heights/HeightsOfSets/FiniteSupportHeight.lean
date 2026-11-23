import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

theorem evalCone_map {ι : Type} {n : ι → ℕ} {F F' : Type*} [CommRing F] [CommRing F'] (φ : F →+* F')
    (z : Cone n F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone (fun k i ↦ φ (z k i)) f = φ (evalCone z f) := by
  unfold evalCone
  rw [MvPolynomial.eval₂_comp_left φ]
  congr 1
  exact RingHom.ext_int _ _

theorem sigma_mem_points {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (P : ArithVariety n)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : x ∈ P.points (AlgebraicClosure ℚ))
    (σ : coordField x →+* ℂ) : (fun k i ↦ σ (coordVec x k i)) ∈ P.points ℂ := by
  refine ⟨fun k h ↦ hx.1 k ?_, fun f hf ↦ ?_⟩
  · funext i
    have h1 : σ (coordVec x k i) = 0 := congrFun h i
    have h2 : coordVec x k i = 0 := (map_eq_zero σ).mp h1
    exact congrArg Subtype.val h2
  · rw [evalCone_map σ (coordVec x) f]
    have h0 : evalCone x f = 0 := hx.2 f hf
    have h1 := evalCone_map (coordField x).val.toRingHom (coordVec x) f
    have h2 : evalCone (coordVec x) f = 0 := by
      apply (coordField x).val.toRingHom.injective
      rw [map_zero, ← h1]
      exact h0
    rw [h2, map_zero]

theorem finite_support_height {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (A : HermLine n)
    (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) :
    (Function.support fun v : FinitePlace (coordField x) ↦
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))).Finite := by
  classical
  let c : Coord n → coordField x := fun p ↦ coordVec x p.1 p.2
  have hT : (⋃ p ∈ {p | c p ≠ 0},
      Function.mulSupport fun w : FinitePlace (coordField x) ↦ w (c p)).Finite :=
    Set.Finite.biUnion (Set.toFinite _) fun p hp ↦ FinitePlace.hasFiniteMulSupport hp
  refine hT.subset fun v hv ↦ ?_
  by_contra hvT
  apply hv
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  have h1 : ∀ i, coordVec x k i ≠ 0 → v (coordVec x k i) = 1 := by
    intro i hi
    by_contra hne
    exact hvT (Set.mem_biUnion (x := (⟨k, i⟩ : Coord n)) hi hne)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp (hx k)
  have hi0' : coordVec x k i0 ≠ 0 := fun h ↦ hi0 (congrArg Subtype.val h)
  have hs : (⨆ i, v (coordVec x k i)) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_) (le_ciSup_of_le (Set.finite_range _).bddAbove i0 ?_)
    · by_cases h : coordVec x k i = 0
      · rw [h, map_zero]; exact zero_le_one
      · exact (h1 i h).le
    · exact (h1 i0 hi0').ge
  rw [hs, Real.log_one, mul_zero]

theorem heightMetricChange : HeightMetricChange.Statement := by
  intro ι _ _ n P A A' hdeg B hB x hx
  have key : height A x - height A' x =
      ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
        ∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) -
          Real.log (A'.metric fun k i ↦ σ (coordVec x k i))) := by
    unfold height
    rw [hdeg, Finset.sum_sub_distrib]
    ring
  have hpos : (0 : ℝ) < Module.finrank ℚ (coordField x) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := coordField x)
  rw [key, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  have hs : |∑ σ : coordField x →+* ℂ, (Real.log (A.metric fun k i ↦ σ (coordVec x k i)) -
      Real.log (A'.metric fun k i ↦ σ (coordVec x k i)))| ≤
      Module.finrank ℚ (coordField x) * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ B fun σ _ ↦ hB _ (sigma_mem_points P hx σ)).trans ?_
    rw [Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  calc _ ≤ ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ * (Module.finrank ℚ (coordField x) * B) :=
        mul_le_mul_of_nonneg_left hs (inv_pos.mpr hpos).le
    _ = B := by field_simp

theorem HermitianBundle.degree_bot {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K) :
    E.degree ⊥ = 0 := by
  unfold HermitianBundle.degree HermitianBundle.degreeWith
  have hc : Nat.card ((⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range
      (HermitianBundle.exists_linearIndependent_rank E ⊥).choose)) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨inferInstance, inferInstance⟩
  rw [hc]
  have hz : E.rank ⊥ = 0 := by simp [HermitianBundle.rank]
  have hg : ∀ (m : ℕ) (hm : m = 0) (σ : K →+* ℂ) (f : Fin m → E.carrier),
      ‖HermitianBundle.gramDet E σ f‖ = 1 := by
    intro m hm σ f
    subst hm
    simp [HermitianBundle.gramDet]
  simp [hg _ hz]

theorem flagDegreeBound : FlagDegreeBound.Statement := by
  intro K _ _ E r F _ _ hr i
  by_cases hi : (i : ℕ) = 0
  · have hrk : E.rank (F i) = 0 := by rw [hr i, hi]
    have hbot : F i = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := F i)).mp hrk
    have hdeg : E.normDegree (F i) = 0 := by
      rw [HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot, zero_div]
    rw [hdeg, hi]
    simp
  · have hne : F i ≠ ⊥ := by
      intro h
      apply hi
      rw [← hr i, h]
      simp [HermitianBundle.rank]
    have hle : ((E.slope (F i) : ℝ) : EReal) ≤ E.slopeMax :=
      le_iSup₂_of_le (F i) hne le_rfl
    have hipos : (0 : ℝ) < (i : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hi
    have hd : ((E.normDegree (F i) : ℝ) : EReal) =
        (((i : ℕ) : EReal)) * ((E.slope (F i) : ℝ) : EReal) := by
      have : E.normDegree (F i) = ((i : ℕ) : ℝ) * E.slope (F i) := by
        unfold HermitianBundle.slope
        rw [hr i]
        field_simp
      rw [this]
      simp
    rw [hd, ge_iff_le, EReal.neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end GroundTheory.Heights₂.Heights
