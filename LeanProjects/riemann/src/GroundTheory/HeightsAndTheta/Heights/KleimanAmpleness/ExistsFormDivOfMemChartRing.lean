import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XNotMemMIdealOver
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver chartRingOver)

noncomputable section

theorem exists_form_div_of_mem_chartRing {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (e : ℕ) (f : Kleiman.Poly k N), f.IsHomogeneous e ∧ a = aeval x f / x i ^ e := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := ha
  have ht' : t ∈ Submonoid.closure {(X i : Kleiman.Poly k N)} := by
    have : ((fun l => (X l : Kleiman.Poly k N)) '' ((({i} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X i} := by simp
    rw [← this]; exact ht
  obtain ⟨p, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
  have hpe : e = p := hte.inj_right (isHomogeneous_X_pow i p) (by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
  subst hpe
  exact ⟨e, f, hf, by rw [map_pow, aeval_X]⟩

theorem exists_common_form_div {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {ι : Type} [Fintype ι] {i : Fin (N + 1)} (hi : x i ≠ 0) (a : ι → Ω)
    (ha : ∀ t, a t ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (D : ℕ) (E : ι → Kleiman.Poly k N), (∀ t, (E t).IsHomogeneous D) ∧
      ∀ t, a t = aeval x (E t) / x i ^ D := by
  classical
  choose e f hf hfa using fun t => exists_form_div_of_mem_chartRing hi (ha t)
  have hle : ∀ t, e t ≤ ∑ t, e t := fun t =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  refine ⟨∑ t, e t, fun t => f t * X i ^ (∑ t, e t - e t), fun t => ?_, fun t => ?_⟩
  · have h := (hf t).mul (isHomogeneous_X_pow i (∑ t, e t - e t))
    rwa [Nat.add_sub_cancel' (hle t)] at h
  · have hD : x i ^ (∑ t, e t) = x i ^ e t * x i ^ (∑ t, e t - e t) := by
      rw [← pow_add, Nat.add_sub_cancel' (hle t)]
    rw [hfa t, map_mul, map_pow, aeval_X, hD, mul_div_mul_right _ _ (pow_ne_zero _ hi)]

theorem mConeMapOver_rename_base {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    (x : Fin (N + 1) → Ω) {m : ℕ} (s : Fin m → Ω) {F : Kleiman.Poly k N} {D : ℕ} (hF : F.IsHomogeneous D) :
    mConeMapOver k (graphVec x s) (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) F) =
      C (aeval x F) * X baseBlock ^ D := by
  have h := congrArg (fun φ => φ F) (mConeMapOver_graph_comp_base (S := k) x s)
  simp only [AlgHom.comp_apply] at h
  rw [h, Kleiman.cone_eq, Kleiman.coneGen_of_isHomogeneous x hF]
  simp only [AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    MvPolynomial.algebraMap_eq]

theorem mConeMapOver_X' {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω] {m : ℕ}
    (y : (Σ c, graphIdx N m c) → Ω) (v : Σ c, graphIdx N m c) :
    mConeMapOver k y (X v) = C (y v) * X v.1 := by
  simp [mConeMapOver]

theorem SectionRatio.full : SectionRatio.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle j b hYj
  have hmem : ∀ P, mConeMapOver k (graphVec x s) P = 0 → P ∈ W := fun P hP => hle (RingHom.mem_ker.mpr hP)
  obtain ⟨i, hXi⟩ : ∃ i : Fin (N + 1), (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W :=
    hW.relevant baseBlock
  have hi : x i ≠ 0 := fun h0 => hXi (hmem _ (by
    rw [mConeMapOver_X', show graphVec x s ⟨baseBlock, i⟩ = 0 from h0, map_zero, zero_mul]))
  obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
  have hw' : ∀ p : Fin m × Fin m,
      x i ^ (-n) * s p.1 * w p.2 ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p => by
    rw [← chartRingOver_oneBlock x (fun _ => i) hi]; exact hw p.1 p.2
  obtain ⟨D, E, hE, hEq⟩ := exists_common_form_div hi _ hw'
  have hval : ∀ a c, aeval x (E (a, c)) = x i ^ D * (x i ^ (-n) * s a * w c) := fun a c => by
    have h := hEq (a, c)
    dsimp only at h
    rw [h]; field_simp
  obtain ⟨b0, hb0⟩ : ∃ b0, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, b0)) ∉ W := by
    by_contra h
    push Not at h
    have key : ∑ c, aeval x (E (j, c)) * s c = x i ^ D * s j := by
      simp only [hval]
      calc ∑ c, x i ^ D * (x i ^ (-n) * s j * w c) * s c
          = x i ^ D * s j * ∑ c, x i ^ (-n) * s c * w c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
        _ = x i ^ D * s j := by rw [hsum, mul_one]
    have hrel : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
          X ⟨Sum.inr (), c⟩ -
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i ^ D) *
          X ⟨Sum.inr (), j⟩ ∈ W := by
      apply hmem
      rw [map_sub, map_sum, map_mul, mConeMapOver_rename_base x s (isHomogeneous_X_pow i D), mConeMapOver_X']
      have hc : ∀ c, mConeMapOver k (graphVec x s)
          (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
            X ⟨Sum.inr (), c⟩) = C (aeval x (E (j, c)) * s c) * (X baseBlock ^ D * X (Sum.inr ())) := fun c => by
        rw [map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_X', graphVec_inr, map_mul]
        ring
      rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.sum_mul, ← map_sum, key, graphVec_inr]
      simp only [map_pow, aeval_X, map_mul]
      ring
    have hsumW : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
        X ⟨Sum.inr (), c⟩ ∈ W := W.sum_mem fun c _ => W.mul_mem_right _ (h c)
    have hXY := W.sub_mem hsumW hrel
    rw [sub_sub_cancel, map_pow, rename_X] at hXY
    rcases hW.isPrime.mem_or_mem hXY with h1 | h1
    · exact hXi (hW.isPrime.mem_of_pow_mem _ h1)
    · exact hYj h1
  refine ⟨D, E (b, b0), E (j, b0), hE _, hE _, hb0, hmem _ ?_⟩
  rw [map_sub, map_mul, map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_rename_base x s (hE _),
    mConeMapOver_X', mConeMapOver_X', graphVec_inr, graphVec_inr, hval, hval]
  dsimp only
  simp only [map_mul]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
