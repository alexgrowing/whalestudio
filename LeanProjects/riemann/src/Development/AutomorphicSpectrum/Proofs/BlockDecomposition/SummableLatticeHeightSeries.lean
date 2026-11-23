import Mathlib

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Filter Topology
open scoped Classical

namespace GlobalTheory.CompanionTheory.KMajSum

variable {K : Type} [Field K] [NumberField K]

lemma place_nonneg (w : InfinitePlace K) (x : K) : 0 ≤ w x := by
  rw [← w.norm_embedding_eq]
  exact norm_nonneg _

lemma infinitePlace_eq (h2 : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (v w : InfinitePlace K) : v = w := by
  have h1 := IsTotallyComplex.finrank K
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h4 := card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h5 : Fintype.card (InfinitePlace K) ≤ 1 := by omega
  exact Fintype.card_le_one_iff.1 h5 v w

lemma norm_mixedEmbedding_le {w : InfinitePlace K} (hall : ∀ v : InfinitePlace K, v = w) (x : K) :
    ‖mixedEmbedding K x‖ ≤ w x := by
  rw [norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun v _ => ?_
  rw [normAtPlace_apply, hall v]

lemma summable_integers (h2 : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (w : InfinitePlace K) {s : ℝ} (hs : 2 < s) :
    Summable fun a : 𝓞 K => ((1 + w (a : K)) ^ s)⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hfr : Module.finrank ℤ (mixedEmbedding.integerLattice K) = 2 := by
    rw [ZLattice.rank ℝ, mixedEmbedding.finrank, h2]
  have h0 := ZLattice.summable_norm_rpow (mixedEmbedding.integerLattice K) (-s)
    (by rw [hfr]; push_cast; linarith)
  have h1 : Summable fun z : mixedEmbedding.integerLattice K => ((1 + ‖z‖) ^ s)⁻¹ := by
    have hz : Summable fun z : mixedEmbedding.integerLattice K =>
        (if z = 0 then (1 : ℝ) else 0) := by
      apply summable_of_ne_finset_zero (s := {0})
      intro z hz
      have : z ≠ 0 := by simpa using hz
      simp [this]
    refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add hz)
    have hr : 0 ≤ ‖z‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hz0 : z = 0
    · subst hz0
      simp only [if_true]
      have h00 : ‖(0 : mixedEmbedding.integerLattice K)‖ = 0 := norm_zero
      rw [h00]
      simp only [add_zero, Real.one_rpow, inv_one]
      linarith [Real.rpow_nonneg (le_refl (0 : ℝ)) (-s)]
    · simp only [hz0, if_false, add_zero]
      have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      rw [Real.rpow_neg hpos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hpos s)
        (Real.rpow_le_rpow hpos.le (by linarith) hs0.le)
  let ι : 𝓞 K → mixedEmbedding.integerLattice K := fun a => ⟨mixedEmbedding K (a : K), ⟨a, rfl⟩⟩
  have hι : Function.Injective ι := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact RingOfIntegers.coe_injective (mixedEmbedding_injective K h)
  refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) (h1.comp_injective hι)
  · have := place_nonneg w (a : K)
    positivity
  · have hw := place_nonneg w (a : K)
    have hle : ‖ι a‖ ≤ w (a : K) :=
      norm_mixedEmbedding_le (fun v => infinitePlace_eq h2 hc v w) (a : K)
    have hn : 0 ≤ ‖ι a‖ := norm_nonneg _
    simp only [Function.comp]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) s)
      (Real.rpow_le_rpow (by linarith) (by linarith) hs0.le)

noncomputable def bump (w : InfinitePlace K) (M : ℕ) (x : K) : ℝ :=
  if ∃ a : 𝓞 K, (a : K) = (M : K) * x then ((1 + w x) ^ (5 / 2 : ℝ))⁻¹ else 0

lemma bump_nonneg (w : InfinitePlace K) (M : ℕ) (x : K) : 0 ≤ bump w M x := by
  have := place_nonneg w x
  unfold bump
  split_ifs <;> positivity

lemma place_div_natCast (w : InfinitePlace K) {M : ℕ} (x : K) :
    w (x / (M : K)) = w x / M := by
  rw [← w.norm_embedding_eq, ← w.norm_embedding_eq, map_div₀, norm_div, map_natCast,
    Complex.norm_natCast]

lemma summable_bump (h2 : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (w : InfinitePlace K) {M : ℕ} (hM : 0 < M) : Summable (bump w M) := by
  have hM0 : (M : K) ≠ 0 := by exact_mod_cast hM.ne'
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let g : 𝓞 K → K := fun a => (a : K) / M
  have hg : Function.Injective g := by
    intro a b hab
    exact RingOfIntegers.coe_injective ((div_left_inj' hM0).1 hab)
  refine (hg.summable_iff ?_).1 ?_
  · intro x hx
    refine if_neg ?_
    rintro ⟨a, ha⟩
    refine hx ⟨a, ?_⟩
    simp only [g]
    rw [ha, mul_div_cancel_left₀ _ hM0]
  · have hS := (summable_integers h2 hc w (s := 5 / 2) (by norm_num)).mul_left
      ((M : ℝ) ^ (5 / 2 : ℝ))
    refine Summable.of_nonneg_of_le (fun a => bump_nonneg w M _) (fun a => ?_) hS
    have hw := place_nonneg w (a : K)
    have hm : ∃ b : 𝓞 K, (b : K) = (M : K) * g a := ⟨a, by simp only [g]; field_simp⟩
    simp only [Function.comp, bump]
    rw [if_pos hm]
    simp only [g]
    rw [place_div_natCast]
    set t := w (a : K)
    have hM1 : (0 : ℝ) < M := by linarith
    have hP : 0 < 1 + t / M := by positivity
    have hQ : 0 < 1 + t := by linarith
    have hle : 1 + t ≤ M * (1 + t / M) := by
      have : (M : ℝ) * (1 + t / M) = M + t := by field_simp
      rw [this]; linarith
    have hpow : (1 + t) ^ (5 / 2 : ℝ) ≤ (M : ℝ) ^ (5 / 2 : ℝ) * (1 + t / M) ^ (5 / 2 : ℝ) := by
      rw [← Real.mul_rpow hM1.le hP.le]
      exact Real.rpow_le_rpow hQ.le hle (by norm_num)
    have hA : 0 < (1 + t / M) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hP _
    have hB : 0 < (1 + t) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hQ _
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hB]
    linarith

lemma term_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ((1 + x + y) ^ 5 * (1 + z) ^ 3)⁻¹ ≤
      ((1 + x) ^ (5 / 2 : ℝ))⁻¹ * (((1 + y) ^ (5 / 2 : ℝ))⁻¹ * ((1 + z) ^ (5 / 2 : ℝ))⁻¹) := by
  have hX : 0 < 1 + x := by linarith
  have hY : 0 < 1 + y := by linarith
  have hZ : 0 < 1 + z := by linarith
  have hS : 0 < 1 + x + y := by linarith
  have h1 : (1 + x) ^ (5 / 2 : ℝ) * (1 + y) ^ (5 / 2 : ℝ) ≤ (1 + x + y) ^ 5 := by
    rw [← Real.mul_rpow hX.le hY.le]
    have hle : (1 + x) * (1 + y) ≤ (1 + x + y) ^ 2 := by nlinarith [mul_nonneg hx hy]
    calc ((1 + x) * (1 + y)) ^ (5 / 2 : ℝ)
        ≤ ((1 + x + y) ^ 2) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (1 + x + y) ^ 5 := by
          rw [← Real.rpow_natCast (1 + x + y) 2, ← Real.rpow_mul hS.le,
            ← Real.rpow_natCast (1 + x + y) 5]
          norm_num
  have h2 : (1 + z) ^ (5 / 2 : ℝ) ≤ (1 + z) ^ 3 := by
    rw [← Real.rpow_natCast (1 + z) 3]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hA : 0 < (1 + x) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  have hB : 0 < (1 + y) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hY _
  have hC : 0 < (1 + z) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hZ _
  have key : (1 + x) ^ (5 / 2 : ℝ) * ((1 + y) ^ (5 / 2 : ℝ) * (1 + z) ^ (5 / 2 : ℝ)) ≤
      (1 + x + y) ^ 5 * (1 + z) ^ 3 := by
    rw [← mul_assoc]
    exact mul_le_mul h1 h2 hC.le (by positivity)
  rw [← mul_inv, ← mul_inv]
  exact inv_anti₀ (by positivity) key

theorem summable_lattice_majorant :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
      ∀ (w : InfinitePlace K) (M : ℕ), 0 < M →
        Summable (fun p : K × K × K =>
          if (∃ a : 𝓞 K, (a : K) = (M : K) * p.1) ∧ (∃ a : 𝓞 K, (a : K) = (M : K) * p.2.1) ∧
              (∃ a : 𝓞 K, (a : K) = (M : K) * p.2.2) then
            ((1 + w p.1 + w p.2.1) ^ 5 * (1 + w p.2.2) ^ 3)⁻¹ else (0 : ℝ)) := by
  intro K _ _ h2 hc w M hM
  have hb := summable_bump h2 hc w hM
  have hn : 0 ≤ bump w M := fun x => bump_nonneg w M x
  have hBC := hb.mul_of_nonneg hb hn hn
  have hnBC : 0 ≤ fun t : K × K => bump w M t.1 * bump w M t.2 := fun t =>
    mul_nonneg (bump_nonneg w M _) (bump_nonneg w M _)
  have hABC := hb.mul_of_nonneg hBC hn hnBC
  refine Summable.of_nonneg_of_le ?_ ?_ hABC
  · rintro ⟨x, y, z⟩
    have h1 := place_nonneg w x
    have h3 := place_nonneg w y
    have h4 := place_nonneg w z
    dsimp only
    split_ifs <;> positivity
  · rintro ⟨x, y, z⟩
    dsimp only
    split_ifs with h
    · obtain ⟨h1, h3, h4⟩ := h
      simp only [bump]
      rw [if_pos h1, if_pos h3, if_pos h4]
      exact term_le (place_nonneg w x) (place_nonneg w y) (place_nonneg w z)
    · exact mul_nonneg (bump_nonneg w M _) (mul_nonneg (bump_nonneg w M _) (bump_nonneg w M _))

end GlobalTheory.CompanionTheory.KMajSum
