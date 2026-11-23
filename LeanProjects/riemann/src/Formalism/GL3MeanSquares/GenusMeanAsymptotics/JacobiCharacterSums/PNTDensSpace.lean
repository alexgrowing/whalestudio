import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSt

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma space_harm (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp
  · have h := harmonic_le_one_add_log x
    have e : ((harmonic x : ℚ) : ℝ) = ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [← e]; exact h

lemma floor_eq_close {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ⌊a⌋₊ = ⌊b⌋₊) : |a - b| < 1 := by
  have h1 := Nat.floor_le ha
  have h2 := Nat.lt_floor_add_one a
  have h3 := Nat.floor_le hb
  have h4 := Nat.lt_floor_add_one b
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith

lemma space_side (Q : Finset ℝ) (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (h1 : ∀ x ∈ Q, 1 ≤ f x)
    (h2 : ∀ x ∈ Q, f x ≤ 2 * T) (hsp : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → 1 ≤ |f x - f y|) :
    ∑ x ∈ Q, 1 / f x ≤ 1 + Real.log (2 * T + 1) := by
  have hinj : Set.InjOn (fun x => ⌊f x⌋₊) Q := by
    intro x hx y hy hxy
    by_contra hne
    have := floor_eq_close (by linarith [h1 x hx]) (by linarith [h1 y hy]) hxy
    have := hsp x hx y hy hne
    linarith
  have step1 : ∑ x ∈ Q, 1 / f x ≤ ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ := by
    refine sum_le_sum (fun x hx => ?_)
    have hf1 := h1 x hx
    have hfl : (1 : ℝ) ≤ (⌊f x⌋₊ : ℝ) := by
      have : 1 ≤ ⌊f x⌋₊ := Nat.le_floor (by exact_mod_cast hf1)
      exact_mod_cast this
    rw [one_div]
    exact inv_anti₀ (by linarith) (Nat.floor_le (by linarith))
  have step2 : ∑ x ∈ Q, ((⌊f x⌋₊ : ℕ) : ℝ)⁻¹ = ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ := by
    rw [sum_image hinj]
  have hsub : Q.image (fun x => ⌊f x⌋₊) ⊆ Icc 1 ⌊2 * T⌋₊ := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [mem_Icc]
    exact ⟨Nat.le_floor (by exact_mod_cast h1 x hx), Nat.floor_le_floor (h2 x hx)⟩
  have step3 : ∑ k ∈ Q.image (fun x => ⌊f x⌋₊), ((k : ℕ) : ℝ)⁻¹ ≤ ∑ k ∈ Icc 1 ⌊2 * T⌋₊, ((k : ℕ) : ℝ)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have step4 : Real.log (⌊2 * T⌋₊ : ℝ) ≤ Real.log (2 * T + 1) := by
    rcases Nat.eq_zero_or_pos ⌊2 * T⌋₊ with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) (by linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)])
  linarith [space_harm ⌊2 * T⌋₊]

theorem zero_spacing : Spacing := by
  intro P T hT hP hsp
  constructor
  · have hinj : Set.InjOn (fun x => ⌊x + T⌋₊) P := by
      intro x hx y hy hxy
      by_contra hne
      have hx' := abs_le.1 (hP x hx)
      have hy' := abs_le.1 (hP y hy)
      have := floor_eq_close (by linarith) (by linarith) hxy
      have := hsp x hx y hy hne
      rw [show x + T - (y + T) = x - y by ring] at *
      linarith
    have hsub : P.image (fun x => ⌊x + T⌋₊) ⊆ range (⌊2 * T⌋₊ + 1) := by
      intro k hk
      rw [mem_image] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      rw [mem_range, Nat.lt_succ_iff]
      exact Nat.floor_le_floor (by linarith [(abs_le.1 (hP x hx)).2])
    have h1 : P.card ≤ ⌊2 * T⌋₊ + 1 := by
      rw [← card_image_of_injOn hinj]
      exact (card_le_card hsub).trans (by simp)
    have h2 : ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * T + 1 := by
      push_cast; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * T)]
    exact (by exact_mod_cast h1 : (P.card : ℝ) ≤ ((⌊2 * T⌋₊ + 1 : ℕ) : ℝ)).trans h2
  · intro t ht
    have hsplit := sum_filter_add_sum_filter_not (P.erase t) (fun x => t < x) (fun x => 1 / |t - x|)
    rw [← hsplit]
    have hR : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => t < x), 1 / (x - t) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter] at hx
        rw [abs_sub_comm, abs_of_pos (by linarith [hx.2])]
      rw [e]
      refine space_side _ (fun x => x - t) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_pos (by linarith [hx.2])] at this
        exact this
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show x - t ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show x - t - (y - t) = x - y by ring]
    have hL : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| ≤ 1 + Real.log (2 * T + 1) := by
      have e : ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / |t - x| =
          ∑ x ∈ (P.erase t).filter (fun x => ¬ t < x), 1 / (t - x) := by
        refine sum_congr rfl (fun x hx => ?_)
        rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        rw [abs_of_pos (by linarith)]
      rw [e]
      refine space_side _ (fun x => t - x) T hT (fun x hx => ?_) (fun x hx => ?_) (fun x hx y hy hne => ?_)
      · rw [mem_filter, mem_erase] at hx
        have hlt : x < t := lt_of_le_of_ne (not_lt.1 hx.2) hx.1.1
        have := hsp x hx.1.2 t ht hx.1.1
        rw [abs_of_neg (by linarith)] at this
        show 1 ≤ t - x
        linarith
      · rw [mem_filter, mem_erase] at hx
        have a := abs_le.1 (hP x hx.1.2)
        have b := abs_le.1 (hP t ht)
        show t - x ≤ 2 * T
        linarith
      · rw [mem_filter, mem_erase] at hx hy
        have := hsp x hx.1.2 y hy.1.2 hne
        rwa [show t - x - (t - y) = -(x - y) by ring, abs_neg]
    linarith

theorem space_card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  have h : (Finset.univ : Finset (DirichletCharacter ℂ M)).card = M.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  rw [h]
  exact_mod_cast Nat.totient_le M

theorem trivial_bound : Triv := by
  intro M _ T S hT hS hsp
  classical
  have hfib : ∀ χ : DirichletCharacter ℂ M, ((S.filter (fun p => p.1 = χ)).card : ℝ) ≤ 2 * T + 1 := by
    intro χ
    set F := S.filter (fun p => p.1 = χ) with hF
    have hinj : Set.InjOn (fun p : DirichletCharacter ℂ M × ℂ => p.2.im) F := by
      intro p hp p' hp' h
      by_contra hne
      rw [hF, coe_filter] at hp hp'
      have := hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm)
      simp only at h
      rw [h, sub_self, abs_zero] at this
      linarith
    have hsp' := (zero_spacing (F.image (fun p => p.2.im)) T hT
      (fun x hx => by
        rw [mem_image] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact hS p (mem_of_mem_filter _ hp))
      (fun x hx y hy hne => by
        rw [mem_image] at hx hy
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨p', hp', rfl⟩ := hy
        have hpp : p ≠ p' := fun h => hne (by rw [h])
        rw [hF, mem_filter] at hp hp'
        exact hsp p hp.1 p' hp'.1 hpp (hp.2.trans hp'.2.symm))).1
    rwa [card_image_of_injOn hinj] at hsp'
  have hsum : (S.card : ℝ) = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)),
      ((S.filter (fun p => p.1 = χ)).card : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := fun p : DirichletCharacter ℂ M × ℂ => p.1) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast; rfl
  rw [hsum]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), ((S.filter (fun p => p.1 = χ)).card : ℝ)
      ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ M)), (2 * T + 1) := sum_le_sum (fun χ _ => hfib χ)
    _ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) * (2 * T + 1) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * (2 * T + 1) := mul_le_mul_of_nonneg_right (space_card_char_le M) (by linarith)

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
