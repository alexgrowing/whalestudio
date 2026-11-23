import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section IntCone

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem intCone_evalZ_sum {n : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (h : φ.LinearOn β) (a : Fin n → ℕ) :
    φ.evalZ (∑ i, a i • β i) = ∑ i, (a i : ℝ) * φ.evalZ (β i) := by
  have := h (fun i => (a i : ℝ)) (fun i => Nat.cast_nonneg _)
  refine Eq.trans ?_ this
  unfold InvFun.evalZ
  congr 1
  funext x y
  simp [LinearMap.sum_apply]

theorem intCone_absorb {n s : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) (hβl : φ.LinearOn β) {δ : Fin s → LinearMap.BilinForm ℤ X} (hδ : IsCone bar φ δ)
    (a : Fin n → ℕ) (b : Fin s → ℕ) (h : ∑ i, a i • β i = ∑ l, b l • δ l) (i : Fin n) (hi : 0 < a i) :
    ∃ (k : ℕ) (e : Fin s → ℕ), 0 < k ∧ k • β i = ∑ l, e l • δ l := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict
  refine h3 (β i) (hβ i) (hβp i) ?_
  have hx1 : (ℓ (∑ i, a i • β i) : ℝ) = N * ∑ i, (a i : ℝ) * φ.evalZ (β i) := by
    rw [← intCone_evalZ_sum hβl, h, intCone_evalZ_sum hδ.linear, map_sum, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, h1]
    ring
  have hx2 : (ℓ (∑ i, a i • β i) : ℝ) = ∑ i, (a i : ℝ) * ℓ (β i) := by
    simp [map_sum, map_nsmul]
  have hle : ∀ j, (a j : ℝ) * (N * φ.evalZ (β j)) ≤ (a j : ℝ) * ℓ (β j) := fun j =>
    mul_le_mul_of_nonneg_left (h2 _ (hβ j) (hβp j)) (Nat.cast_nonneg _)
  have hsum : ∑ j, ((a j : ℝ) * ℓ (β j) - (a j : ℝ) * (N * φ.evalZ (β j))) = 0 := by
    rw [Finset.sum_sub_distrib, ← hx2, hx1, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hle j))).1 hsum i (Finset.mem_univ _)
  have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have h4 : (a i : ℝ) * (ℓ (β i) - N * φ.evalZ (β i)) = 0 := by rw [mul_sub]; exact ht
  have h5 := (mul_eq_zero.1 h4).resolve_left hai
  linarith

theorem intCone_face : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X], IsPolFanOn bar φ X → ∀ (r r' : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (γ' : Fin r' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCone bar φ γ' → ∀ (c : Fin r → ℕ) (c' : Fin r' → ℕ),
    (∀ j, 0 < c j) → ∑ j, c j • γ j = ∑ j, c' j • γ' j → ∀ j, ∃ j', γ j = γ' j' := by
  intro O _ bar φ X _ _ _ _ r r' γ γ' hγ hγ' c c' hc he j
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hγ.mem hγ.nonneg hγ.linear hγ' c c' he j (hc j)
  have hd' : ∑ i, d i • γ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • γ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • γ' i = ∑ l, e l • γ l :=
    fun i hi => intCone_absorb hγ'.mem hγ'.nonneg hγ'.linear hγ d _ hd' i hi
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨g, hg⟩ := hγ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨γ' i, hγ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0
    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • γ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hγ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG
    rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE
    rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← mul_assoc, ← h2, mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

end IntCone

end GlobalTheory.Poinc
