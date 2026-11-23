import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LiftXHasSubst

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]

theorem sum_side {M : Type} [AddCommMonoid M] (s : ι → Bool) (g : ι → ι → M)
    (hg : ∀ l l', g l l' ≠ 0 → s l = true ∧ s l' = false) :
    ∑ l, ∑ l', g l l' = ∑ i, ∑ j, g ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j)) := by
  have h1 : ∀ l, ∑ l', g l l' = ∑ j, g l ((sideE s).symm (Sum.inr j)) := by
    intro l
    rw [← Equiv.sum_comp (sideE s).symm (g l), Fintype.sum_sum_type]
    have h0 : ∑ i, g l ((sideE s).symm (Sum.inl i)) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_contra hne
      have h2 := (hg _ _ hne).2
      rw [side_inl s i] at h2
      simp at h2
    rw [h0, zero_add]
  rw [Finset.sum_congr rfl (fun l _ => h1 l),
    ← Equiv.sum_comp (sideE s).symm (fun l => ∑ j, g l ((sideE s).symm (Sum.inr j))),
    Fintype.sum_sum_type]
  have h3 : ∑ j, ∑ j', g ((sideE s).symm (Sum.inr j)) ((sideE s).symm (Sum.inr j')) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun j' _ => ?_))
    by_contra hne
    have h2 := (hg _ _ hne).1
    rw [side_inr s j] at h2
    simp at h2
  rw [h3, add_zero]

abbrev kapE (s : ι → Bool) (κ : ι → ι → k) (i : Fin (Fintype.card {l // s l = true}))
    (j : Fin (Fintype.card {l // ¬ s l = true})) : k :=
  κ ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j))

theorem delta_rename (s : ι → Bool) (κ : ι → ι → k) (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false)
    (P : MvPolynomial ι k) :
    PI.WickFormula.delta (kapE s κ) (rename (sideE s) P) = rename (sideE s) (secondOrder k κ P) := by
  have hd : ∀ (x : Fin (Fintype.card {l // s l = true}) ⊕ Fin (Fintype.card {l // ¬ s l = true}))
      (Q : MvPolynomial ι k),
      pderiv x (rename (sideE s) Q) = rename (sideE s) (pderiv ((sideE s).symm x) Q) := by
    intro x Q
    conv_lhs => rw [← (sideE s).apply_symm_apply x]
    exact pderiv_rename (sideE s).injective _ _
  rw [PI.WickFormula.delta_eq_gdelta, PI.WickFormula.Gen.gdelta_apply,
    show secondOrder k κ P = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' P) from rfl]
  simp only [map_sum, map_mul, rename_C]
  rw [sum_side s _ ?_]
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [smul_eq_C_mul, hd, hd]
  · intro l l' hne
    apply hκ
    intro h0
    apply hne
    rw [h0, map_zero, zero_mul]

theorem delta_pow_rename (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false) (n : ℕ) (P : MvPolynomial ι k) :
    (PI.WickFormula.delta (kapE s κ) ^ n) (rename (sideE s) P) =
      rename (sideE s) ((secondOrder k κ)^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, delta_rename s κ hκ, Function.iterate_succ_apply']

section Van

variable {π : Type} [Fintype π] [DecidableEq π]

theorem pairMin_step (c : ι → π) (s : ι → Bool) (n : ι →₀ ℕ) (l l' : ι) (hc : c l = c l')
    (hs : s l = true) (hs' : s l' = false) :
    pairMin c s (n + Finsupp.single l 1 + Finsupp.single l' 1) = pairMin c s n + 1 := by
  have key : ∀ q : π,
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x) =
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true), n x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false), n x) +
        if c l = q then 1 else 0 := by
    intro q
    classical
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Finset.sum_ite_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hq : c l = q
    · have hq' : c l' = q := hc ▸ hq
      simp [hq, hq', hs, hs']
      try omega
    · have hq' : ¬ c l' = q := hc ▸ hq
      simp only [hq, hq', false_and, if_false]
      omega
  simp only [pairMin]
  rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem secondOrder_support (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (Q : MvPolynomial ι k) (p j : ℕ)
    (hQ : ∀ n ∈ Q.support, pairMin c s n + j ≤ p) :
    ∀ n ∈ (secondOrder k κ Q).support, pairMin c s n + (j + 1) ≤ p := by
  intro n hn
  rw [MvPolynomial.mem_support_iff] at hn
  have h1 : coeff n (secondOrder k κ Q) = ∑ l, ∑ l', κ l l' * coeff n (pderiv l (pderiv l' Q)) := by
    rw [show secondOrder k κ Q = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' Q) from rfl]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [h1] at hn
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨l', -, hl'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
  have hκ0 : κ l l' ≠ 0 := left_ne_zero_of_mul hl'
  have hc0 : coeff n (pderiv l (pderiv l' Q)) ≠ 0 := right_ne_zero_of_mul hl'
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv] at hc0
  have hQn : n + Finsupp.single l 1 + Finsupp.single l' 1 ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hc0
    rw [h0, zero_mul, zero_mul]
  obtain ⟨hcl, hsl, hsl'⟩ := hκ l l' hκ0
  have h2 := hQ _ hQn
  rw [pairMin_step c s n l l' hcl hsl hsl'] at h2
  omega

theorem secondOrder_iterate_eq_zero (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (P : MvPolynomial ι k) (e : ℕ)
    (hP : ∀ n ∈ P.support, pairMin c s n ≤ e) (j : ℕ) (hj : e < j) :
    (secondOrder k κ)^[j] P = 0 := by
  have h : ∀ t, ∀ n ∈ ((secondOrder k κ)^[t] P).support, pairMin c s n + t ≤ e := by
    intro t
    induction t with
    | zero => simpa using hP
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact secondOrder_support c s κ hκ _ e t ih
  by_contra hne
  obtain ⟨n, hn⟩ : ((secondOrder k κ)^[j] P).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hne
  have h2 := h j n hn
  omega

end Van

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
