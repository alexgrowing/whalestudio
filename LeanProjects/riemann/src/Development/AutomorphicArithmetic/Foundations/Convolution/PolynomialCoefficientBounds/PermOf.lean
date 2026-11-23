import Mathlib

open MvPolynomial Filter Topology

private theorem UpperTheory.ConvolutionTheory.FX.eval_esymm_eq {n : ℕ} (x : Fin n → ℂ) (k : ℕ) :
    eval x (esymm (Fin n) ℂ k) = (Finset.univ.val.map x).esymm k := by
  have := MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℂ k x
  rw [← this]
  rfl

private theorem UpperTheory.ConvolutionTheory.FX.perm_of_multiset {n : ℕ} (x y : Fin n → ℂ)
    (h : Finset.univ.val.map x = Finset.univ.val.map y) :
    ∃ w : Equiv.Perm (Fin n), y = x ∘ w := by
  classical
  have hc : ∀ c : ℂ, Fintype.card {i // y i = c} = Fintype.card {i // x i = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have e1 : ∀ z : Fin n → ℂ, (Finset.univ.filter (fun i => z i = c)).card
        = (Multiset.filter (fun a => c = z a) Finset.univ.val).card := by
      intro z
      simp only [Finset.card, Finset.filter_val, eq_comm]
    rw [e1, e1, h1]
  let e : ∀ c : ℂ, {i // y i = c} ≃ {i // x i = c} := fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map e i).symm

theorem UpperTheory.ConvolutionTheory.FX.perm_of_esymm :
    ∀ (n : ℕ) (x y : Fin n → ℂ), (∀ i : Fin n, eval x (esymm (Fin n) ℂ (i + 1)) = eval y (esymm (Fin n) ℂ (i + 1))) ↔ ∃ w : Equiv.Perm (Fin n), y = x ∘ w := by
  intro n x y
  constructor
  · intro h
    apply UpperTheory.ConvolutionTheory.FX.perm_of_multiset
    set s := Finset.univ.val.map x with hs
    set t := Finset.univ.val.map y with ht
    have hsc : s.card = n := by simp [hs]
    have htc : t.card = n := by simp [ht]
    have he : ∀ k, k ≤ n → s.esymm k = t.esymm k := by
      intro k hk
      rcases k with _ | k
      · simp [Multiset.esymm]
      · have := h ⟨k, hk⟩
        rw [UpperTheory.ConvolutionTheory.FX.eval_esymm_eq, UpperTheory.ConvolutionTheory.FX.eval_esymm_eq] at this
        exact this
    have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod
        = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
      rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hsc, htc]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [he j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    have := congrArg Polynomial.roots hp
    rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this
  · rintro ⟨w, rfl⟩ i
    rw [UpperTheory.ConvolutionTheory.FX.eval_esymm_eq, UpperTheory.ConvolutionTheory.FX.eval_esymm_eq]
    congr 1
    rw [← Multiset.map_map]
    congr 1
    exact (Multiset.map_univ_val_equiv w).symm
