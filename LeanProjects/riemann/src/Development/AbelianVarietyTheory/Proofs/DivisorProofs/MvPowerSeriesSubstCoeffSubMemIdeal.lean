import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderProdSubProd

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.SubstMod

theorem order_prod_sub_prod {R τ ι : Type} [CommRing R] (s : Finset ι)
    (a b : ι → MvPowerSeries τ R) (k : ι → ℕ)
    (ha : ∀ i ∈ s, (k i : ℕ∞) ≤ (a i).order) (hb : ∀ i ∈ s, (k i : ℕ∞) ≤ (b i).order)
    (hab : ∀ i ∈ s, (k i : ℕ∞) + 1 ≤ (a i - b i).order) :
    (∑ i ∈ s, (k i : ℕ∞)) + 1 ≤ (∏ i ∈ s, a i - ∏ i ∈ s, b i).order := by
  first
  | exact @_root_.GlobalTheory.OrderProductDifference.target
  | exact _root_.GlobalTheory.OrderProductDifference.target
  | (apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrderProductDifference.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrderProductDifference.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrderProductDifference.target ..)

theorem order_pow_sub_pow {R τ : Type} [CommRing R] (u l : MvPowerSeries τ R)
    (hu : constantCoeff u = 0) (hl : constantCoeff l = 0) (hul : (2 : ℕ∞) ≤ (u - l).order)
    (n : ℕ) : (n : ℕ∞) + 1 ≤ (u ^ n - l ^ n).order := by
  have := order_prod_sub_prod (Finset.range n) (fun _ => u) (fun _ => l) (fun _ => 1)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hu)
    (fun _ _ => by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hl)
    (fun _ _ => by simpa [one_add_one_eq_two] using hul)
  simpa [Finset.prod_const] using this

theorem order_monoProd_sub {R σ τ : Type} [CommRing R] (u l : σ → MvPowerSeries τ R)
    (hu : ∀ s, constantCoeff (u s) = 0) (hl : ∀ s, constantCoeff (l s) = 0)
    (hul : ∀ s, (2 : ℕ∞) ≤ (u s - l s).order) (α : σ →₀ ℕ) :
    (α.degree : ℕ∞) + 1 ≤
      ((α.prod fun s e => u s ^ e) - α.prod fun s e => l s ^ e).order := by
  have := order_prod_sub_prod α.support (fun s => u s ^ α s) (fun s => l s ^ α s) α
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hu s))
    (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hl s))
    (fun s _ => order_pow_sub_pow _ _ (hu s) (hl s) (hul s) _)
  rw [Finsupp.degree_apply]
  push_cast
  exact this

theorem subst_coeff_sub_mem : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
    (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
    (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
    ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
    ∀ (w : τ →₀ ℕ), w.degree = m →
      ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hl m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← hl s 0 (by simp), coeff_zero_eq_constantCoeff_apply,
      hu s]
  have hul : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hl s β (by omega), sub_self]
  have hU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hu s]
  have hL : HasSubst (up Q ℓ) := hasSubst_of_constantCoeff_zero fun s => by
    simp [up, hℓ s]
  rw [coeff_subst hU, coeff_subst hL,
    ← finsum_sub_distrib (coeff_subst_finite hU c w) (coeff_subst_finite hL c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r) ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add]⟩)
    fun α => ?_
  have hprod : ∀ v : σ → MvPowerSeries τ B, (α.prod fun s e => up Q v s ^ e) =
      map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    intro v
    simp only [up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have h0 : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 := by
      refine coeff_of_lt_order (lt_of_lt_of_le ?_ (order_monoProd_sub u ℓ hu hℓ hul α))
      have : w.degree ≤ α.degree := by omega
      exact_mod_cast Nat.lt_succ_of_le this
    exact ⟨0, N.zero_mem, by rw [h0, map_zero, mul_zero]⟩

end GlobalTheory.SubstMod
