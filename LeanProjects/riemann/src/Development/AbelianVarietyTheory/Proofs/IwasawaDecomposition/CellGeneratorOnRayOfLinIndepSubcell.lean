import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace CellRay

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m' : ℕ}

theorem inCell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

end CellRay

end GlobalTheory.PolFan

open GlobalTheory.PolFan.CellRay in

theorem GlobalTheory.PolFan.cell_gen_on_ray : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X)
    (c : Fin n → ℝ), IsCell bar φ δ → IsCell bar φ γ → LinearIndependent ℤ δ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) → ∀ i, ∃ (j : Fin n) (a b : ℕ), 0 < a ∧ 0 < b ∧ a • δ i = b • γ j := by
  intro O _ bar φ X _ _ _ m n δ γ c hδ hγ hli hc hrel i
  classical

  obtain ⟨k, d, hk, hkd⟩ := inCell hγ hδ.mem hδ.nonneg (a := fun _ => (1 : ℝ)) (b := c) (fun _ => zero_le_one) hc
    ((linearOn_iff φ δ).1 hδ.linear (fun _ => 1) fun _ => zero_le_one) (by simpa using hrel) i one_ne_zero

  have hB : ∀ j, ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ (d j ≠ 0 → kj • γ j = ∑ l, e l • δ l) := by
    intro j
    by_cases hd : d j = 0
    · exact ⟨1, 0, one_pos, fun h => absurd hd h⟩
    obtain ⟨kj, e, hkj, he⟩ := inCell (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hδ hγ.mem hγ.nonneg
      (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
      ((linearOn_iff φ γ).1 hγ.linear _ fun j => Nat.cast_nonneg _) (by
        refine LinearMap.ext₂ fun a b => ?_
        have := LinearMap.congr_fun₂ hkd a b
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
        simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
        exact_mod_cast this.symm) j (by exact_mod_cast hd)
    exact ⟨kj, e, hkj, fun _ => he⟩
  choose kk e hkk he using hB
  set K := ∏ j, kk j with hKdef
  let Kj : Fin n → ℕ := fun j => ∏ j' ∈ Finset.univ.erase j, kk j'
  have hK : ∀ j, kk j * Kj j = K := fun j => Finset.mul_prod_erase Finset.univ kk (Finset.mem_univ j)
  have hKpos : 0 < K := Finset.prod_pos fun j _ => hkk j
  have hKj : ∀ j, Kj j ≠ 0 := fun j h => by
    have := hK j
    rw [h, mul_zero] at this
    omega
  have hterm : ∀ j, (K * d j) • γ j = ∑ l, (d j * Kj j * e j l) • δ l := by
    intro j
    by_cases hd : d j = 0
    · simp [hd]
    rw [← hK j, show kk j * Kj j * d j = (d j * Kj j) * kk j by ring, ← smul_smul, he j hd, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
  have key : (K * k) • δ i = ∑ l, (∑ j, d j * Kj j * e j l) • δ l := by
    rw [← smul_smul, hkd, Finset.smul_sum]
    simp only [smul_smul, hterm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
  have hFG := Fintype.linearIndependent_iffₛ.1 hli (fun l => ((∑ j, d j * Kj j * e j l : ℕ) : ℤ))
    (fun l => if l = i then ((K * k : ℕ) : ℤ) else 0) (by
      simp only [Nat.cast_smul_eq_nsmul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact key.symm)
  have hoff : ∀ l, l ≠ i → ∀ j, d j * Kj j * e j l = 0 := by
    intro l hl j
    have := hFG l
    simp only [if_neg hl, Nat.cast_eq_zero] at this
    exact (Finset.sum_eq_zero_iff.1 this) j (Finset.mem_univ _)
  have hon : ∑ j, d j * Kj j * e j i ≠ 0 := by
    have := hFG i
    rw [if_pos rfl, Nat.cast_inj] at this
    rw [this]
    exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hon
  have hdj : d j ≠ 0 := fun h => hj (by rw [h]; ring)
  have hej : e j i ≠ 0 := fun h => hj (by rw [h]; ring)
  have hel : ∀ l, l ≠ i → e j l = 0 := fun l hl => by
    have := hoff l hl j
    rcases Nat.mul_eq_zero.1 this with h | h
    · rcases Nat.mul_eq_zero.1 h with h' | h'
      · exact absurd h' hdj
      · exact absurd h' (hKj j)
    · exact h
  have hγj : kk j • γ j = e j i • δ i := by
    rw [he j hdj, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  exact ⟨j, e j i, kk j, Nat.pos_of_ne_zero hej, hkk j, hγj.symm⟩
