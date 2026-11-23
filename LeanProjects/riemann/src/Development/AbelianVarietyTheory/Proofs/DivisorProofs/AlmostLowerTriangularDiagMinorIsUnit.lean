import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.AlmostLowUnits

theorem det_almost {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (a b : Fin n)
    (hb : (b : ℕ) = a + 1) (hab : A a b ≠ 0)
    (hl : ∀ i j : Fin n, i < j → ¬ (i = a ∧ j = b) → A i j = 0) :
    A.det = (A a a * A b b - A a b * A b a) * ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
  have hne : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_iff_val_lt_val]; omega
  set c := A a a / A a b with hc
  set U := A.updateCol a (fun k => A k a + (-c) • A k b) with hU
  set N := U.submatrix id (Equiv.swap a b) with hN
  have hdetU : U.det = A.det := Matrix.det_updateCol_add_smul_self A hne (-c)
  have hdetN : N.det = - A.det := by
    rw [hN, Matrix.det_permute', Equiv.Perm.sign_swap hne, hdetU]; simp
  have hUapp : ∀ i j, U i j = if j = a then A i a - c * A i b else A i j := by
    intro i j
    rw [hU, Matrix.updateCol_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  have hNapp : ∀ i j, N i j = U i (Equiv.swap a b j) := fun _ _ => rfl
  have htri : N.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    rw [hNapp]
    by_cases hja : j = a
    · rw [hja, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
      rw [hja] at hij'
      exact hl i b (lt_trans hij' hlt) (fun h => (ne_of_lt hij') h.1)
    · by_cases hjb : j = b
      · rw [hjb, Equiv.swap_apply_right, hUapp, if_pos rfl]
        rw [hjb] at hij'
        by_cases hia : i = a
        · rw [hia, hc, div_mul_cancel₀ _ hab, sub_self]
        · have hia' : i < a := by
            have h1 : (i : ℕ) < b := hij'
            have h2 : (i : ℕ) ≠ a := fun h => hia (Fin.ext h)
            rw [Fin.lt_iff_val_lt_val]; omega
          rw [hl i a hia' (fun h => hia h.1), hl i b (lt_trans hia' hlt) (fun h => hia h.1)]; ring
      · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, hUapp, if_neg hja]
        exact hl i j hij' (fun h => hjb h.2)
  have hprod := Matrix.det_of_lowerTriangular N htri
  have hmb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ hmb] at hprod
  have hNa : N a a = A a b := by rw [hNapp, Equiv.swap_apply_left, hUapp, if_neg hne.symm]
  have hNb : N b b = A b a - c * A b b := by rw [hNapp, Equiv.swap_apply_right, hUapp, if_pos rfl]
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, N i i = ∏ i ∈ (Finset.univ.erase a).erase b, A i i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hib := (Finset.mem_erase.1 hi).1
    have hia := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    rw [hNapp, Equiv.swap_apply_of_ne_of_ne hia hib, hUapp, if_neg hia]
  rw [hNa, hNb, hrest, hdetN] at hprod
  have e : A a b * (A b a - c * A b b) = A a b * A b a - A a a * A b b := by
    rw [hc]; field_simp
  rw [← mul_assoc, e] at hprod
  linear_combination (-1 : K) * hprod

theorem units_of_det {K α : Type} [Field K] [DecidableEq α] (O : Subring K) {s : Finset α} (x : α → K) (y d : K)
    (hd : d = y * ∏ i ∈ s, x i) (hd0 : d ≠ 0) (hdi : d⁻¹ ∈ O) (hy : y ∈ O) (hx : ∀ i ∈ s, x i ∈ O) :
    (y ≠ 0 ∧ y⁻¹ ∈ O) ∧ ∀ i ∈ s, x i ≠ 0 ∧ (x i)⁻¹ ∈ O := by
  have hP : ∏ i ∈ s, x i ∈ O := O.prod_mem hx
  rw [hd] at hd0
  refine ⟨⟨left_ne_zero_of_mul hd0, ?_⟩, fun i hi => ?_⟩
  · have e : y⁻¹ = d⁻¹ * ∏ i ∈ s, x i := by
      rw [hd, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul hd0), mul_one]
    rw [e]; exact O.mul_mem hdi hP
  · have e : d = x i * (y * ∏ j ∈ s.erase i, x j) := by
      rw [hd, ← Finset.mul_prod_erase s x hi]; ring
    have h0 : x i * (y * ∏ j ∈ s.erase i, x j) ≠ 0 := by rw [← e, hd]; exact hd0
    refine ⟨left_ne_zero_of_mul h0, ?_⟩
    have e' : (x i)⁻¹ = d⁻¹ * (y * ∏ j ∈ s.erase i, x j) := by
      rw [e, mul_inv, mul_assoc, inv_mul_cancel₀ (right_ne_zero_of_mul h0), mul_one]
    rw [e']
    exact O.mul_mem hdi (O.mul_mem hy (O.prod_mem fun j hj => hx j (Finset.mem_of_mem_erase hj)))

end GlobalTheory.FlagPush.AlmostLowUnits

open GlobalTheory.FlagPush.AlmostLowUnits in

theorem GlobalTheory.FlagPush.almostLow_units : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (K : Type) [Field K] (O : Subring K) (g : Mat m K), AlmostLow τ a b g → Par 0 O g →
    (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → g x.1 x.2 x.2 ≠ 0 ∧ (g x.1 x.2 x.2)⁻¹ ∈ O) ∧
      minor τ a b g ≠ 0 ∧ (minor τ a b g)⁻¹ ∈ O := by
  intro ι m τ a b hb K _ O g hg hp
  have hlτ : ∀ i j : Fin (m τ), i < j → ¬ (i = a ∧ j = b) → g τ i j = 0 := fun i j hij h =>
    hg.2.2 τ i j hij (fun h' => h ⟨eq_of_heq (Sigma.mk.inj h'.1).2, eq_of_heq (Sigma.mk.inj h'.2).2⟩)
  have hdetτ := det_almost (g τ) a b hb hg.2.1 hlτ
  have hmO : minor τ a b g ∈ O :=
    O.sub_mem (O.mul_mem ((hp τ).1 a a) ((hp τ).1 b b)) (O.mul_mem ((hp τ).1 a b) ((hp τ).1 b a))
  have hτ := units_of_det O (fun i => g τ i i) (minor τ a b g) ((g τ).det) hdetτ (hp τ).2.1 (hp τ).2.2.1 hmO
    (fun i _ => (hp τ).1 i i)
  refine ⟨?_, hτ.1⟩
  rintro ⟨σ, i⟩ h1 h2
  by_cases hσ : σ = τ
  · subst hσ
    have hia : i ≠ a := fun e => h1 (by rw [e])
    have hib : i ≠ b := fun e => h2 (by rw [e])
    exact hτ.2 i (Finset.mem_erase.2 ⟨hib, Finset.mem_erase.2 ⟨hia, Finset.mem_univ _⟩⟩)
  · have htri : (g σ).BlockTriangular OrderDual.toDual := fun i j hij =>
      hg.2.2 σ i j (OrderDual.toDual_lt_toDual.1 hij) (fun h' => hσ (congrArg Sigma.fst h'.1))
    have hdet := Matrix.det_of_lowerTriangular (g σ) htri
    have h := units_of_det O (s := Finset.univ) (fun j => g σ j j) 1 ((g σ).det) (by rw [one_mul]; exact hdet)
      (hp σ).2.1 (hp σ).2.2.1 O.one_mem (fun j _ => (hp σ).1 j j)
    exact h.2 i (Finset.mem_univ _)
