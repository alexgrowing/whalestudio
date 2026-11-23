import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

noncomputable def pairMap {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k) :
    (Fin (n + 1) → k) →ₗ[k] k × k where
  toFun x := (a ⬝ᵥ x, b ⬝ᵥ x)
  map_add' x y := by simp [dotProduct_add]
  map_smul' c x := by simp [dotProduct_smul]

theorem pairMap_range {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) : LinearMap.range (pairMap a b) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hform : ∀ u v : k, φ (u, v) = u * φ (1, 0) + v * φ (0, 1) := by
    intro u v
    have h : ((u, v) : k × k) = u • ((1, 0) : k × k) + v • ((0, 1) : k × k) := by simp
    rw [h, map_add, map_smul, map_smul]
    simp
  have hzero : (φ (1, 0) • a + φ (0, 1) • b) = 0 := by
    apply dotProduct_eq_zero
    intro x
    have hx : φ (pairMap a b x) = 0 := hle (LinearMap.mem_range_self _ x)
    have hx' : φ (a ⬝ᵥ x, b ⬝ᵥ x) = 0 := hx
    rw [hform] at hx'
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    linear_combination hx'
  by_cases hμ : φ (0, 1) = 0
  · rw [hμ, zero_smul, add_zero] at hzero
    rcases smul_eq_zero.mp hzero with hl | h0
    · apply hφ
      ext p
      · simp [hl]
      · simp [hμ]
    · exact ha h0
  · apply hb (-(φ (0, 1))⁻¹ * φ (1, 0))
    have h1 : φ (0, 1) • b = -(φ (1, 0) • a) := eq_neg_of_add_eq_zero_right hzero
    calc b = (φ (0, 1))⁻¹ • (φ (0, 1) • b) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = (-(φ (0, 1))⁻¹ * φ (1, 0)) • a := by
        rw [h1, smul_neg, smul_smul, neg_mul, neg_smul]

theorem card_two_equations (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) :
    Fintype.card k ^ 2 * (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  have hr := pairMap_range a b ha hb
  obtain ⟨x0, hx0⟩ : ∃ x0, pairMap a b x0 = ((1, 1) : k × k) := by
    have : ((1, 1) : k × k) ∈ LinearMap.range (pairMap a b) := by rw [hr]; trivial
    exact this
  have hx1 : a ⬝ᵥ x0 = 1 := congrArg Prod.fst hx0
  have hx2 : b ⬝ᵥ x0 = 1 := congrArg Prod.snd hx0
  have hker : ∀ y, y ∈ LinearMap.ker (pairMap a b) ↔ a ⬝ᵥ y = 0 ∧ b ⬝ᵥ y = 0 := by
    intro y
    rw [LinearMap.mem_ker]
    exact Prod.ext_iff
  let e : LinearMap.ker (pairMap a b) ≃ {x : Fin (n + 1) → k // a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1} :=
    { toFun := fun y => ⟨y.1 + x0, by
        have h := (hker y.1).1 y.2
        simp [dotProduct_add, h.1, h.2, hx1, hx2]⟩
      invFun := fun x => ⟨x.1 - x0, by
        rw [hker]
        simp [dotProduct_sub, x.2.1, x.2.2, hx1, hx2]⟩
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  have hcard : (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card
      = Fintype.card k ^ Module.finrank k (LinearMap.ker (pairMap a b)) := by
    rw [← Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (pairMap a b)),
      Fintype.card_congr e, Fintype.card_subtype]
  have hrank := LinearMap.finrank_range_add_finrank_ker (pairMap a b)
  rw [hr, finrank_top] at hrank
  have h2 : Module.finrank k (k × k) = 2 := by simp
  have hV : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
  rw [h2, hV] at hrank
  rw [hcard, ← pow_add, hrank]

end GlobalTheory.CompanionTheory.GapOpCount
