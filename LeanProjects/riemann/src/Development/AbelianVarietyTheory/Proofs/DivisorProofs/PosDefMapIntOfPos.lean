import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamilyStatement

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem posDef_map_int_of_pos {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ) (hs : L.IsSymm)
    (hp : ∀ ξ : Fin n → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ)) : (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  set M := L.map (Int.cast : ℤ → ℝ) with hM
  have hH : M.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [M, hs.apply]
  have hdet : L.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hLv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := hp v hv
    rw [hLv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hint : ∀ z : Fin n → ℤ, (fun i => (z i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (z i : ℝ)) = ((z ⬝ᵥ (L *ᵥ z) : ℤ) : ℝ) := by
    intro z
    simp [M, dotProduct, mulVec]
  have hrat : ∀ t : Fin n → ℚ, 0 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ)) := by
    intro t
    obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) t
    choose z hz using hn
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
    have hz' : (fun i => (z i : ℝ)) = (D : ℝ) • fun i => (t i : ℝ) := by
      funext i
      have h1 : (z i : ℚ) = D * t i := by simpa [Submonoid.smul_def] using hz i
      have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
      push_cast at h2
      simpa using h2
    have h0 : 0 ≤ z ⬝ᵥ (L *ᵥ z) := by
      rcases eq_or_ne z 0 with h | h
      · simp [h]
      · exact (hp z h).le
    have h3 := hint z
    rw [hz', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h3
    have h4 : 0 ≤ ((D : ℝ) * D) * ((fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ))) := by
      rw [mul_assoc, h3]; exact_mod_cast h0
    exact (mul_nonneg_iff_of_pos_left (mul_self_pos.2 hD')).1 h4
  have hpsd : M.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun y => ?_⟩
    rw [star_trivial]
    have hcl : IsClosed {y : Fin n → ℝ | 0 ≤ y ⬝ᵥ (M *ᵥ y)} :=
      isClosed_le continuous_const
        (Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id))
    exact (DenseRange.piMap fun _ => Rat.denseRange_cast).induction_on y hcl fun t => hrat t
  have hdetM : M.det = (L.det : ℝ) := by
    rw [hM]
    exact ((Int.castRingHom ℝ).map_det L).symm
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  refine lt_of_le_of_ne ((posSemidef_iff_dotProduct_mulVec.1 hpsd).2 x) fun h0 => hdet ?_
  have hk : M *ᵥ x = 0 := (hpsd.dotProduct_mulVec_zero_iff x).1 h0.symm
  have : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩
  rw [hdetM] at this
  exact_mod_cast this

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem exists_supports_int : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    IsPolFanOn id φ X → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone id φ γ →
      ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports id φ d γ a := by
  intro φ X _ _ _ hφ r γ hγ
  classical
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  let b := Module.finBasis ℤ X
  let S : Fin (Module.finrank ℤ X) → Fin (Module.finrank ℤ X) → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) + (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord j) (b.coord i)
  have hS : ∀ i j x y, S i j x y = b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
    intro i j x y; simp [S]
  let L : Matrix (Fin (Module.finrank ℤ X)) (Fin (Module.finrank ℤ X)) ℤ := Matrix.of fun i j => ℓ (S i j)
  have hL : ∀ i j, L i j = ℓ (S i j) := fun _ _ => rfl
  have hexp : ∀ (β : LinearMap.BilinForm ℤ X) x y,
      β x y = ∑ i, ∑ j, b.repr x i * b.repr y j * β (b i) (b j) := by
    intro β x y
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hA : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ i, ∑ j, β (b i) (b j) * L i j = 2 * ℓ β := by
    intro β hβ
    have hsum : ∑ i, ∑ j, β (b i) (b j) • S i j = (2 : ℤ) • β := by
      refine LinearMap.ext₂ fun x y => ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hS]
      have e : (2 : ℤ) * β x y = β x y + β y x := by rw [hβ y x]; ring
      rw [e, hexp β x y, hexp β y x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := congrArg ℓ hsum
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simpa only [hL] using this
  have hsym : L.IsSymm := Matrix.IsSymm.ext fun i j => by simp only [hL, S, add_comm]
  have hpos : ∀ ξ : Fin (Module.finrank ℤ X) → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ) := by
    intro ξ hξ
    let l : X →ₗ[ℤ] ℤ := ∑ i, ξ i • b.coord i
    have hl : ∀ i, l (b i) = ξ i := by
      intro i
      simp [l, Finsupp.single_apply]
    have hsymm : ∀ y z, sqForm l y z = sqForm l z y := fun y z => by simp [mul_comm]
    have hmem : sqForm l ∈ balForms id X := mem_balForms_int.2 hsymm
    have hnn : ∀ y, 0 ≤ sqForm l y y := fun y => by simpa using mul_self_nonneg (l y)
    have hne : sqForm l ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have := LinearMap.congr_fun₂ h0 (b i) (b i)
      simp [hl] at this
      exact hi this
    have hφp := hφ.pos _ hmem hnn hne
    have hℓ := h2 _ hmem hnn
    have hℓpos : 0 < ℓ (sqForm l) := by
      have : (0 : ℝ) < ℓ (sqForm l) := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) hφp) hℓ
      exact_mod_cast this
    have h5 := hA (sqForm l) hsymm
    simp only [sqForm_apply, hl] at h5
    have e : ξ ⬝ᵥ (L *ᵥ ξ) = ∑ i, ∑ j, ξ i * ξ j * L i j := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e, h5]
    omega
  obtain ⟨D, m, a, hD, hspan, hsum⟩ := GlobalTheory.T.exists_smul_eq_sum_vecMulVec_spanning_family _ L (posDef_map_int_of_pos L hsym hpos)
  let x : Fin m → X := fun k => b.equivFun.symm (a k)
  have hx : ∀ k i, b.repr (x k) i = a k i := fun k i => by
    show b.equivFun (b.equivFun.symm (a k)) i = a k i
    rw [b.equivFun.apply_symm_apply]
  have hB : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ k, β (x k) (x k) = 2 * D * ℓ β := by
    intro β hβ
    have hsum' : ∀ i j, (D : ℤ) * L i j = ∑ k, a k i * a k j := by
      intro i j
      have := congrFun (congrFun hsum i) j
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    calc ∑ k, β (x k) (x k) = ∑ k, ∑ i, ∑ j, a k i * a k j * β (b i) (b j) :=
          Finset.sum_congr rfl fun k _ => by rw [hexp β]; simp only [hx]
      _ = ∑ i, ∑ j, β (b i) (b j) * ((D : ℤ) * L i j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsum' i j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = D * (2 * ℓ β) := by
          rw [← hA β hβ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * D * ℓ β := by ring
  have hspanX : Submodule.span ℤ (Set.range x) = ⊤ := by
    have e : Set.range x = (b.equivFun.symm.toLinearMap : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X) '' Set.range a :=
      Set.range_comp _ _
    rw [e, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have hD0 : (0 : ℝ) < 2 * D := by have : (1 : ℝ) ≤ D := by exact_mod_cast hD
                                   linarith
  refine ⟨2 * D * N, m, x, Nat.one_le_iff_ne_zero.2 (by positivity), ⟨hspanX, ?_, ?_, ?_⟩⟩
  · intro β hβ hp
    rw [hB β (mem_balForms_int.1 hβ)]
    have := h2 β hβ hp
    push_cast
    nlinarith
  · intro j
    rw [hB (γ j) (mem_balForms_int.1 (hγ.mem j))]
    push_cast
    rw [h1 j]
    ring
  · intro β hβ hp he
    rw [hB β (mem_balForms_int.1 hβ)] at he
    push_cast at he
    refine h3 β hβ hp (mul_left_cancel₀ hD0.ne' ?_)
    linear_combination he

end GlobalTheory.Poinc
