import Mathlib

open Matrix

namespace GlobalTheory

theorem eigen_decomp_base_change :
  ∀ (K C : Type) [CommRing K] [CommRing C] (n a : ℕ) (ω : K) (tr nm : ℤ), ω ^ 2 - (tr : K) * ω + (nm : K) = 0 → ∀ (f : K →+* Matrix (Fin n) (Fin n) C) (ρ : C), ρ ^ 2 - (tr : C) * ρ + (nm : C) = 0 → IsUnit (2 * ρ - (tr : C)) → ∀ (t : Fin a → (K →+* C)), (∀ i, t i ω = ρ) → (∀ v : Fin n → C, Matrix.mulVec (f ω) v = ρ • v → ∃ w : Fin a → Fin n → C, (∀ i (c : K), Matrix.mulVec (f c) (w i) = t i c • w i) ∧ v = ∑ i, w i) → ∀ (R' : Type) [CommRing R'] (g : C →+* R') (v : Fin n → R'), Matrix.mulVec ((f ω).map g) v = g ρ • v → ∃ w : Fin a → Fin n → R', (∀ i (c : K), Matrix.mulVec ((f c).map g) (w i) = g (t i c) • w i) ∧ v = ∑ i, w i := by
  intro K C _ _ n a ω tr nm hω f ρ hρ hu t ht H R' _ g v hv
  obtain ⟨uinv, huinv⟩ : ∃ uinv : C, uinv * (2 * ρ - (tr : C)) = 1 := by
    obtain ⟨u, hu'⟩ := hu
    exact ⟨↑u⁻¹, by rw [← hu']; simp⟩
  set Ω := f ω with hΩdef

  have hΩΩ : Ω * Ω = (tr : Matrix (Fin n) (Fin n) C) * Ω - (nm : Matrix (Fin n) (Fin n) C) := by
    have h1 : ω * ω = (tr : K) * ω - (nm : K) := by linear_combination hω
    have h2 := congrArg f h1
    simpa [map_mul, map_sub, map_intCast] using h2
  have key : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x) = (tr : C) • (Ω *ᵥ x) - (nm : C) • x := by
    intro x
    rw [mulVec_mulVec, hΩΩ, sub_mulVec, ← mulVec_mulVec, intCast_mulVec, intCast_mulVec]
  have eig : ∀ x : Fin n → C, Ω *ᵥ (Ω *ᵥ x - ((tr : C) - ρ) • x) = ρ • (Ω *ᵥ x - ((tr : C) - ρ) • x) := by
    intro x
    rw [mulVec_sub, mulVec_smul, key]
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(x k)) * hρ
  let e : Fin n → Fin n → C := fun j => uinv • (Ω *ᵥ Pi.single j 1 - ((tr : C) - ρ) • Pi.single j 1)
  have he : ∀ j, Ω *ᵥ e j = ρ • e j := by
    intro j
    simp only [e, mulVec_smul, eig]
    rw [smul_comm]
  choose W hW hWsum using fun j => H (e j) (he j)

  have hmap : ∀ (M : Matrix (Fin n) (Fin n) C) (x : Fin n → C), M.map g *ᵥ (g ∘ x) = g ∘ (M *ᵥ x) := by
    intro M x
    funext k
    simp only [Function.comp_apply]
    rw [RingHom.map_mulVec]
  have hvsum : v = ∑ j, v j • (g ∘ e j) := by
    funext k
    have hv' := congrFun hv k
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hv'
    simp only [e, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.sub_apply,
      mulVec_single_one, col_apply, Pi.single_apply, map_mul, map_sub, mul_ite, mul_one, mul_zero,
      map_zero]
    have hterm : ∀ x, v x * (g uinv * (g (Ω k x) - g (if k = x then (tr : C) - ρ else 0))) =
        g uinv * (g (Ω k x) * v x) - (if k = x then g uinv * g ((tr : C) - ρ) * v k else 0) := by
      intro x
      split_ifs with h
      · subst h; ring
      · simp only [map_zero, sub_zero]; ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_sub_distrib, ← Finset.mul_sum, hv',
      Finset.sum_ite_eq]
    have hg := congrArg g huinv
    simp only [map_mul, map_sub, map_intCast, map_one, map_ofNat] at hg ⊢
    simp only [Finset.mem_univ, if_true]
    linear_combination (-(v k)) * hg
  refine ⟨fun i => ∑ j, v j • (g ∘ W j i), ?_, ?_⟩
  · intro i c
    rw [mulVec_sum]
    simp only [mulVec_smul, hmap, hW]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
    congr 1
    funext k
    simp [Function.comp_apply]
  · conv_lhs => rw [hvsum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    rw [hWsum j]
    funext k
    simp [Finset.sum_apply, map_sum]

end GlobalTheory
