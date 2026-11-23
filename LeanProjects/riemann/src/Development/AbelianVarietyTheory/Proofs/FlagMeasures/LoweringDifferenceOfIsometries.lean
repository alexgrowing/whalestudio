import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

open Matrix

namespace GlobalTheory

theorem hform_sub_left_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x x' y : n → A) :
    Formalism.UG.hform σ J (x - x') y = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x' y := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right_flag {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J : Matrix n n A) (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  unfold Formalism.UG.hform
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem hform_eq_dotProduct_mulVec {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private theorem hform_mulVec_eq_of_unitary {K : Type} [CommRing K] {n : ℕ} (σ : K →+* K)
    (J γ : Matrix (Fin n) (Fin n) K) (hγ : Formalism.UG.cT σ γ * J * γ = J) (x y : Fin n → K) :
    Formalism.UG.hform σ J (γ *ᵥ x) (γ *ᵥ y) = Formalism.UG.hform σ J x y := by
  rw [hform_eq_dotProduct_mulVec, hform_eq_dotProduct_mulVec]
  have h1 : (fun i => σ ((γ *ᵥ x) i)) = γ.map σ *ᵥ (fun i => σ (x i)) := by
    funext i
    exact RingHom.map_mulVec σ γ x i
  unfold Formalism.UG.cT at hγ
  rw [Matrix.mul_assoc] at hγ
  rw [h1, ← vecMul_transpose (γ.map σ), ← dotProduct_mulVec]
  simp only [mulVec_mulVec, hγ]

theorem lowering_difference_of_isometries :
    ∀ (K R : Type) [Field K] [StarRing K] [CommRing R] [Algebra R K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm (starRingEnd K) J → ∀ (a : ℕ) (G : ℕ → Submodule R (Fin n → K)), G 0 = ⊥ → Monotone G → (∀ p ≤ 2 * a + 1, ∀ y, y ∈ G (2 * a + 1 - p) ↔ y ∈ G (2 * a + 1) ∧ ∀ s ∈ G p, Formalism.UG.hform (starRingEnd K) J s y = 0) → ∀ γ γ' : Matrix (Fin n) (Fin n) K, Formalism.UG.cT (starRingEnd K) γ * J * γ = J → Formalism.UG.cT (starRingEnd K) γ' * J * γ' = J → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ - 1) *ᵥ y ∈ G p) → (∀ p ≤ 2 * a, ∀ y ∈ G (p + 1), (γ' - 1) *ᵥ y ∈ G p) → ∀ c : ℕ, 1 ≤ c → (∀ q p : ℕ, q < p → q + p ≤ 2 * a → p - q < c → ∀ y ∈ G (p + 1), (γ - γ') *ᵥ y ∈ G q) → (∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c)) ∧ ∀ p p' : ℕ, p ≤ 2 * a → p' ≤ 2 * a → p + p' ≤ 2 * a + c → ∀ x ∈ G (p + 1), ∀ y ∈ G (p' + 1), Formalism.UG.hform (starRingEnd K) J ((γ - γ') *ᵥ x) y + Formalism.UG.hform (starRingEnd K) J x ((γ - γ') *ᵥ y) = 0 := by
  intro K R _ _ _ _ n J _ a G hG0 hGm hdual γ γ' hγ hγ' hl hl' c hc hlow
  set hf := Formalism.UG.hform (starRingEnd K) J with hhf
  have hL : ∀ x x' y, hf (x - x') y = hf x y - hf x' y := fun x x' y => hform_sub_left_flag _ J x x' y
  have hR : ∀ x y y', hf x (y - y') = hf x y - hf x y' := fun x y y' => hform_sub_right_flag _ J x y y'
  have iso : ∀ x y, hf (γ *ᵥ x) (γ *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ hγ
  have iso' : ∀ x y, hf (γ' *ᵥ x) (γ' *ᵥ y) = hf x y := hform_mulVec_eq_of_unitary _ J γ' hγ'
  have h0 : ∀ v, hf 0 v = 0 := fun v => by simp [hhf, Formalism.UG.hform]
  have mem0 : ∀ y ∈ G 0, y = 0 := fun y hy => by
    rw [hG0] at hy
    exact (Submodule.mem_bot R).1 hy
  have orth : ∀ m m', m + m' ≤ 2 * a + 1 → ∀ u ∈ G m, ∀ v ∈ G m', hf u v = 0 := by
    intro m m' hmm u hu v hv
    exact ((hdual m (by omega) v).1 (hGm (by omega) hv)).2 u hu
  have key : ∀ x y, hf ((γ - γ') *ᵥ x) (γ *ᵥ y) + hf (γ' *ᵥ x) ((γ - γ') *ᵥ y) = 0 := by
    intro x y
    rw [sub_mulVec, sub_mulVec, hL, hR, iso, iso']
    ring
  have base : ∀ p ≤ 2 * a + 1, ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - 1) := by
    intro p hp y hy
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [mem0 y hy, mulVec_zero]
      exact zero_mem _
    · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
      have e : (γ - γ') *ᵥ y = (γ - 1) *ᵥ y - (γ' - 1) *ᵥ y := by
        simp only [sub_mulVec, one_mulVec]
        abel
      rw [e, Nat.add_sub_cancel]
      exact sub_mem (hl p0 (by omega) y hy) (hl' p0 (by omega) y hy)
  have main1 : ∀ p, p ≤ 2 * a + 1 → ∀ y ∈ G p, (γ - γ') *ᵥ y ∈ G (p - c) := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp y hy
      by_cases hA : c = 1 ∨ p ≤ 1
      · exact hGm (by omega) (base p hp y hy)
      by_cases hB : 2 * p ≤ 2 * a + 1 + c ∨ p < c
      · obtain ⟨p0, rfl⟩ : ∃ p0, p = p0 + 1 := ⟨p - 1, by omega⟩
        exact hlow (p0 + 1 - c) p0 (by omega) (by omega) (by omega) y hy
      have hγy : γ *ᵥ y ∈ G p := by
        have e1 : γ *ᵥ y = (γ - 1) *ᵥ y + y := by
          simp only [sub_mulVec, one_mulVec]
          abel
        rw [e1]
        refine add_mem (hGm (Nat.sub_le p 1) (hl (p - 1) (by omega) y ?_)) hy
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      have inner : ∀ j, j ≤ 2 * a + 1 - (p - c) → ∀ s ∈ G j, hf s ((γ - γ') *ᵥ y) = 0 := by
        intro j
        induction j with
        | zero =>
          intro _ s hs
          rw [mem0 s hs, h0]
        | succ j ihj =>
          intro hj s hs
          have k := key s y
          have ha : hf ((γ' - 1) *ᵥ s) ((γ - γ') *ᵥ y) =
              hf (γ' *ᵥ s) ((γ - γ') *ᵥ y) - hf s ((γ - γ') *ᵥ y) := by
            rw [sub_mulVec γ' 1, one_mulVec, hL]
          have hz1 := ihj (by omega) _ (hl' j (by omega) s hs)
          have hz2 := orth (j + 1 - c) p (by omega) _ (ih (j + 1) (by omega) (by omega) s hs) _ hγy
          linear_combination k + ha - hz1 - hz2
      have hd := (hdual (2 * a + 1 - (p - c)) (by omega) ((γ - γ') *ᵥ y)).2
        ⟨hGm (by omega) (base p hp y hy), fun s hs => inner _ le_rfl s hs⟩
      have e2 : 2 * a + 1 - (2 * a + 1 - (p - c)) = p - c := by omega
      rwa [e2] at hd
  refine ⟨main1, ?_⟩
  intro p p' hp hp' hpp x hx y hy
  have e3 : hf ((γ - γ') *ᵥ x) ((γ - 1) *ᵥ y) = 0 :=
    orth (p + 1 - c) p' (by omega) _ (main1 (p + 1) (by omega) x hx) _ (hl p' hp' y hy)
  have e4 : hf ((γ' - 1) *ᵥ x) ((γ - γ') *ᵥ y) = 0 :=
    orth p (p' + 1 - c) (by omega) _ (hl' p hp x hx) _ (main1 (p' + 1) (by omega) y hy)
  rw [sub_mulVec γ 1, one_mulVec, hR] at e3
  rw [sub_mulVec γ' 1, one_mulVec, hL] at e4
  linear_combination key x y - e3 - e4

end GlobalTheory
