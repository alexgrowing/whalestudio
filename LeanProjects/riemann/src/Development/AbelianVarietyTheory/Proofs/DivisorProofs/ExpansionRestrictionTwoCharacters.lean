import Mathlib
open Polynomial

namespace GlobalTheory

theorem expansion_restrict_two_characters : (∀ (G : Type) [CommGroup G] (L : G → ℝ), (∀ x y, L (x * y) = L x + L y) → (∃ t, L t ≠ 0) → ∀ (ι : Type) [Fintype ι] (χ : ι → G →* ℂˣ), Function.Injective χ → ∀ (P : ι → ℂ[X]), (∀ t, ∑ i, (P i).eval ((L t : ℝ) : ℂ) * ((χ i t : ℂˣ) : ℂ) = 0) → ∀ i, P i = 0) → ∀ (T : Type) [CommGroup T] (L : T → ℝ), (∀ x y, L (x * y) = L x + L y) → ∀ (N : ℕ) (χ : Fin N → T →* ℂˣ) (P : Fin N → ℂ[X]), Function.Injective χ → ∀ (H : Subgroup T) (ψ₁ ψ₂ : T →* ℂˣ), (∃ x ∈ H, L x ≠ 0) → (∀ s, ∃ p q : ℂ, ∀ x ∈ H, ∑ i, (P i).eval ((L (x * s) : ℝ) : ℂ) * ((χ i (x * s) : ℂˣ) : ℂ) = p * ((ψ₁ x : ℂˣ) : ℂ) + q * ((ψ₂ x : ℂˣ) : ℂ)) → ∀ i, P i ≠ 0 → derivative (P i) = 0 ∧ ((∀ x ∈ H, χ i x = ψ₁ x) ∨ ∀ x ∈ H, χ i x = ψ₂ x) := by
  classical
  intro hInd T _ L hL N χ P hχ H ψ₁ ψ₂ hH hexp
  obtain ⟨x₀, hx₀H, hx₀⟩ := hH
  choose p q hpq using hexp
  let r : (T →* ℂˣ) → (↥H →* ℂˣ) := fun φ => φ.comp H.subtype
  let S : Finset (↥H →* ℂˣ) := Finset.univ.image (fun i => r (χ i)) ∪ {r ψ₁, r ψ₂}
  have hS : ∀ i, r (χ i) ∈ S := fun i =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hS1 : r ψ₁ ∈ S := by simp [S]
  have hS2 : r ψ₂ ∈ S := by simp [S]
  let Q : T → (↥H →* ℂˣ) → ℂ[X] := fun s η =>
    (∑ i, if r (χ i) = η then C ((χ i s : ℂˣ) : ℂ) * taylor ((L s : ℝ) : ℂ) (P i) else 0)
      - (if r ψ₁ = η then C (p s) else 0) - (if r ψ₂ = η then C (q s) else 0)
  have hQeval : ∀ s η (z : ℂ), (Q s η).eval z =
      (∑ i, if r (χ i) = η then ((χ i s : ℂˣ) : ℂ) * (P i).eval (z + ((L s : ℝ) : ℂ)) else 0)
        - (if r ψ₁ = η then p s else 0) - (if r ψ₂ = η then q s else 0) := by
    intro s η z
    simp only [Q, eval_sub, eval_finsetSum]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp [taylor_eval]
      · split_ifs <;> simp
    · split_ifs <;> simp
  have hQ0 : ∀ s, ∀ η ∈ S, Q s η = 0 := by
    intro s
    have hL' : ∀ a b : ↥H, L ((a * b : ↥H) : T) = L a + L b := fun a b => hL a b
    have key := hInd (↥H) (fun a => L a) hL' ⟨⟨x₀, hx₀H⟩, hx₀⟩ (↥S) (fun η => (η : ↥H →* ℂˣ))
      Subtype.val_injective (fun η => Q s η) ?_
    · intro η hη; exact key ⟨η, hη⟩
    intro x
    rw [Finset.sum_coe_sort S (fun η => (Q s η).eval ((L x : ℝ) : ℂ) * ((η x : ℂˣ) : ℂ))]
    simp only [hQeval, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, hS, hS1, hS2, if_true]
    have h := hpq s x x.2
    simp only [r, MonoidHom.comp_apply, Subgroup.coe_subtype]
    have e : (∑ i, ((χ i s : ℂˣ) : ℂ) * (P i).eval (((L (x : T) : ℝ) : ℂ) + ((L s : ℝ) : ℂ))
        * ((χ i (x : T) : ℂˣ) : ℂ)) = ∑ i, (P i).eval ((L ((x : T) * s) : ℝ) : ℂ) * ((χ i ((x : T) * s) : ℂˣ) : ℂ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, map_mul, Units.val_mul, Complex.ofReal_add]; ring
    rw [e, h]; ring
  have hD : ∀ η ∈ S, ∀ i, r (χ i) = η → derivative (P i) = 0 := by
    intro η hη
    have key := hInd T L hL ⟨x₀, hx₀⟩ (Fin N) χ hχ
      (fun i => if r (χ i) = η then derivative (P i) else 0) ?_
    · intro i hi; simpa [hi] using key i
    intro t
    have h1 := congrArg (fun f => f.coeff 1) (hQ0 t η hη)
    simp only [Q, coeff_sub, finsetSum_coeff, apply_ite (fun f : ℂ[X] => f.coeff 1), coeff_C_mul,
      taylor_coeff_one, coeff_C, coeff_zero, one_ne_zero, if_false, ite_self, sub_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  have hZ : ∀ η ∈ S, r ψ₁ ≠ η → r ψ₂ ≠ η → ∀ i, r (χ i) = η → P i = 0 := by
    intro η hη h₁ h₂
    have key := hInd T L hL ⟨x₀, hx₀⟩ (Fin N) χ hχ
      (fun i => if r (χ i) = η then P i else 0) ?_
    · intro i hi; simpa [hi] using key i
    intro t
    have h1 := congrArg (fun f => f.coeff 0) (hQ0 t η hη)
    simp only [Q, coeff_sub, finsetSum_coeff, apply_ite (fun f : ℂ[X] => f.coeff 0), coeff_C_mul,
      taylor_coeff_zero, coeff_zero, h₁, h₂, if_false, sub_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  intro i hi
  refine ⟨hD _ (hS i) i rfl, ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hc
  exact hi (hZ _ (hS i) (fun e => ha' (DFunLike.congr_fun e ⟨a, ha⟩).symm)
    (fun e => hb' (DFunLike.congr_fun e ⟨b, hb⟩).symm) i rfl)

end GlobalTheory
