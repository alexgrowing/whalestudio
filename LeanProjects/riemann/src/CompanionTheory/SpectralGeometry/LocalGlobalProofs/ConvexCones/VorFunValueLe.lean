import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem vorFun_value_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (n : ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X)
    (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) →
    Covers2 (fun y => r (a y)) ∧ ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y, 0 ≤ B y y) →
      (2 : ℝ) ^ n * evalR (vorFun O g) B ≤ 2 ^ g * ∑ y, B (r (a y)) (r (a y)) ∧
      ((2 : ℝ) ^ n * evalR (vorFun O g) B = 2 ^ g * ∑ y, B (r (a y)) (r (a y)) ↔ ∀ y, IsMin2 B (r (a y))) := by
  intro O _ _ _ _ bar g X _ _ _ n r a hr ha
  have hfin : Module.Finite ℤ X := Module.Finite.of_surjective r hr
  have hs : ∀ c d : Fin n → ℤ, r (c + (((1 : ℕ) : ℤ) + 1) • d) = r c + (r d + r d) := fun c d => by
    rw [map_add, map_smul, show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num, two_smul]
  refine ⟨fun x => ?_, fun B hB => ?_⟩
  · obtain ⟨b, rfl⟩ := hr x
    obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq (M := 1) (a := b) (a' := a (redV 1 b)) (ha _).symm
    exact ⟨redV 1 b, r d, by rw [← hs, ← hd]⟩
  set Br : (Fin n → ℤ) → (Fin n → ℤ) → ℝ := fun c d => B (r c) (r d) with hBr
  have hval : (2 : ℝ) ^ n * evalR (vorFun O g) B = 2 ^ g * ∑ y, classMin 1 Br y := by
    have h0 : zeroFun.eval X (fun c d => B c d) = 0 := by
      rw [zeroFun.eval_eq hr]; rfl
    have h1 : (fineMean 1).eval X (fun c d => B c d) =
        (((((1 : ℕ) : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin 1 Br y - Br 0 0) := by
      rw [(fineMean 1).eval_eq hr]; rfl
    have h2 : Br 0 0 = 0 := by simp [hBr]
    have h3 : ((fineDen g {1} : ℕ) : ℝ) = 2 ^ g := by
      simp only [fineDen, Finset.prod_singleton]; norm_num
    have h4 : (((1 : ℕ) : ℝ) + 1) = 2 := by norm_num
    unfold evalR vorFun
    rw [eval_baseFun, h0, Finset.sum_singleton, h1, h2, h3, h4]
    field_simp
    ring
  have hbdd : ∀ y, BddBelow {x | ∃ c : Fin n → ℤ, redV 1 c = y ∧ Br c c = x} := fun y =>
    ⟨0, by rintro x ⟨c, -, rfl⟩; exact hB _⟩
  have hle : ∀ y, classMin 1 Br y ≤ B (r (a y)) (r (a y)) := fun y =>
    csInf_le (hbdd y) ⟨a y, ha y, rfl⟩
  have hiff : ∀ y, classMin 1 Br y = B (r (a y)) (r (a y)) ↔ IsMin2 B (r (a y)) := fun y => by
    constructor
    · intro h x
      obtain ⟨b, rfl⟩ := hr x
      rw [← h, ← hs]
      refine csInf_le (hbdd y) ⟨_, ?_, rfl⟩
      rw [redV_add_smul, ha]
    · intro h
      refine le_antisymm (hle y) (le_csInf ⟨_, a y, ha y, rfl⟩ ?_)
      rintro x ⟨c, hc, rfl⟩
      obtain ⟨d, rfl⟩ := exists_eq_add_of_redV_eq (M := 1) (a := c) (a' := a y) (by rw [hc, ha])
      simp only [hBr]
      rw [hs]
      exact h _
  have hp : (0 : ℝ) < 2 ^ g := by positivity
  rw [hval]
  refine ⟨mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hle y) hp.le, ?_⟩
  rw [mul_right_inj' hp.ne', Finset.sum_eq_sum_iff_of_le fun y _ => hle y]
  simp only [Finset.mem_univ, true_imp_iff, hiff]

end GlobalTheory.CompanionTheory.Ar.Fan
