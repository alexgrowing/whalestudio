import Mathlib

open Polynomial

namespace GlobalTheory

theorem newton_powerSeries_of_surjective_linearisation (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ]
    (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k))
    (hL : Function.Surjective L)
    (h0 : ∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0)
    (hG : ∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e -
        PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) :
    ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  classical
  let r := Function.surjInv hL
  have hLr : ∀ v, L (r v) = v := Function.surjInv_eq hL
  let step : ℕ → (ι → PowerSeries k) → (ι → PowerSeries k) := fun m x i =>
    x i + PowerSeries.X ^ m * PowerSeries.C (r (fun e => -PowerSeries.coeff m (G x e)) i)
  let sq : ℕ → (ι → PowerSeries k) := fun n =>
    Nat.rec (motive := fun _ => ι → PowerSeries k) (fun i => PowerSeries.C (x₀ i)) (fun n x => step (n + 1) x) n
  have sq_zero : sq 0 = fun i => PowerSeries.C (x₀ i) := rfl
  have sq_succ : ∀ n, sq (n + 1) = step (n + 1) (sq n) := fun n => rfl
  have coeffXC : ∀ (m j : ℕ) (c : k),
      PowerSeries.coeff j ((PowerSeries.X : PowerSeries k) ^ m * PowerSeries.C c) = if j = m then c else 0 := by
    intro m j c
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
  have inv : ∀ n, (∀ i, PowerSeries.constantCoeff (sq n i) = x₀ i) ∧
      ∀ e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G (sq n) e := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => by simp [sq_zero], fun e => ?_⟩
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, sq_zero]
      exact h0 e
    | succ n ih =>
      have hc : ∀ i, PowerSeries.constantCoeff (sq (n + 1) i) = x₀ i := by
        intro i
        simp [sq_succ, step, ih.1 i]
      refine ⟨hc, fun e => ?_⟩
      set x := sq n with hx
      set v : κ → k := fun e => -PowerSeries.coeff (n + 1) (G x e) with hv
      have key := hG x (fun i => PowerSeries.C (r v i)) (n + 1) (by omega) ih.1 e
      have hcv : (fun i => PowerSeries.constantCoeff (PowerSeries.C (r v i))) = r v := by
        funext i; simp
      rw [hcv, hLr] at key
      have hs : sq (n + 1) = fun i => x i + PowerSeries.X ^ (n + 1) * PowerSeries.C (r v i) := by
        rw [sq_succ]
      have h2 : (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) ∣
          G x e + PowerSeries.X ^ (n + 1) * PowerSeries.C (v e) := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro j hj
        rw [map_add, coeffXC]
        rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · have := (PowerSeries.X_pow_dvd_iff.mp (ih.2 e)) j hj'
          rw [this, if_neg (by omega), add_zero]
        · have hjn : j = n + 1 := by omega
          subst hjn
          simp [hv]
      have := dvd_add key h2
      rw [hs]
      convert this using 1
      ring
  have stab : ∀ i j n, j ≤ n → PowerSeries.coeff j (sq n i) = PowerSeries.coeff j (sq j i) := by
    intro i j n hjn
    induction n, hjn using Nat.le_induction with
    | base => rfl
    | succ n hjn ihn =>
      rw [← ihn, sq_succ]
      simp only [step, map_add]
      rw [coeffXC, if_neg (by omega), add_zero]
  let xl : ι → PowerSeries k := fun i => PowerSeries.mk (fun j => PowerSeries.coeff j (sq j i))
  have hdiff : ∀ n i, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ xl i - sq n i := by
    intro n i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    simp only [xl, map_sub, PowerSeries.coeff_mk]
    rw [stab i j n (by omega), sub_self]
  have hlim : ∀ n e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e := by
    intro n e
    choose d hd using hdiff n
    have hx : xl = fun i => sq n i + PowerSeries.X ^ (n + 1) * d i := by
      funext i; rw [← hd i]; ring
    have key := hG (sq n) d (n + 1) (by omega) (inv n).1 e
    rw [← hx] at key
    have k1 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e - G (sq n) e := by
      have h3 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) :=
        pow_dvd_pow _ (by omega)
      have := dvd_add (h3.trans key) (dvd_mul_right ((PowerSeries.X : PowerSeries k) ^ (n + 1))
        (PowerSeries.C (L (fun i => PowerSeries.constantCoeff (d i)) e)))
      simpa using this
    have := dvd_add k1 ((inv n).2 e)
    simpa using this
  refine ⟨xl, fun i => ?_, fun e => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [xl, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).1 i
  · ext j
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.mp (hlim j e) j (by omega)

theorem newton_powerSeries_target : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 :=
  fun k ι κ _ _ _ G x₀ L hL h0 hG => newton_powerSeries_of_surjective_linearisation k ι κ G x₀ L hL h0 hG

end GlobalTheory
