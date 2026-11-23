import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters

open Polynomial GlobalTheory.GLq GlobalTheory.Published

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

def fo (g n : ℕ) {K : Type} [Field K] (θ : Kˣ →* ℂˣ) (z : Kˣ) : ℂ :=
  ∑ i ∈ Finset.range n, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)

section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem charSum (χ : Kˣ →* ℂˣ) :
    ∑ z : Kˣ, ((χ z : ℂˣ) : ℂ) = if χ = 1 then (Fintype.card Kˣ : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  · have hne : (Units.coeHom ℂ).comp χ ≠ 1 := by
      intro hc
      apply h
      ext z
      have := congrArg (fun f : Kˣ →* ℂ => f z) hc
      simpa using this
    exact sum_hom_units_eq_zero _ hne

theorem norm_val (θ : Kˣ →* ℂˣ) (z : Kˣ) : ‖((θ z : ℂˣ) : ℂ)‖ = 1 := by
  have h : (θ z) ^ Fintype.card Kˣ = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card Kˣ) ?_ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem norm_fo_le (g n : ℕ) (θ : Kˣ →* ℂˣ) (z : Kˣ) : ‖fo g n θ z‖ ≤ n := by
  unfold fo
  refine (norm_sum_le _ _).trans ?_
  simp [norm_val]

theorem sum_fo_mul (g n : ℕ) (θ θ' : Kˣ →* ℂˣ) :
    ∑ z : Kˣ, fo g n θ z * fo g n θ' z⁻¹ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if θ ^ g ^ i = θ' ^ g ^ j then (Fintype.card Kˣ : ℂ) else 0 := by
  unfold fo
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ z : Kˣ, ((θ (z ^ g ^ i) : ℂˣ) : ℂ) * ((θ' (z⁻¹ ^ g ^ j) : ℂˣ) : ℂ) =
      (((θ ^ g ^ i * (θ' ^ g ^ j)⁻¹) z : ℂˣ) : ℂ) := by
    intro z
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, map_pow, inv_pow, map_inv,
      Units.val_mul]
  rw [Finset.sum_congr rfl fun z _ => e z, charSum]
  simp only [mul_inv_eq_one]

end

theorem char_pow_period {g n : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K] (hK : Fintype.card K = g ^ n)
    (θ : Kˣ →* ℂˣ) (hg : 0 < g) (a : ℕ) : θ ^ g ^ a = θ ^ g ^ (a % n) := by
  have hN : ∀ z : Kˣ, z ^ (g ^ n - 1) = 1 := fun z => by
    rw [← hK, ← Fintype.card_units]; exact pow_card_eq_one
  have hper : θ ^ g ^ n = θ := by
    ext z
    rw [MonoidHom.pow_apply, ← map_pow]
    have : z ^ g ^ n = z := by
      have h1 : 1 ≤ g ^ n := Nat.one_le_pow _ _ hg
      conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ, hN, one_mul]
    rw [this]
  have ha : g ^ a = (g ^ n) ^ (a / n) * g ^ (a % n) := by
    conv_lhs => rw [← Nat.mod_add_div a n]
    rw [pow_add, pow_mul, mul_comm]
  have : ∀ m : ℕ, θ ^ (g ^ n) ^ m = θ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hper]
  rw [ha, pow_mul, this]

end DiscreteGroups.sglob.DzType.Kon
