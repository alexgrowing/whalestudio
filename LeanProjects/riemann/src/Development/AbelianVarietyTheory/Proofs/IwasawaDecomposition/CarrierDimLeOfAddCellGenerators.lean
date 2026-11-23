import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem carrierDim_le_of_add_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  intro O _ bar q ψ lab hlab X _ _ _ _ hX b v hv β₀ hβ₀ hp₀ β hβ hp hin c₀ c hc₀ hc hrel
  obtain ⟨e, he, he'⟩ := hin
  have hw : ∀ k, 0 ≤ c₀ * e k + c k := fun k => add_nonneg (mul_nonneg hc₀.le (he k)) (hc k)
  have hcomb : toReal β = ∑ k, (c₀ * e k + c k) • toReal (v k) := by
    rw [hrel, he', Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, add_smul]
  have hβv : InRCone v β := ⟨_, hw, hcomb⟩
  have hne : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}).Nonempty := ⟨_, b, v, hv, hβv, rfl⟩
  obtain ⟨m, τ, hτ, hβτ, hrank⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hτ.strict
  have hψτ : ((ℓ β : ℤ) : ℝ) = N * ψ.evalZ β := by
    obtain ⟨d, hd, hde⟩ := hβτ
    rw [apply_eq_of_toReal_eq hde ℓ]
    have A := (linearOn_iff ψ τ).1 hτ.linear d hd
    rw [← hde, evalR_toReal] at A
    rw [A, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring
  have hψv : ψ.evalZ β = c₀ * ψ.evalZ β₀ + ∑ k, c k * ψ.evalZ (v k) := by
    have A := (linearOn_iff ψ v).1 hv.linear _ hw
    rw [← hcomb, evalR_toReal] at A
    have B := (linearOn_iff ψ v).1 hv.linear e he
    rw [← he', evalR_toReal] at B
    rw [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hℓv : ((ℓ β : ℤ) : ℝ) = c₀ * ℓ β₀ + ∑ k, c k * ℓ (v k) := by
    rw [apply_eq_of_toReal_eq hcomb ℓ, apply_eq_of_toReal_eq he' ℓ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k, (N : ℝ) * ψ.evalZ (v k) ≤ ℓ (v k) := fun k => h2 _ (hv.mem k) (hv.nonneg k)
  have h0 : (N : ℝ) * ψ.evalZ β₀ ≤ ℓ β₀ := h2 _ hβ₀ hp₀
  have heq : (N : ℝ) * ψ.evalZ β₀ = ℓ β₀ := by
    have hsum : ∑ k, c k * (N * ψ.evalZ (v k)) ≤ ∑ k, c k * (ℓ (v k) : ℝ) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hc k)
    have E : c₀ * (ℓ β₀ : ℝ) + ∑ k, c k * (ℓ (v k) : ℝ) = c₀ * (N * ψ.evalZ β₀) + ∑ k, c k * (N * ψ.evalZ (v k)) := by
      rw [← hℓv, hψτ, hψv, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    by_contra hne'
    have hlt : (N : ℝ) * ψ.evalZ β₀ < ℓ β₀ := lt_of_le_of_ne h0 hne'
    have := mul_lt_mul_of_pos_left hlt hc₀
    linarith
  obtain ⟨kk, d, hkk, hd⟩ := h3 β₀ hβ₀ hp₀ heq
  have hβ₀τ : InRCone τ β₀ := by
    refine ⟨fun i => (d i : ℝ) / kk, fun i => by positivity, LinearMap.ext₂ fun a b' => ?_⟩
    have h := LinearMap.congr_fun₂ hd a b'
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h
    have hR : (kk : ℝ) * (β₀ a b' : ℝ) = ∑ i, (d i : ℝ) * (τ i a b' : ℝ) := by exact_mod_cast h
    have hkR : (kk : ℝ) ≠ 0 := by positivity
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    calc (β₀ a b' : ℝ) = ((kk : ℝ) * (β₀ a b' : ℝ)) / kk := by field_simp
      _ = _ := by rw [hR, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have hle := Nat.sInf_le (s := {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β₀ ∧ genRank γ = k}) ⟨m, τ, hτ, hβ₀τ, rfl⟩
  rw [hlab X hX β hβ hp, hlab X hX β₀ hβ₀ hp₀]
  exact_mod_cast hle.trans hrank.le

end GlobalTheory.PolFan
