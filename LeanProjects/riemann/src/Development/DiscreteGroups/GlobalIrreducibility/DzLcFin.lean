import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors

noncomputable section

open GlobalTheory.GLq
open scoped Classical

namespace DiscreteGroups.sglob.DzLc

theorem sum_rho_eq_zero {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) (U : Subgroup G) {_ : Fintype U}
    (h : ∑ u : U, τ.character (u : G) = 0) : ∑ u : U, τ.ρ (u : G) = 0 := by
  obtain ⟨E, hE⟩ : ∃ E : Module.End ℂ τ, E = ∑ u : U, τ.ρ (u : G) := ⟨_, rfl⟩
  rw [← hE]
  have hinv : ∀ v : U, τ.ρ (v : G) * E = E := by
    intro v
    rw [hE, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ fun u => ?_
    simp [map_mul]
  have hsq : E * E = (Fintype.card U : ℂ) • E := by
    calc E * E = ∑ u : U, τ.ρ (u : G) * E := by nth_rewrite 1 [hE]; rw [Finset.sum_mul]
      _ = ∑ _u : U, E := Finset.sum_congr rfl fun u _ => hinv u
      _ = (Fintype.card U : ℂ) • E := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have htE : LinearMap.trace ℂ τ E = 0 := by
    rw [hE, map_sum]
    exact h
  have hc : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨P, hP⟩ : ∃ P : Module.End ℂ τ, P = (Fintype.card U : ℂ)⁻¹ • E := ⟨_, rfl⟩
  have hPP : P * P = P := by
    rw [hP, smul_mul_assoc, mul_smul_comm, hsq, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hproj : LinearMap.IsProj (LinearMap.range P) P :=
    ⟨fun x => LinearMap.mem_range_self P x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact congrArg (fun f : Module.End ℂ τ => f y) hPP⟩
  have htP : LinearMap.trace ℂ τ P = 0 := by
    rw [hP, map_smul, htE, smul_zero]
  rw [hproj.trace, Nat.cast_eq_zero, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at htP
  calc E = (Fintype.card U : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = 0 := by rw [htP, smul_zero]

variable {g : ℕ} [Fact g.Prime]

theorem res_eq {n a : ℕ} (ha : a < n) (χ : Gn g n → ℂ) :
    res a (n - a) χ 1 1 = ((g : ℂ) ^ (a * (n - a)))⁻¹ *
      ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a), χ (u : Gn g n) := by
  unfold res
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => x ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g)
    (GlobalTheory.FiniteGL.twoBlocks n a)) _ (fun x => by rw [GlobalTheory.SerSys.TameGen.mem_unipRadical_iff ha]; simp) χ]

theorem sum_unip_eq_zero {n a : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) (h0 : 0 < a) (ha : a < n) :
    ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a), τ.ρ (u : Gn g n) = 0 := by
  refine sum_rho_eq_zero τ _ ?_
  have hres := hτ.2.2 a h0 ha
  rw [res_eq ha] at hres
  refine (mul_eq_zero.1 hres).resolve_left ?_
  have : (g : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  exact inv_ne_zero (pow_ne_zero _ this)

end DiscreteGroups.sglob.DzLc
