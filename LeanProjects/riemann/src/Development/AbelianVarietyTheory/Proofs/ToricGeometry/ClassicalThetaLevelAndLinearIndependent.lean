import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem classicalTheta_level_and_linearIndependent' (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : τ ∈ SiegelH (Fin g)) (N : ℕ) (hN : 1 ≤ N) :
    (∀ c : Fin g → Fin N,
      (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧
        ∀ (n n' : Fin g → ℤ) z,
          (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))
              (z + τ *ᵥ ofIntVec n + ofIntVec n') =
            eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) *
              (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧
    LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) := by
  have e (c : Fin g → Fin N) : levelTheta 0 0 N τ (fun i => ((c i : ℕ) : ℤ)) =
      fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
    funext z
    rw [levelTheta_zero_zero]
    simp only [Int.cast_natCast]
  refine ⟨fun c => ?_, ?_⟩
  · have h := levelTheta_zero_zero_mem hτ hN (fun i => ((c i : ℕ) : ℤ))
    rw [e] at h
    exact mem_thetaLevel.1 h
  · have h := linearIndependent_levelTheta (a := 0) (b := 0) hτ hN
      (r := fun (c : Fin g → Fin N) i => ((c i : ℕ) : ℤ)) (bijective_fin_zmod hN).1
    simpa only [e] using h

open Complex Matrix Filter Topology in
open scoped BigOperators Real in

theorem _root_.GlobalTheory.classicalTheta_level_and_linearIndependent :
    _root_.ReciprocityTheory.PTheta.SiegelSubDomainStatement → _root_.ReciprocityTheory.PTheta.ThetaHoloStatement → _root_.ReciprocityTheory.PTheta.ThetaMTestStatement → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by
  intro _ _ _ g τ hτ N hN
  have hN0 : 0 < N := hN
  have heq : ∀ c : Fin g → Fin N, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) =
      _root_.GlobalTheory.levelTheta 0 0 N τ (fun i => ((c i : ℕ) : ℤ)) := by
    intro c
    funext z
    rw [_root_.GlobalTheory.levelTheta_zero_zero]
    simp
  refine ⟨fun c => ?_, ?_⟩
  · rw [heq c]
    exact _root_.GlobalTheory.mem_thetaLevel.1 (_root_.GlobalTheory.levelTheta_zero_zero_mem hτ hN0 _)
  · have := _root_.GlobalTheory.linearIndependent_levelTheta (a := 0) (b := 0) hτ hN0
      (r := fun (c : Fin g → Fin N) i => ((c i : ℕ) : ℤ))
      (_root_.GlobalTheory.bijective_fin_zmod (ι := Fin g) hN0).injective
    convert this using 1
    funext c
    exact heq c

end GlobalTheory
