import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.GNorm

theorem entry_bound {ι κ E : Type} [Fintype κ] [DecidableEq κ] [Ring E] {m n : ℕ}
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) (s : κ → ℝ) (hs : ∀ k, 0 < s k)
    (B : ι → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ))
    (ξ : Matrix (Fin m) (Fin n) E) (τ : ι) (k : κ) (j : Fin n) :
    ‖σ τ ((T * ξ) k j)‖ / s k ≤ ∑ i, ‖T.map (σ τ) k i‖ * ‖(B τ * ξ.map (σ τ)) i j‖ := by
  have hmap : σ τ ((T * ξ) k j) = (T.map (σ τ) * ξ.map (σ τ)) k j := by
    rw [← Matrix.map_mul]; rfl
  have key : ((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j) = (T.map (σ τ) * (B τ * ξ.map (σ τ))) k j := by
    rw [hmap, ← Matrix.mul_assoc, hB τ, Matrix.mul_assoc, Matrix.diagonal_mul]
  have hnorm : ‖σ τ ((T * ξ) k j)‖ / s k = ‖((s k : ℝ) : ℂ)⁻¹ * σ τ ((T * ξ) k j)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hs k).le, div_eq_inv_mul]
  rw [hnorm, key, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun i _ => norm_mul _ _)

theorem gnorm_gen {ι κ E : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] [Ring E] (m n : ℕ)
    (σ : ι → E →+* ℂ) (T : Matrix κ (Fin m) E) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : ι → Matrix (Fin m) (Fin m) ℂ,
      (∀ τ, T.map (σ τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (σ τ)) →
      ∀ ξ : Matrix (Fin m) (Fin n) E,
        ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤
          C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (σ τ)) i j‖ := by
  set c : ℝ := ∑ τ, ∑ k, ∑ i, ‖T.map (σ τ) k i‖ with hc
  have hc0 : 0 ≤ c := by positivity
  have hac : ∀ τ k i, ‖T.map (σ τ) k i‖ ≤ c := by
    intro τ k i
    have h1 : ‖T.map (σ τ) k i‖ ≤ ∑ i', ‖T.map (σ τ) k i'‖ :=
      Finset.single_le_sum (f := fun i' => ‖T.map (σ τ) k i'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i', ‖T.map (σ τ) k i'‖ ≤ ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ :=
      Finset.single_le_sum (f := fun k' => ∑ i', ‖T.map (σ τ) k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ k)
    have h3 : ∑ k', ∑ i', ‖T.map (σ τ) k' i'‖ ≤ c :=
      Finset.single_le_sum (f := fun τ' => ∑ k', ∑ i', ‖T.map (σ τ') k' i'‖) (fun _ _ => by positivity) (Finset.mem_univ τ)
    linarith
  refine ⟨1 + Fintype.card κ * c, by nlinarith [hc0, (Nat.cast_nonneg (Fintype.card κ) : (0:ℝ) ≤ _)], ?_⟩
  intro s hs B hB ξ
  set b : ι → Fin m → Fin n → ℝ := fun τ i j => ‖(B τ * ξ.map (σ τ)) i j‖ with hb
  have hb0 : ∀ τ i j, 0 ≤ b τ i j := fun _ _ _ => norm_nonneg _
  have S0 : 0 ≤ ∑ τ, ∑ i, ∑ j, b τ i j := by positivity
  calc ∑ p : κ × Fin n, (∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖) / s p.1
      = ∑ p : κ × Fin n, ∑ τ, ‖σ τ ((T * ξ) p.1 p.2)‖ / s p.1 := by
        simp_rw [Finset.sum_div]
    _ ≤ ∑ p : κ × Fin n, ∑ τ, ∑ i, c * b τ i p.2 := by
        gcongr with p _ τ _
        refine (entry_bound σ T s hs B hB ξ τ p.1 p.2).trans ?_
        gcongr with i _
        exact hac τ p.1 i
    _ = ∑ _k : κ, ∑ j : Fin n, ∑ τ, ∑ i, c * b τ i j := by
        rw [Fintype.sum_prod_type]
    _ = Fintype.card κ * (c * ∑ j, ∑ τ, ∑ i, b τ i j) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Finset.mul_sum]
    _ = Fintype.card κ * c * ∑ τ, ∑ i, ∑ j, b τ i j := by
        rw [mul_assoc]
        congr 2
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_comm]
    _ ≤ (1 + Fintype.card κ * c) * ∑ τ, ∑ i, ∑ j, b τ i j := by nlinarith

end GlobalTheory.Proof.GNorm

namespace GlobalTheory

theorem tGnorm : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E), ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∀ ξ : Matrix (Fin m) (Fin n) D.host.E, ∑ p : κ × Fin n, (∑ τ, ‖tauE D τ ((T * ξ) p.1 p.2)‖) / s p.1 ≤ C * ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖ := by
  intro D κ _ _ m n T
  exact GlobalTheory.Proof.GNorm.gnorm_gen m n (tauE D) T

end GlobalTheory
