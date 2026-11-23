import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.cocycle_rat_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  intro l _ n _ _ K r σ ρ₀ p c c₀ hint hc0 hc g h
  set f : ℚ_[l] →+* ↥(MaximalUnramifiedExtension l) := algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) with hf
  set P : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hP

  have hC : (fun x : n × Fin r => fr l x.2 (c (g * h) x.1)) =
      (fun x : n × Fin r => fr l x.2 (c g x.1)) +
        (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).mulVec
          (fun x : n × Fin r => fr l x.2 (c h x.1)) := by
    funext ⟨i, m⟩
    simp only [hc, Pi.add_apply, map_add, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.blockDiagonal_apply, Matrix.map_apply, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  have key : P.mulVec (fun x => f (c₀ (g * h) x)) =
      P.mulVec (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    rw [hc0, hC, ← hc0 g, ← hc0 h, Matrix.mulVec_mulVec, ← hint g]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    congr 1
    funext x
    simp only [Pi.add_apply, map_add]
    congr 1
    rw [RingHom.map_mulVec]
    rfl
  have inj : (fun x => f (c₀ (g * h) x)) =
      (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    have := congrArg (fun v => ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec v) key
    simp only [hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
    exact this
  funext x
  exact f.injective (congrFun inj x)
