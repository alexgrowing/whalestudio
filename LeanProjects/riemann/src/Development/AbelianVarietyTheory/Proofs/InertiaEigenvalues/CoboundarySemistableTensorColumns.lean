import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonCob

theorem coboundary_cols (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P) :
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  intro h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] (ι → Bst P) :=
    TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : ι → ℚ_[l]) (a : Bst P) (x : ι) => v x • a)
      (fun v w a => by funext x; simp [add_smul])
      (fun c v a => by funext x; simp [mul_smul])
      (fun v a a' => by funext x; simp [smul_add])
      (fun c v a => by funext x; simp [smul_comm c]))
  have hΦ : ∀ (v : ι → ℚ_[l]) (a : Bst P), Φ (v ⊗ₜ a) = fun x => v x • a := fun v a => by
    simp [Φ]
  have hst : ∀ (g : ↥(GK K)) (y : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
      Φ (stRep P (repOf ρ₀) g y) = ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (Φ y x)) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => funext x; simp [Matrix.mulVec, dotProduct]
    | tmul v a =>
      rw [stRep_tmul, repOf_apply, hΦ, hΦ]
      funext x
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
    | add y z hy hz =>
      rw [map_add, map_add, hy, hz, ← Matrix.mulVec_add]
      congr 1
      funext x
      simp
  refine ⟨Φ b, fun g => ?_⟩
  have := congrArg Φ (h g)
  rw [map_sub, hst, hΦ] at this
  rw [← this]
  funext x
  simp [Algebra.algebraMap_eq_smul_one]

end GlobalTheory.PMonCob
