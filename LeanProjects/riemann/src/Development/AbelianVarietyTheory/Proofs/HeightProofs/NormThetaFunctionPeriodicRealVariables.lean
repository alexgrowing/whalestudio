import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.ThetaPeriod

variable {D : D7}

def mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) : AF D.host.F →+ WA V W where
  toFun a := Matrix.of fun i j => a ⊗ₜ[D.host.F] γ i j
  map_zero' := by ext i j; exact TensorProduct.zero_tmul _ _
  map_add' x y := by ext i j; exact TensorProduct.add_tmul _ _ _

theorem continuous_mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    Continuous (mulRat V W γ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun a : AF D.host.F => mulRat V W γ a i j) =
      fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ i j : AE D) := by
    funext a
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
  rw [e]
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  exact Continuous.smul (M := AF D.host.F) (X := AE D) (f := fun a : AF D.host.F => a) continuous_id continuous_const

theorem mulRat_one (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    mulRat V W γ 1 = ratW V W γ := by
  ext i j; rfl

theorem ratW_nsmul (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (N : ℕ) :
    ratW V W (N • γ) = N • ratW V W γ := by
  ext i j
  exact (incA D).toAddMonoidHom.map_nsmul N (γ i j)

theorem norm_periodic (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (hU : ∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) →
      ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U)
    (V W : HSp D) (f : WA V W → ℂ) (hf : IsThetaFun ψ V W f) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨N, hN, hmem⟩ := hU (U.comap (mulRat V W γ)) (hUo.preimage (continuous_mulRat V W γ))
  refine ⟨N, hN, fun w => ?_⟩
  set u : WA V W := mulRat V W γ (pairA D.host.F 0 (N : Af D.host.F)) with hu
  set r : WA V W := mulRat V W γ (pairA D.host.F (N : Ainf D.host.F) 0) with hr
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hr0 : IsRealW V W r := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hsum : r + u = N • ratW V W γ := by
    rw [hr, hu, ← AddMonoidHom.map_add, ← mulRat_one, ← AddMonoidHom.map_nsmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (N : Ainf D.host.F) + 0 = N • (1 : Ainf D.host.F)
      rw [add_zero, nsmul_one]
    · show 0 + (N : Af D.host.F) = N • (1 : Af D.host.F)
      rw [zero_add, nsmul_one]
  have hpu : piW θ V W u = 0 := by
    funext τ i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu0 i) j
    show θ τ (infPart D (u i j)) = 0
    rw [this, RingHom.map_zero]
  have hi : iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)) = r := by
    rw [Nat.cast_smul_eq_nsmul, ← AddMonoidHom.map_nsmul, ← hsum, AddMonoidHom.map_add, hpu, add_zero,
      h.iota_pi hr0]
  have h1 : ∀ x, ‖f (x + u)‖ = ‖f x‖ := fun x => by
    have := congrFun (hUf u hmem hu0) x
    rw [← this, Heisenberg₂, norm_mul, hψ, one_mul]
  have h2 := congrArg norm (hf.quasi (N • γ) w)
  rw [norm_mul, hψ, one_mul, ratW_nsmul, ← hsum] at h2
  rw [hi, ← h1, ← h2, add_assoc, add_comm]

end GlobalTheory.FockCompare.ThetaPeriod

end
