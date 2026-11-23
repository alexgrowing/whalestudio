import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.RankZeroVac

variable {D : D7}

theorem incA_tmul' (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem continuous_wittExtendByZero : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const

theorem heisenbergOperator_wittExtendByZero (ψ : AddChar (AF D.host.F) ℂ) (u : WO W₀ T) (f : WO W T → ℂ) :
    heisO ψ W₀ T u (fun w => f (d.ext0 T w)) = fun w => heisO ψ W T (d.ext0 T u) f (d.ext0 T w) := by
  funext w
  simp only [heisO, map_add, d.wittDecomp_sympl_extAnisotropic_extAnisotropic]

theorem isThetaFunction_comp_wittExtendByZero {ψ : AddChar (AF D.host.F) ℂ} {f : WO W T → ℂ} (hf : IsThetaFunO ψ W T f) :
    IsThetaFunO ψ W₀ T (fun w => f (d.ext0 T w)) where
  quasi γ w := by
    have h := hf.quasi (γ * d.q0) (d.ext0 T w)
    have hr : ratW T W (γ * d.q0) = d.ext0 T (ratW T W₀ γ) := by
      rw [ratW_eq, ratW_eq, rat_mul, d.matrixExtendByZero_apply]; rfl
    rw [hr, d.wittDecomp_sympl_extAnisotropic_extAnisotropic] at h
    simp only [map_add]
    exact h
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (d.ext0 T), hU.preimage (continuous_wittExtendByZero d T), fun u hu hinf => ?_⟩
    rw [heisenbergOperator_wittExtendByZero]
    have h0 : (d.ext0 T u).map (infPart D) = 0 := by
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hinf, Matrix.zero_mul]
    rw [hfix _ hu h0]
  cont := hf.cont.comp (continuous_wittExtendByZero d T)
  smooth k L hL hLf w := by
    have h := hf.smooth k ((d.ext0 T).comp L) ((continuous_wittExtendByZero d T).comp hL) (fun t => by
      show (d.ext0 T (L t)).map (finPart D) = 0
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hLf t, Matrix.zero_mul]) (d.ext0 T w)
    simpa only [AddMonoidHom.comp_apply, map_add] using h

theorem isHalf_wittHyperbolicExtendByZero_apply {e : AE D} {u : WO W₀ T} (h : IsHalf e u) : IsHalf e (d.ext0 T u) := by
  intro i j
  have hl : ∀ l, e * ((u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j) =
      (u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j := fun l => by rw [← mul_assoc, h i l]
  rw [d.matrixExtendByZero_apply, Matrix.mul_apply]
  show e * ∑ l, _ = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => hl l

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem wittDecomposition_gram_projection_identity (s : Fin W₀.rank → D.host.E) (j : Fin W.rank) :
    ∑ l, (∑ k, star (s k) * W₀.gram k l) * d.q0 l j = ∑ m, star ((Matrix.mulVec d.i₀ s) m) * W.gram m j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) W₀.gram) d.q0 = Matrix.vecMul (star (Matrix.mulVec d.i₀ s)) W.gram := by
    rw [Matrix.vecMul_vecMul, HypDec.q0, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det W₀),
      Matrix.one_mul, ← Matrix.vecMul_vecMul, Matrix.star_mulVec]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

end

end GlobalTheory.RankZeroVac
