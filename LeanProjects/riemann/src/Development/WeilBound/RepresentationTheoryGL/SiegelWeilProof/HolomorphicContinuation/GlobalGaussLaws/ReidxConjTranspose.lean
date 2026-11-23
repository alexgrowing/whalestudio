import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousAtMN

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open EmbP
open Formalism.IndefR.Eqv (psiT thetaC eq_thetaC)

variable {D : D7} {n : ℕ}

theorem reidx_mul (a b : M2 n) : reidx (a * b) = reidx a * reidx b := by
  simp only [reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : reidx (1 : M2 n) = 1 := Matrix.submatrix_one_equiv _

theorem reidx_conjTranspose (a : M2 n) : reidx aᴴ = (reidx a)ᴴ := by
  simp only [reidx, Matrix.conjTranspose_submatrix]

theorem continuous_reidx : Continuous (fun a : M2 n => reidx a) :=
  continuous_id.matrix_submatrix _ _

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = reidx (JJ n) := by
  ext i j
  simp only [Jst, blk4, reidx, JJ, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

theorem mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

theorem mR_one : mR (1 : GR n) = 1 := rfl

theorem mR_mul_inv (a : GR n) : mR a * mR a⁻¹ = 1 := by
  rw [← mR_mul, mul_inv_cancel, mR_one]

theorem mR_inv_mul (a : GR n) : mR a⁻¹ * mR a = 1 := by
  rw [← mR_mul, inv_mul_cancel, mR_one]

theorem reidx_unitary (τ : D.what₂.Tau) (y : GR n) :
    (reidx (mR y))ᴴ * (Jst D n).map (tauE D τ) * reidx (mR y) = (Jst D n).map (tauE D τ) := by
  have h : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  rw [Jst_map, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, h]

def iotaF (τ : D.what₂.Tau) (y : GR n) : G D n :=
  (⟨⟨atMN D τ (reidx (mR y)), atMN D τ (reidx (mR y⁻¹)),
      by rw [← atMN_mul, ← reidx_mul, mR_mul_inv, reidx_one, atMN_one],
      by rw [← atMN_mul, ← reidx_mul, mR_inv_mul, reidx_one, atMN_one]⟩,
    atMN_unitary D τ (Jst D n) _ (reidx_unitary τ y)⟩ : HR (AF D.host.F) D.sp.cm.sig (Jst D n))

theorem mat_iotaF (τ : D.what₂.Tau) (y : GR n) : mat (iotaF τ y) = atMN D τ (reidx (mR y)) := rfl

def iota (τ : D.what₂.Tau) : GR n →* G D n where
  toFun := iotaF τ
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR 1)) = 1
    rw [mR_one, reidx_one, atMN_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    show atMN D τ (reidx (mR (a * b))) = atMN D τ (reidx (mR a)) * atMN D τ (reidx (mR b))
    rw [mR_mul, reidx_mul, atMN_mul]

theorem continuous_iota (τ : D.what₂.Tau) : Continuous (iota (D := D) (n := n) τ) := by
  have hm : Continuous fun y : GR n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun y : GR n => mR y⁻¹ := hm.comp continuous_inv
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hm)
  · exact (continuous_atMN D τ).comp (continuous_reidx.comp hmi)

theorem sEmb : SEmb := by
  intro D n θ τ hθ
  obtain rfl := eq_thetaC D hθ
  refine ⟨iota τ, continuous_iota τ, fun y => ⟨?_, fun τ' hτ' => ?_, ?_⟩⟩
  · have e := psi_atMN D τ τ (reidx (mR y))
    rw [if_pos rfl] at e
    exact e
  · have e := psi_atMN D τ τ' (reidx (mR y))
    rw [if_neg hτ'] at e
    exact e
  · exact fin_atMN D τ (reidx (mR y))

end PositivityTheory.Rg.Sw.Glob
