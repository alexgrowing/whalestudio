import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSectionWeylElementEqSchrodingerIntegralStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.WeylFourier

variable {D : D7}

theorem extX_mul_weyl {A B : HSp D} {w : GA D (dblSp A)} {b c : AE D}
    (hX : mt (dblSp A) w ⬝ (dblDec A).jX = -(b • (dblDec A).jY))
    (hY : mt (dblSp A) w ⬝ (dblDec A).jY = c • (dblDec A).jX) (x : Mx D B.rank A.rank) :
    (dblDec A).extX B x ⬝ mt (dblSp A) w = (dblDec A).extY B (c • x) := by
  refine (dblDec A).mat_ext ?_ (Matrix.ext fun _ j => Fin.elim0 j) ?_
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hX, Matrix.mul_neg, Matrix.mul_smul]
    rw [(dblDec A).pX_jY, (dblDec A).pY_jX, Matrix.mul_zero, Matrix.mul_zero, smul_zero, neg_zero]
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hY, Matrix.mul_smul]
    rw [(dblDec A).pX_jX, (dblDec A).pY_jY, Matrix.mul_one, Matrix.mul_one]

theorem symplO_extX_extY_smul {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : AE D) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T y) (d.extY T (c • x)) =
      trA (incA D D.host.xi0 * cA D c * Matrix.trace (GlobalTheory.StdUnn.inner T x y)) := by
  have h := d.hO_ext T y 0 0 (c • x) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, Matrix.trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, adj_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc]
  rfl

theorem sch_weyl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ w : GA D (dblSp A), IsWeyl A w → mt (dblSp A) w ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) → mt (dblSp A) w ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x, sch ψ A B ν 𝓨 (omh (w, 1) f) x = ∫ y, sch ψ A B ν 𝓨 f y * ψ (trA (incA D (-D.host.xi0 / μ) * Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  intro D ψ A B χB omh hW ν 𝓨 hν μ hμ w hw hX hY f hf x
  set u : WO (dblSp A) B := (dblDec A).extY B (incA D μ⁻¹ • x) with hu
  have hact : actO (dblSp A) B w 1 u = (dblDec A).extX B x := by
    rw [actO_eq, mt_one, Matrix.one_mul, hu, ← extX_mul_weyl hX hY x, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  have hf₁ : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B u f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hW.std (dblSp A) B).1 u f hf
  have h1 : sch ψ A B ν 𝓨 (omh (w, 1) f) x = swSec A B omh ν 𝓨 (heisO ψ (dblSp A) B u f) w := by
    have h := congrFun (GlobalTheory.MixModel.Check.mixS_heis_extX (ψ := ψ) (dblDec A) ν 𝓨 (omh (w, 1) f) x 0) 0
    rw [zero_add, ← hact, ← hW.om_heis w 1 u f hf, mixS_dblDec_zero] at h
    exact h.symm
  rw [h1, GlobalTheory.T.siegelSection_weylElement_eq_schrodingerIntegral D ψ A B χB omh hW ν 𝓨 hν _ hf₁ w hw]
  refine congrArg _ (funext fun y => ?_)
  have hc : incA D D.host.xi0 * cA D (incA D μ⁻¹) = incA D (-D.host.xi0 / μ) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_inv₀, hμ.2, inv_neg, mul_neg, neg_div, div_eq_mul_inv]
  have h2 := GlobalTheory.MixModel.Check.mixS_heis_extY (dblDec A) hν hf (incA D μ⁻¹ • x) y 0
  rw [symplO_extX_extY_smul, hc, mul_comm] at h2
  exact h2

end GlobalTheory.StdUnn.WeylFourier

end
