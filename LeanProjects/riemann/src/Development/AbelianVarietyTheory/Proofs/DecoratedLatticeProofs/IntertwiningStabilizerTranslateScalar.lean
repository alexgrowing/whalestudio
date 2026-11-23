import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.IkStab

variable {D : D7}

def mulLeft {t : ℕ} (n : ℕ) (α : GL (Fin t) (AE D)) : Mx D t n ≃ₜ+ Mx D t n where
  toFun x := α.1 ⬝ x
  invFun x := (α⁻¹).1 ⬝ x
  left_inv x := by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv x := by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _
  continuous_toFun := continuous_const.matrix_mul continuous_id
  continuous_invFun := continuous_const.matrix_mul continuous_id

theorem exists_valuation_adapted_index {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {p : GA D T} (hp : p ∈ stab d) :
    ∃ (β : Mx D t T'.rank) (g : GA D T'), mt T p ⬝ d.j0 = d.jX ⬝ β + d.j0 ⬝ mt T' g := by
  obtain ⟨α, hα⟩ := hp
  have hu := mt_unitary T p
  have h1 : adj (mt T p ⬝ d.jX) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.wittDecomp_gram_X_anisotropic]
  have h2 : d.pY ⬝ (mt T p ⬝ d.j0) = 0 := by
    rw [hα, adj_mul, Matrix.mul_assoc] at h1
    have h3 := congrArg (fun z : Mx D t T'.rank => adj (α⁻¹).1 ⬝ z) h1
    simp only [← Matrix.mul_assoc (adj (α⁻¹).1), ← adj_mul, Units.mul_inv, adj_one, Matrix.one_mul,
      Matrix.mul_zero] at h3
    rw [d.pY_eq, Matrix.mul_assoc, h3]
  have h4 : mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt T p ⬝ d.j0)) := by
    conv_lhs => rw [← Matrix.one_mul (mt T p ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h2, Matrix.mul_zero, add_zero]
  have h5 : adj (mt T p ⬝ d.j0) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) = gA T' := by
    rw [adj_mul, Matrix.mul_assoc, cancel₃ hu, d.gram_00]
  generalize d.pX ⬝ (mt T p ⬝ d.j0) = β at h4
  generalize d.p0 ⬝ (mt T p ⬝ d.j0) = g at h4
  rw [h4] at h5
  simp only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₃ d.gram_XX,
    cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero] at h5
  exact ⟨β, ofMat T' g h5, h4⟩

end GlobalTheory.RegSch.IkStab

end
