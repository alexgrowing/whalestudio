import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawD
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

theorem fromBlocks_of (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    mR y = Matrix.fromBlocks (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ 0 (mR y).toBlocks₂₂ := by
  rw [← hy]
  exact (Matrix.fromBlocks_toBlocks _).symm

theorem blocks_ad (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    ((mR y).toBlocks₁₁)ᴴ * (mR y).toBlocks₂₂ = 1 := by
  have hG : (mR y)ᴴ * PositivityTheory.Rg.Sw.JJ n * mR y = PositivityTheory.Rg.Sw.JJ n := y.2
  have hJ : PositivityTheory.Rg.Sw.JJ n = Matrix.fromBlocks 0 1 (-1) 0 := rfl
  rw [hJ, fromBlocks_of y hy, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hG
  have h12 := hG.2.1
  simpa using h12

theorem det_rel (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    star ((mR y).toBlocks₁₁).det * ((mR y).toBlocks₂₂).det = 1 := by
  have h := congrArg Matrix.det (blocks_ad y hy)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact h

theorem det_ne (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) : ((mR y).toBlocks₁₁).det ≠ 0 := by
  intro h0
  have h := det_rel y hy
  rw [h0, star_zero, zero_mul] at h
  exact zero_ne_one h

def aOf (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) : GL (Fin n) ℂ :=
  ⟨(mR y).toBlocks₁₁, ((mR y).toBlocks₁₁)⁻¹, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne y hy)),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne y hy))⟩

theorem aOf_val (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) : (aOf y hy).1 = (mR y).toBlocks₁₁ := rfl

theorem decomp (y : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    mR ((mOf (aOf y hy))⁻¹ * y) = Matrix.fromBlocks 1 (((mR y).toBlocks₁₁)⁻¹ * (mR y).toBlocks₁₂) 0 1 := by
  have hmul : mR ((mOf (aOf y hy))⁻¹ * y) = mR (mOf (aOf y hy))⁻¹ * mR y := rfl
  have hinv : (((aOf y hy)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = ((mR y).toBlocks₁₁)⁻¹ := rfl
  have hval : ((aOf y hy : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (mR y).toBlocks₁₁ := rfl
  rw [hmul, mR_mOf_inv, hinv, hval]
  conv_lhs => rw [fromBlocks_of y hy]
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (det_ne y hy)), blocks_ad y hy]

set_option maxHeartbeats 400000 in
theorem glob_law {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → NNReal}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)} {τ : D.what₂.Tau}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : PositivityTheory.Rg.Sw.GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : PositivityTheory.Rg.Sw.GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocOp ω l s τ fr ι L) {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (P : PX V.rank n)
    (y g : PositivityTheory.Rg.Sw.GR n) (hy : (mR y).toBlocks₂₁ = 0) :
    sLd L (cLoc l τ) P (y * g) =
      (χ (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy))) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det (unitAt hσ τ (aOf y hy)))) ((V.rank : ℂ) / 2) *
        sLd L (cLoc l τ) P g := by
  obtain ⟨-, -, -, -, -, hω, -, -, -, -, -, -, -, hι, -⟩ := hC
  obtain ⟨hlevi, hunip, -⟩ := hω
  have hphase : ∀ b : Formalism.IndefR.Datum.Mx D n n,
      ψ (GlobalTheory.StdUnn.halfTr ((b * GlobalTheory.StdUnn.inner V (0 : Formalism.IndefR.Datum.Mx D V.rank n) 0).trace)) = 1 := by
    intro b
    have hin : GlobalTheory.StdUnn.inner V (0 : Formalism.IndefR.Datum.Mx D V.rank n) 0 = 0 := by
      show GlobalTheory.MixModel.adj 0 * (GlobalTheory.MixModel.gA V * 0) = 0
      rw [Matrix.mul_zero, Matrix.mul_zero]
    have htr : GlobalTheory.StdUnn.trA (0 : Formalism.L2.Theta.AE D) = 0 := by
      show Algebra.trace _ _ (0 : Formalism.L2.Theta.AE D) = 0
      exact map_zero _
    have hh : GlobalTheory.StdUnn.halfTr (0 : Formalism.L2.Theta.AE D) = 0 := by
      show _ * GlobalTheory.StdUnn.trA (0 : Formalism.L2.Theta.AE D) = 0
      rw [htr, mul_zero]
    rw [hin, Matrix.mul_zero, Matrix.trace_zero, hh, AddChar.map_zero_eq_one]
  have hL0 : ∀ z : PositivityTheory.Rg.Sw.GR n,
      ((ω (ι z)) (PositivityTheory.Rg.Sw.Glob.phiS θ τ fr (PositivityTheory.Rg.Sw.Glob.cLoc l τ)
        (PositivityTheory.Rg.Sw.Glob.LocLawH.psi0 θ V n l s τ) P) : Formalism.IndefR.Datum.Mx D V.rank n → ℂ) 0 =
        L z (PositivityTheory.Rg.Sw.Glob.fP (PositivityTheory.Rg.Sw.Glob.cLoc l τ) P) 0 := by
    intro z
    rw [hL z _ (PositivityTheory.Rg.Sw.Glob.LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ) P, PositivityTheory.Rg.Sw.Glob.LocLawH.tens_zero,
      PositivityTheory.Rg.Sw.Glob.LocLawH.cmTraceAdditiveCharacter_zero, mul_one]
  have hsplit : mOf (aOf y hy) * ((mOf (aOf y hy))⁻¹ * y * g) = y * g := by
    rw [← mul_assoc, mul_inv_cancel_left]
  have hm := PositivityTheory.Rg.Sw.Glob.LocLawH.mat_mOf hσ hι (aOf y hy)
  have hn := PositivityTheory.Rg.Sw.Glob.LocLawH.mat_nOf hσ hι ((mOf (aOf y hy))⁻¹ * y) _ (decomp y hy)
  have key := hL0 (y * g)
  rw [← hsplit, map_mul ι (mOf (aOf y hy)) ((mOf (aOf y hy))⁻¹ * y * g), map_mul ι ((mOf (aOf y hy))⁻¹ * y) g,
    map_mul ω, map_mul ω, Module.End.mul_apply, Module.End.mul_apply, hlevi _ _ hm, Matrix.zero_mul,
    hunip _ _ hn, hphase, one_mul, hL0 g, hsplit] at key
  show L (y * g) (PositivityTheory.Rg.Sw.Glob.fP (PositivityTheory.Rg.Sw.Glob.cLoc l τ) P) 0 =
    _ * _ * L g (PositivityTheory.Rg.Sw.Glob.fP (PositivityTheory.Rg.Sw.Glob.cLoc l τ) P) 0
  exact key.symm

end PositivityTheory.Rg.Sw.Glob.LocLawH
