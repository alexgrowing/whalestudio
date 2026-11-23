import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.ZcDer

open GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift (dOmT)

theorem conjAt_rel {D : D7} (V : HSp D) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    gramAt D V τ * Formalism.L2.Theta.conjAt V τ Z = -(Zᴴ * gramAt D V τ) ∧
      (Formalism.L2.Theta.conjAt V τ Z)ᴴ * gramAt D V τ = -(gramAt D V τ * Z) := by
  have h1 : gramAt D V τ * Formalism.L2.Theta.conjAt V τ Z = -(Zᴴ * gramAt D V τ) := by
    unfold Formalism.L2.Theta.conjAt
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ), Matrix.one_mul]
  refine ⟨h1, ?_⟩
  have h2 := congrArg Matrix.conjTranspose h1
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, GlobalTheory.SmoothForms.RealPts.gramAt_herm] at h2

theorem re_mem {D : D7} (V : HSp D) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / 2 : ℂ) • (Z + Formalism.L2.Theta.conjAt V τ Z) ∈ lieAt V τ := by
  obtain ⟨a, b⟩ := conjAt_rel V τ Z
  show _ + _ = _
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_add, Matrix.add_mul,
    Matrix.mul_add, a, b]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  simp

theorem im_mem {D : D7} (V : HSp D) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / (2 * Complex.I)) • (Z - Formalism.L2.Theta.conjAt V τ Z) ∈ lieAt V τ := by
  obtain ⟨a, b⟩ := conjAt_rel V τ Z
  show _ + _ = _
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_sub, Matrix.sub_mul,
    Matrix.mul_sub, a, b]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [this, sub_neg_eq_add, sub_neg_eq_add, add_comm (Zᴴ * gramAt D V τ), neg_smul, neg_add_cancel]

theorem hasDerivAt_dOmT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) :
    (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (dOmT θ om τ X f)) ∧
    (∀ f, IsThetaFunO ψ S T f → ∀ g h w,
      HasDerivAt (fun t : ℝ => om (g, h * oneP θ T τ X t) f w) (om (g, h) (dOmT θ om τ X f) w) 0) ∧
    (∀ f, IsThetaFunO ψ S T f → ∀ w,
      HasDerivAt (fun t : ℝ => om (1, oneP θ T τ X t) f w) (dOmT θ om τ X f w) 0) := by
  obtain ⟨ht, hd⟩ := GlobalTheory.Chain.LiftReg.tame_dOmT hθ hω hX
  have h2 : ∀ f, IsThetaFunO ψ S T f → ∀ g h w,
      HasDerivAt (fun t : ℝ => om (g, h * oneP θ T τ X t) f w) (om (g, h) (dOmT θ om τ X f) w) 0 := by
    intro f hf g h w
    have := hd f hf (g, h) w
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  refine ⟨fun f hf => ht.theta hf, h2, fun f hf w => ?_⟩
  have := h2 f hf 1 1 w
  simp only [one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at this
  exact this

theorem dOmT_add {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    dOmT θ om τ X (f + f') = dOmT θ om τ X f + dOmT θ om τ X f' := by
  obtain ⟨-, -, hD⟩ := hasDerivAt_dOmT hθ hω hX
  funext w
  have h1 := (hD f hf w).add (hD f' hf' w)
  have h2 := hD (f + f') ((GlobalTheory.RealWeil.thetaSub ψ S T).add_mem hf hf') w
  have e : (fun t : ℝ => om (1, oneP θ T τ X t) (f + f') w) =
      fun t => om (1, oneP θ T τ X t) f w + om (1, oneP θ T τ X t) f' w := by
    funext t
    simp only [map_add, Pi.add_apply]
  rw [e] at h2
  exact h2.unique h1

theorem dOmT_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dOmT θ om τ X (c • f) = c • dOmT θ om τ X f := by
  obtain ⟨-, -, hD⟩ := hasDerivAt_dOmT hθ hω hX
  funext w
  have h1 := (hD f hf w).const_mul c
  have h2 := hD (c • f) ((GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c hf) w
  have e : (fun t : ℝ => om (1, oneP θ T τ X t) (c • f) w) = fun t => c * om (1, oneP θ T τ X t) f w := by
    funext t
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [e] at h2
  exact h2.unique h1

end GlobalTheory.Core.Rk.ZcDer

open GlobalTheory.Core.Rk.ZcDer in

theorem GlobalTheory.Core.Rk.ZcDer.rderC_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ), ∃ Dz : (WO S T → ℂ) → (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Dz f)) ∧ (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Dz (f + f') = Dz f + Dz f') ∧ (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Dz (c • f) = c • Dz f) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ g w, RderC θ T τ Z (fun h => om (g, h) f w) = fun h => om (g, h) (Dz f) w := by
  intro D ψ θ S T χS χT om hθ hω τ Z
  have hX := GlobalTheory.Core.Rk.ZcDer.re_mem T τ Z
  have hY := GlobalTheory.Core.Rk.ZcDer.im_mem T τ Z
  obtain ⟨tX, dX, -⟩ := hasDerivAt_dOmT hθ hω hX
  obtain ⟨tY, dY, -⟩ := hasDerivAt_dOmT hθ hω hY
  refine ⟨fun f => GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ om τ ((1 / 2 : ℂ) • (Z + Formalism.L2.Theta.conjAt T τ Z)) f +
      Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ om τ ((1 / (2 * Complex.I)) • (Z - Formalism.L2.Theta.conjAt T τ Z)) f,
    fun f hf => ?_, fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf g w => ?_⟩
  · exact (GlobalTheory.RealWeil.thetaSub ψ S T).add_mem (tX f hf) ((GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem _ (tY f hf))
  · beta_reduce
    rw [dOmT_add hθ hω hX hf hf', dOmT_add hθ hω hY hf hf', smul_add Complex.I]
    abel
  · beta_reduce
    rw [dOmT_smul hθ hω hX c hf, dOmT_smul hθ hω hY c hf, smul_add c, smul_comm Complex.I c]
  · funext h
    simp only [Formalism.L2.Theta.RderC, Formalism.L2.Theta.Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul]
    rw [(dX f hf g h w).deriv, (dY f hf g h w).deriv]

end
