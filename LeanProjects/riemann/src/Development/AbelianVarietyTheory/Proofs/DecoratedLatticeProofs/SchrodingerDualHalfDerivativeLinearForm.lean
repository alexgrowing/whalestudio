import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtMixedModelSourceDualLineLinearForm
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

theorem gramAt_conjTranspose {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, HSpace.gram]
  rw [← h1]
  exact (NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem conj_complexPlace_traceZero_element (D : D7) (τ : D.what₂.Tau) : conj (tauE D τ D.host.xi0) = -tauE D τ D.host.xi0 := by
  have hcm := D.host.isCMField_hostE
  rw [← NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _]
  have h := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  change tauE D τ (star D.host.xi0) = _
  rw [h, map_neg]

theorem re_trace_swap {n m : ℕ} (c : ℂ) (hc : conj c = -c) (G : Matrix (Fin n) (Fin n) ℂ) (hG : Gᴴ = G)
    (X Y : Matrix (Fin n) (Fin m) ℂ) :
    (c * Matrix.trace (Xᴴ * G * Y)).re = -(c * Matrix.trace (Yᴴ * G * X)).re := by
  have ht : Matrix.trace (Xᴴ * G * Y) = conj (Matrix.trace (Yᴴ * G * X)) := by
    have h := Matrix.trace_conjTranspose (Yᴴ * G * X)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      ← Matrix.mul_assoc] at h
    exact h
  rw [ht]
  have hre : c.re = 0 := by
    have := congrArg Complex.re hc
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hre]
  ring

end GlobalTheory.StdUnn

open GlobalTheory.Unf in

theorem GlobalTheory.StdUnn.sch_dRho_dualHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (Y * (dblDec A).qY.map (tauE D τ)) f) x = -(2 * Real.pi * Complex.I) * ((2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re : ℝ) : ℂ) * sch ψ A B ν 𝓨 f x := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν f hf τ Y x
  let d := dblDec A
  let v : VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt (m := B.rank) (n := A.rank) hθ τ Y
  have hq : compAt θ τ d.pY = d.qY.map (tauE D τ) := by
    ext i j
    exact (hθ τ).1 _
  have hL' : IsLineAt θ τ (Y * compAt θ τ d.pY) ((d.extY B).comp (lineAt θ τ Y)) := by
    refine ⟨?_, fun t => ?_, fun t τ' => ?_⟩
    · exact hL.1.matrix_mul continuous_const
    · show ((lineAt θ τ Y t) * d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
    · show compAt θ τ' ((lineAt θ τ Y t) * d.pY) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2 t τ']
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  have hline := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _)
  have hline' : ∀ t, d.extY B (lineAt θ τ Y t) = lineAt θ τ (Y * compAt θ τ d.pY) t := fun t => by
    rw [← hline]; rfl
  have hder := GlobalTheory.Unf.hasDerivAt_mixS_extY D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank d v f hf
    (lineAt θ τ Y) hL.1 hL.2.1 x 0
  have hfun : (fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (d.extY B (lineAt θ τ Y t)) f p) 0) =
      dRho (heisO ψ (dblSp A) B) θ τ (Y * compAt θ τ d.pY) f := by
    funext p
    simp only [hline']
    rfl
  rw [hfun] at hder
  have hphase : ∀ t : ℝ, ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
      Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) := by
    intro t
    have e := GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ (GlobalTheory.Size.posSp D A.rank) B x τ Y t
    have e2 : symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t)) =
        symplOH (GlobalTheory.Size.posSp D A.rank) B x (lineAt θ τ Y t) := by
      rw [d.symplOH_extX_extY]
      exact (congrArg (trHalf D) (hO_posSp D B A.rank x _)).symm
    have e3 : ψ (symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
        Complex.exp ((Real.pi * Complex.I) *
          ((t * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℝ) : ℂ)) := by
      rw [e2]; exact e
    rw [symplO_eq_two_half, AddChar.map_add_eq_mul, e3, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun2 : (fun t : ℝ => ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) *
      d.mixS B ψ v.μ v.𝓕 f x 0) =
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) *
          d.mixS B ψ v.μ v.𝓕 f x 0 :=
    funext fun t => by rw [hphase]
  rw [hfun2] at hder
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) with ha_def
  set M := d.mixS B ψ v.μ v.𝓕 f x 0 with hM
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * t) * M)
      ((2 * Real.pi * Complex.I * (a : ℂ)) * M) 0 := by
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * u) * M)
        (Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * ((0:ℝ):ℂ)) * ((2 * Real.pi * Complex.I * (a : ℂ)) * 1) * M)
        ((0:ℝ):ℂ) :=
      (((hasDerivAt_id _).const_mul (2 * Real.pi * Complex.I * (a : ℂ))).cexp).mul_const M
    have h3 := h2.comp_ofReal
    refine h3.congr_deriv ?_
    simp
  have heq := hder.unique hexp
  have ha : a = -(2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re) := by
    rw [ha_def]
    refine (GlobalTheory.Unf.symplAt_posSp D B A.rank τ Y (compAt θ τ x)).trans ?_
    rw [GlobalTheory.StdUnn.re_trace_swap _ (GlobalTheory.StdUnn.conj_complexPlace_traceZero_element D τ) _ (GlobalTheory.StdUnn.gramAt_conjTranspose B τ)]
    ring
  show d.mixS B ψ ν 𝓨 _ x 0 = _ * d.mixS B ψ ν 𝓨 f x 0
  rw [← hq]
  change d.mixS B ψ v.μ v.𝓕 _ x 0 = _ * M
  rw [heq, ha]
  push_cast
  ring

end
