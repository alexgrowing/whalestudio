import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtMixedModelSourceDualLineLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf

theorem gram_posSp_one (D : D7) (n : ℕ) : (GlobalTheory.Size.posSp D n).gram = 1 := by
  funext i j
  refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
  change (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
  by_cases h : i = j <;> simp [h, Examples₂.sgn]

theorem giA_posSp (D : D7) (n : ℕ) : giA (GlobalTheory.Size.posSp D n) = 1 := by
  rw [giA, gram_posSp_one, inv_one]
  unfold rat
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem hO_posSp (D : D7) (T : HSp D) (ρ : ℕ) (x y : Mx D T.rank ρ) :
    hO (GlobalTheory.Size.posSp D ρ) T x y = pairS T x y := by
  refine (hO_eq_trace (GlobalTheory.Size.posSp D ρ) T x y).trans ?_
  have h1 := giA_posSp D ρ
  unfold pairS
  erw [h1, Matrix.one_mul]
  rfl

theorem symplO_eq_two_half {D : D7} (S T : HSp D) (x y : WO S T) :
    symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add]
  norm_num

theorem symplAt_posSp (D : D7) (T : HSp D) (ρ : ℕ) (τ : D.what₂.Tau) (z X : Matrix (Fin T.rank) (Fin ρ) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z X = 2 * (tauE D τ D.host.xi0 * (Xᴴ * gramAt D T τ * z).trace).re := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
  have hg : (gramAt D (GlobalTheory.Size.posSp D ρ) τ)⁻¹ = 1 := by rw [GlobalTheory.Size.gramAt_posSp, inv_one]
  simp only [hg, Matrix.one_mul]
  rfl

end GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem norm_mixS_dRho_ge : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin ρ) ℂ), ∃ Z : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, |2 * (tauE D τ D.host.xi0 * ((compAt θ τ x)ᴴ * gramAt D T τ * z).trace).re| * ‖d.mixS T ψ v.μ v.𝓕 f x w‖ ≤ ‖d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ τ Z f) x w‖ := by
  intro D ψ hψ θ hθ S S₀ T ρ d v τ z
  refine ⟨z * compAt θ τ d.pY, ?_⟩
  intro f hf x w
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt (m := T.rank) (n := ρ) hθ τ z
  have hL' : IsLineAt θ τ (z * compAt θ τ d.pY) ((d.extY T).comp (lineAt θ τ z)) := by
    refine ⟨?_, fun t => ?_, fun t τ' => ?_⟩
    · exact hL.1.matrix_mul continuous_const
    · show ((lineAt θ τ z t) * d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
    · show compAt θ τ' ((lineAt θ τ z t) * d.pY) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2 t τ']
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  have hline := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _)
  have hline' : ∀ t, d.extY T (lineAt θ τ z t) = lineAt θ τ (z * compAt θ τ d.pY) t := fun t => by
    rw [← hline]; rfl
  have hder := GlobalTheory.T.hasDerivAt_mixedModelSource_dualLine_linearForm D ψ hψ θ hθ S S₀ T ρ d v f hf (lineAt θ τ z) hL.1 hL.2.1 x w
  have hfun : (fun p => deriv (fun t : ℝ => heisO ψ S T (d.extY T (lineAt θ τ z t)) f p) 0) =
      dRho (heisO ψ S T) θ τ (z * compAt θ τ d.pY) f := by
    funext p
    simp only [hline']
    rfl
  rw [hfun] at hder
  have hphase : ∀ t : ℝ, ψ (symplO S T (d.extX T x) (d.extY T (lineAt θ τ z t))) =
      Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) : ℂ)) * t) := by
    intro t
    have e := GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ (GlobalTheory.Size.posSp D ρ) T x τ z t
    have e2 : symplOH S T (d.extX T x) (d.extY T (lineAt θ τ z t)) =
        symplOH (GlobalTheory.Size.posSp D ρ) T x (lineAt θ τ z t) := by
      rw [d.symplOH_extX_extY]
      exact (congrArg (trHalf D) (hO_posSp D T ρ x _)).symm
    have e3 : ψ (symplOH S T (d.extX T x) (d.extY T (lineAt θ τ z t))) =
        Complex.exp ((Real.pi * Complex.I) *
          ((t * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) : ℝ) : ℂ)) := by
      rw [e2]; exact e
    rw [symplO_eq_two_half, AddChar.map_add_eq_mul, e3, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun2 : (fun t : ℝ => ψ (symplO S T (d.extX T x) (d.extY T (lineAt θ τ z t))) * d.mixS T ψ v.μ v.𝓕 f x w) =
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) : ℂ)) * t) * d.mixS T ψ v.μ v.𝓕 f x w :=
    funext fun t => by rw [hphase]
  rw [hfun2] at hder
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) T τ z (compAt θ τ x) with ha_def
  set M := d.mixS T ψ v.μ v.𝓕 f x w with hM
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
  rw [heq]
  have ha : 2 * (tauE D τ D.host.xi0 * ((compAt θ τ x)ᴴ * gramAt D T τ * z).trace).re = a := by
    rw [ha_def]
    exact (symplAt_posSp D T ρ τ z (compAt θ τ x)).symm
  rw [ha, norm_mul]
  have hn : ‖2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)‖ = 2 * Real.pi * |a| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hn]
  have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h0 : 0 ≤ |a| * ‖M‖ := by positivity
  nlinarith

end GlobalTheory.Unf
