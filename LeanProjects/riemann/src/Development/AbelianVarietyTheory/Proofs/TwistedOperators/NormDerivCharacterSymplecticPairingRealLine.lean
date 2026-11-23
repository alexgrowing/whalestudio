import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatSum

theorem norm_deriv_psi_symplO_lineAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T), ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ = 2 * Real.pi * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w)| := by
  intro D ψ hψ θ hθ S T τ z w
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ w) with ha
  have h2 : ∀ x y : WO S T, symplO S T x y = symplOH S T x y + symplOH S T x y := by
    intro x y
    unfold symplOH
    rw [← add_mul, ← map_add]
    norm_num
  have hphase : ∀ t : ℝ, ψ (symplO S T (lineAt θ τ z t) w) =
      Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)) := by
    intro t
    rw [GlobalTheory.Asc.symplO_swap, h2, AddChar.map_neg_eq_inv, AddChar.map_add_eq_mul,
      GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ S T w τ z t, ← Complex.exp_add, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hfun : (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) =
      fun t : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)) := funext hphase
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * (t : ℂ)))
      (-(2 * Real.pi * Complex.I * (a : ℂ))) 0 := by
    have h3 : HasDerivAt (fun u : ℂ => Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * u))
        (Complex.exp ((-(2 * Real.pi * Complex.I * (a : ℂ))) * ((0:ℝ):ℂ)) * ((-(2 * Real.pi * Complex.I * (a : ℂ))) * 1))
        ((0:ℝ):ℂ) :=
      ((hasDerivAt_id _).const_mul (-(2 * Real.pi * Complex.I * (a : ℂ)))).cexp
    refine h3.comp_ofReal.congr_deriv ?_
    simp
  rw [hfun, hd.deriv, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simp

end GlobalTheory.LatSum
