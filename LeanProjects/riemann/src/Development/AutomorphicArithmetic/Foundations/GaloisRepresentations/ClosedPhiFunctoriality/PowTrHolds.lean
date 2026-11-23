import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapNormEqOfMapPowEq

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.powTr_holds :
    PowTr := by
  intro E Ω _ _ _ _ _ w A h x σ n
  have h1 : (x.charPol (σ ^ n)).roots = Multiset.map (fun y => y ^ n) (x.charPol σ).roots :=
    GlobalTheory.AboveL.eig_pow_of_rep x σ n
  show (Multiset.map (fun y => y ^ n) (x.charPol σ).roots).sum = _
  rw [← h1, Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic (IsAlgClosed.splits _)
    (x.charPol_monic _), neg_neg]
