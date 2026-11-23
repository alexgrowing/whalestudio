import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilFockAniso
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.NormAdelic

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

def fockStab (X : GlobalTheory.NormDict.Data P) : Subgroup (GA D X.A) where
  carrier := {g | ∀ T, X.om (g, 1) (X.fock T) = X.fock T}
  mul_mem' := by
    intro a b ha hb T
    have e : ((a * b, (1 : GA D X.B)) : GA D X.A × GA D X.B) = (a, 1) * (b, 1) := by simp
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [e, map_mul, Module.End.mul_apply, hb T, ha T]
  one_mem' := by
    intro T
    rw [show ((1 : GA D X.A), (1 : GA D X.B)) = 1 from rfl, map_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha T
    simp only [Set.mem_setOf_eq] at ha ⊢
    have e : ((a⁻¹, (1 : GA D X.B)) : GA D X.A × GA D X.B) * (a, 1) = 1 := by simp
    calc X.om (a⁻¹, 1) (X.fock T) = X.om (a⁻¹, 1) (X.om (a, 1) (X.fock T)) := by rw [ha T]
      _ = X.fock T := by rw [← Module.End.mul_apply, ← map_mul, e, map_one, Module.End.one_apply]

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
