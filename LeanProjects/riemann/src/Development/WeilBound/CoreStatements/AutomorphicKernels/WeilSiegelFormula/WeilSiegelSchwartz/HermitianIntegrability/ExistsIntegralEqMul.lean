import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.UntupTupOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem exists_integral_eq_mul {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V']
    (f : V → V') (g : V' → V) (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hc : Continuous f) (hc' : Continuous g)
    (ν : Measure V) (hν : ν.IsAddHaarMeasure) (μ : Measure V') (hμ : μ.IsAddHaarMeasure) :
    ∃ c : ℂ, ∀ u : V' → ℂ, ∫ x, u (f x) ∂ν = c * ∫ y, u y ∂μ := by
  let e : V ≃+ V' := { toFun := f, invFun := g, left_inv := h1, right_inv := h2, map_add' := hadd }
  haveI : (ν.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map ν hc hc'
  refine ⟨((Measure.addHaarScalarFactor (ν.map f) μ : ℝ) : ℂ), fun u => ?_⟩
  have h : ∫ y, u y ∂(ν.map f) = ∫ x, u (f x) ∂ν :=
    integral_map_equiv
      ({ toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' } : V ≃ₜ V').toMeasurableEquiv u
  rw [← h]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (ν.map f) μ]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem gramR_untup (V : HSp D) {r : ℕ} (y : Mx D V.rank r) :
    gramR (AF D.host.F) D.sp.cm.sig V.gram (untup y) = GlobalTheory.StdUnn.inner V y y := by
  ext a b
  simp only [gramR, untup, hR, Formalism.UG.hform, JR, GlobalTheory.StdUnn.inner, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = (cA D (y i a)) * (incA D (V.gram i j) * y j b)
  rw [mul_assoc]
  rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem starN_hermE (V : HSp D) {r : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank r))
    (hμ : μ.IsAddHaarMeasure) (dx : Measure (Fin r → Fin V.rank → AE D)) (hdx : dx.IsAddHaarMeasure) :
    ∃ c : ℂ, ∀ (Φ : (Fin r → Fin V.rank → AE D) → ℂ) (b : hermA D r),
      starN D.sp.cm.sig V.gram ψ dx Φ (hermE D r b) = c * Jt ψ V μ (fun y => Φ (untup y)) b := by
  obtain ⟨k1, k2, k3, -, -, -⟩ := lattice_Mx D V.rank r
  haveI : IsTopologicalAddGroup (Mx D V.rank r) := k1
  haveI : LocallyCompactSpace (Mx D V.rank r) := k2
  haveI : SecondCountableTopology (Mx D V.rank r) := k3
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  obtain ⟨j1, -, -, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI : BorelSpace (Fin V.rank → AE D) := Pi.borelSpace
  haveI : BorelSpace (Fin r → Fin V.rank → AE D) := Pi.borelSpace
  obtain ⟨c, hc⟩ := exists_integral_eq_mul (tupOf (D := D) (m := V.rank) (r := r)) untup untup_tupOf tupOf_untup
    (fun _ _ => rfl) (continuous_matrix fun i a => (continuous_apply i).comp (continuous_apply a))
    (continuous_pi fun a => continuous_pi fun i => continuous_id.matrix_elem i a) dx hdx μ hμ
  refine ⟨c, fun Φ b => ?_⟩
  unfold starN Jt
  rw [← hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hg := gramR_untup V (tupOf X)
  change Φ X * ψ (_ * Algebra.trace _ _
    (Matrix.trace (b.1 * gramR (AF D.host.F) D.sp.cm.sig V.gram (untup (tupOf X))))) = _
  rw [hg]
  rfl

end PositivityTheory.PfWsf.Hand.TupleUntupling
