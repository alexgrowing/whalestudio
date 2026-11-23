import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open GroundTheory.Automorphic.AutomorphicForm

omit [IsTotallyComplex E] in

theorem unipGL_eq_unip {r : ℕ} (X : UPos a r → Ad E) :
    (unipGL X : GL (Fin a) (Ad E)) = unip X :=
  Units.ext rfl

omit [IsTotallyComplex E] in
theorem isAddHaarMeasure_unipMeasure (r : ℕ) : (unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem ctFun_resQ_eq_zero {φ : GA E a → ℂ} (hφ : φ ∈ cuspCont E a) {r : ℕ} (h0 : 0 < r) (h1 : r < a)
    (y : normOneGL E a) : ctFun E a r (resQ φ) y = 0 := by
  obtain ⟨-, hl, -, hc⟩ := mem_cuspCont.1 hφ
  have h := hc r h0 h1 (unipMeasure E a r) (unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure r) isAddFundamentalDomain_unipFundamentalDomain (y : GA E a)
  unfold ctFun
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)) h
  exact (resQ_mk hl _).trans (congrArg φ (congrArg (· * (y : GA E a)) (unipGL_eq_unip X)))

theorem toLp_restrict_mem_cuspidalL2 (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ν : Measure (normOneGL E a)) [ν.IsHaarMeasure] (φ : GA E a → ℂ) (hφ : φ ∈ cuspCont E a)
    (h : MemLp (resQ φ) 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν)) :
    h.toLp (resQ φ) ∈ cuspidalL2 ν := by
  intro r h0 h1
  filter_upwards [ae_ctFun_congr ν r h.coeFn_toLp] with y hy
  exact hy.trans (ctFun_resQ_eq_zero hφ h0 h1 y)

end GlobalTheory.CompanionTheory.CuspTransfer
