import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeVectorOfGoodLevelRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalIsometriesInnerAutAdelicFrameIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesOddRankGapStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalMultiplicityEqDiscreteSeriesModelMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermitiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.MultEqTrace

def conjEquiv {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (Φ Φ₀ : G ≃* H) (b : G) (hb : ∀ g, Φ g = Φ₀ (b * g * b⁻¹)) :
    Representation.Equiv (σ.comp Φ.symm.toMonoidHom : Representation ℂ H W)
      (σ.comp Φ₀.symm.toMonoidHom : Representation ℂ H W) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (σ b) (σ b⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun h => by
      have e : Φ.symm h = b⁻¹ * Φ₀.symm h * b := by
        apply Φ.injective
        rw [Φ.apply_symm_apply, hb]
        simp [mul_assoc]
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, e]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group

theorem multEq_of_trCusp : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.GreenCuspidal → TRCusp → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  intro hRD hHC hDM hGC hTR D G _ _ Pl0 T A Ks _ _ _ R F hG
  intro i M₀ j Φ hΦ W _ _ σ hirr hadm hgood
  obtain ⟨Ty, hNF, hTV⟩ := GlobalTheory.T.exists_typeVector_of_good_level_representation hGC R F hG W σ hadm hgood
  obtain ⟨jl, Φ₀, b, hjl, hΦ₀, hb⟩ := GlobalTheory.T.exists_localIsometries_innerAut_adelicFrameIsometry R F hG i j Φ hΦ
  obtain ⟨hr, lam, hodd, hgap, hM₀, hMW⟩ := GlobalTheory.T.discrete_series_odd_rank_gap R F hG i M₀
  have hinf : IsInfFam R.θ := hG.core.models.inf
  let μ : Measure (GA D (Yc D 0)) := Measure.haar
  let μ' : Measure (GA D (Wc D i)) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ inferInstance
  haveI : μ'.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ' inferInstance
  have hadm' : IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom) :=
    GlobalTheory.CuspMult.isAdmissible_comp_equiv σ Φ.symm hadm
  rw [GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Yc D 0) _ M₀ μ W σ hadm.1,
    GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Wc D i) _ (R.MW i (sg0 D A)) μ' W _ hadm'.1,
    hTR D (Yc D 0) lam _ M₀ Ty hodd hgap hM₀ hNF (Wc D i) hr _ (R.MW i (sg0 D A)) hMW jl hjl Φ₀ hΦ₀ μ μ' W σ hirr hadm hTV]
  exact ((mDS_congr (GlobalTheory.MultEqTrace.conjEquiv σ Φ.toMulEquiv Φ₀.toMulEquiv b hb)).2).symm

end GlobalTheory.MultEqTrace
