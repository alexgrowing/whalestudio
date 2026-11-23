import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCond
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.KernelCondGlob
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.HasExponentMulOfIsUnram
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PowFamIsDeligneMeas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.TateThesis.EulerFactors
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

section LocalLeaves

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end LocalLeaves

section Weights

open GlobalTheory.WeilRestrict Polynomial

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {K L : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in

theorem eq_resWeil_of_agree (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {σ' : Weil h'} {σ : Weil h}
    (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) : σ = resWeil h h' σ' :=
  Subtype.ext (AlgEquiv.ext fun z => (hσ z).trans (resWeil_apply h h' σ' z).symm)

theorem induces_lpTwist (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {X : WD h'} {Y : WD h}
    (hXY : Induces X Y) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (ξ' : Weil h' →* ℂˣ) (hξ' : IsSmooth ξ')
    (hres : ∀ σ', ξ' σ' = ξ (resWeil h h' σ')) :
    Induces (X.lpTwist ξ' hξ') (Y.lpTwist ξ hξ) := by
  obtain ⟨m, n, a, b, j, rfl, rfl, hn, hj, hspan⟩ := hXY
  refine ⟨m, n, a.twist ξ' hξ', b.twist ξ hξ, j, (WD.lpTwist_mk _ _ _).symm, (WD.lpTwist_mk _ _ _).symm, hn,
    fun σ' σ hσ u => ?_, ?_⟩
  · have e := eq_resWeil_of_agree h h' hσ
    simp only [WDRep.twist_ρ, LinearMap.smul_apply, map_smul, hj σ' σ hσ u, hres, ← e]
  · rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, u⟩, rfl⟩
    have e : b.ρ g (j u) = ((ξ g : ℂ))⁻¹ • (b.twist ξ hξ).ρ g (j u) := by
      rw [WDRep.twist_ρ, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    show b.ρ g (j u) ∈ _
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g, u), rfl⟩)

end Weights

section Twist

open Polynomial

theorem prod_map_finsetSum {ι : Type*} (s : Finset ι) (M : ι → Multiset ℂ) (f : ℂ → ℂ[X]) :
    ((∑ i ∈ s, M i).map f).prod = ∏ i ∈ s, ((M i).map f).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add, Multiset.prod_add, ih]

theorem filter_finsetSum {ι : Type*} (s : Finset ι) (M : ι → Multiset ℂ) (p : ℂ → Prop) [DecidablePred p] :
    (∑ i ∈ s, M i).filter p = ∑ i ∈ s, (M i).filter p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Multiset.filter_add, ih]

theorem map_finsetSum {ι : Type*} (s : Finset ι) (M : ι → Multiset ℂ) (f : ℂ → ℂ) :
    (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Multiset.map_add, ih]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpTwist (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) (σ : Weil h) :
    (x.lpTwist ξ hξ).eig σ = (x.eig σ).map (· * (ξ σ : ℂ)) := by
  induction x using WD.ind with
  | hP n a => rw [WD.lpTwist_mk, WD.eig_mk, WD.eig_mk, WDRep.twist_ρ, GlobalTheory.RowTie.EigTwist.roots_charpoly_smul]

theorem charPol_lpTwist_of_eq_one (x : WD h) (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) {σ : Weil h} (h1 : ξ σ = 1) :
    (x.lpTwist ξ hξ).charPol σ = x.charPol σ := by
  induction x using WD.ind with
  | hP n a => rw [WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ, h1, Units.val_one, one_smul]

theorem prod_charPol_eq {r : ℕ} (p q : Fin r → ℕ) (x y : Fin r → WD h) (σ : Weil h) :
    ∏ i, (x i).charPol σ ^ p i * (y i).charPol σ ^ q i =
      ((∑ i, (p i • (x i).eig σ + q i • (y i).eig σ)).map fun α => X - C α).prod := by
  rw [prod_map_finsetSum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_nsmul, Multiset.map_nsmul, Multiset.prod_nsmul,
    Multiset.prod_nsmul, ← WD.charPol_eq_prod, ← WD.charPol_eq_prod]

end Twist

section Assembly

open GlobalTheory.WeilRestrict

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

end Assembly

end PositivityTheory.Pf1.LocalLanglands.HeckeKernelConditions

end
