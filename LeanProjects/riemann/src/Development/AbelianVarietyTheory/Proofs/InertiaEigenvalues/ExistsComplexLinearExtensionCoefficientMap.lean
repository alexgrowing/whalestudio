import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExtCoeff

open TensorProduct

theorem exists_ext_map {K' : Type} [Field K'] (σ' : K' →+* ℂ) {X : Type} (V : Submodule K' (MvPolynomial X K'))
    (V' : Submodule ℂ (MvPolynomial X ℂ)) {W : Type*} [AddCommGroup W] [Module ℂ W] (c0 : V →ₛₗ[σ'] W) :
    ∃ c : V' →ₗ[ℂ] W, ∀ (v : V) (v' : V'), (v' : MvPolynomial X ℂ) = MvPolynomial.map σ' (v : MvPolynomial X K') → c v' = c0 v := by
  letI : Algebra K' ℂ := σ'.toAlgebra
  letI : Module K' W := Module.compHom W σ'
  haveI : IsScalarTower K' ℂ W := ⟨fun k a w => by
    show (σ' k * a) • w = σ' k • a • w
    rw [mul_smul]⟩
  let c0l : V →ₗ[K'] W := { toFun := c0, map_add' := c0.map_add, map_smul' := fun k v => c0.map_smulₛₗ k v }
  let F : ℂ ⊗[K'] V →ₗ[ℂ] W := c0l.liftBaseChange ℂ
  let ψ : ℂ ⊗[K'] V →ₗ[ℂ] MvPolynomial X ℂ :=
    (MvPolynomial.algebraTensorAlgEquiv K' ℂ).toLinearMap.comp (V.subtype.baseChange ℂ)
  have hψ1 : ∀ v : V, ψ (1 ⊗ₜ v) = MvPolynomial.map σ' (v : MvPolynomial X K') := by
    intro v
    simp [ψ, MvPolynomial.algebraTensorAlgEquiv_tmul]
    rfl
  have hinj : Function.Injective ψ := by
    refine (MvPolynomial.algebraTensorAlgEquiv K' ℂ).injective.comp ?_
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) V.subtype V.injective_subtype
  let e := LinearEquiv.ofInjective ψ hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (F.comp e.symm.toLinearMap)
  refine ⟨g.comp V'.subtype, fun v v' h => ?_⟩
  have hmem : (v' : MvPolynomial X ℂ) ∈ LinearMap.range ψ := ⟨1 ⊗ₜ v, (hψ1 v).trans h.symm⟩
  have key : g (v' : MvPolynomial X ℂ) = F (e.symm ⟨_, hmem⟩) := LinearMap.congr_fun hg ⟨_, hmem⟩
  have he : e.symm ⟨_, hmem⟩ = 1 ⊗ₜ v := by
    rw [LinearEquiv.symm_apply_eq]
    ext
    simp [e, LinearEquiv.ofInjective_apply, hψ1, h]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, key, he, F, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem exists_extC : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T1 : Type) (A : FamIn D.what₂.LL G Pl0 T1 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (j : Fin D.R.m) (Tp : Type) (tup : Tp → T1) (O : OMDat T.toCore R j Tp tup), ∃ c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W, ExtC R j (inC O.c') O.c0' c := by
  intro D G _ _ Pl0 T1 A T _ R j Tp tup O
  obtain ⟨c, hc⟩ := exists_ext_map (inC O.c') (VV O.c'.F (lamV D j)) (VV ℂ (lamV D j)) O.c0'
  exact ⟨c, fun v v' h => hc v v' h⟩

end GlobalTheory.ExtCoeff
