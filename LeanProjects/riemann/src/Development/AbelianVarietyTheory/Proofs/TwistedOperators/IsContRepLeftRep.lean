import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.LeftRegularRepresentation

def leftRep {K : Type} [Group K] (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F) :
    Representation ℂ K F where
  toFun a :=
    { toFun := fun φ => ⟨fun k => φ.1 (a⁻¹ * k), hF _ φ.2 _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ k
    simp
  map_mul' a b := by
    ext φ k
    simp [mul_assoc]

theorem dual_mem_span {K : Type} (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (ℓ : Module.Dual ℂ F) :
    ℓ ∈ Submodule.span ℂ (Set.range fun y : K => (LinearMap.proj y).comp F.subtype) := by
  have h : (Submodule.span ℂ (Set.range fun y : K =>
      ((LinearMap.proj y).comp F.subtype : Module.Dual ℂ F))) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push Not at hc
    exact hz (Subtype.ext (funext fun y => hc _ ⟨y, rfl⟩))
  rw [h]
  trivial

theorem isContRep_leftRep {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (F : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ F] (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) : GlobalTheory.Published.AutFin.IsContRep (leftRep F hF) := by
  intro ℓ w
  induction dual_mem_span F ℓ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact (hc _ w.2).comp (continuous_inv.mul continuous_const)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.const_smul a

theorem conv_mem {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
    (F : Submodule ℂ (K → ℂ)) (hF : ∀ φ ∈ F, ∀ a : K, (fun k => φ (a * k)) ∈ F)
    (hc : ∀ φ ∈ F, Continuous φ) {e : K → ℂ} (he : e ∈ F) {f : K → ℂ} (hf : Continuous f) :
    (fun a => ∫ k, e k * f (a * k) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan (leftRep F hF) := by
  have hi : ∀ φ : F, Integrable (fun k => φ.1 k * f k) μ := fun φ =>
    ((hc _ φ.2).mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ℓ : Module.Dual ℂ F :=
    { toFun := fun φ => ∫ k, φ.1 k * f k ∂μ
      map_add' := fun a b => by
        rw [← integral_add (hi a) (hi b)]
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  refine Submodule.subset_span ⟨ℓ, ⟨e, he⟩, funext fun a => ?_⟩
  change _ = ∫ k, e (a⁻¹ * k) * f k ∂μ
  rw [← integral_mul_left_eq_self (fun k => e (a⁻¹ * k) * f k) a]
  simp only [inv_mul_cancel_left]

theorem kFinAt_avg : ∀ (D : Formalism.BasicNotions.D7) (θ : Formalism.IndefR.Datum.InfFam D), Formalism.L2.Theta.IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : Formalism.L2.Theta.GA D (GlobalTheory.Grid.Node.V N) → ℂ), Formalism.L2.Theta.IsAutFunSm θ (GlobalTheory.Grid.Node.V N) ψ → ∀ (τ : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D)) (e : ↥(Formalism.REAL.KG (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ)) → ℂ), GlobalTheory.TypeSum.KFinFun (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) e → GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ (GlobalTheory.Grid.Node.V N) τ (Formalism.IndefR.Mult.DSModel.ε (GlobalTheory.Grid.Node.M N) τ) (Formalism.IndefR.Mult.DSModel.fr (GlobalTheory.Grid.Node.M N) τ) e ψ) := by
  intro D θ hθ N ψ hψ τ e he
  obtain ⟨F, hfd, heF, hc, hF⟩ := he
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hmem := GlobalTheory.Published.AutFin.conj_mem_UH hP hJ
  have hd : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hK : Continuous fun k : Formalism.REAL.KG (N.M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hk : Continuous (GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ)) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ).comp_continuous
      ((continuous_const.matrix_mul hK).matrix_mul continuous_const) hmem
  have hmul : ∀ a b, GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (a * b) =
      GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) a * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) b := by
    intro a b
    unfold GlobalTheory.Published.AutFin.kAt
    rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ (hmem a) (hmem b)]
    congr 1
    have e1 : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
    rw [e1]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  refine ⟨F, inferInstance, inferInstance, hfd, leftRep F fun φ h a => (hF φ h a).1,
    isContRep_leftRep F _ hc, fun x => ?_⟩
  have h := conv_mem (Formalism.REAL.muK (N.M.ε τ)) F (fun φ h a => (hF φ h a).1) hc heF
    (f := fun k => ψ (x * GlobalTheory.Published.AutFin.kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k))
    (hψ.cont.comp (continuous_const.mul hk))
  simp only [hmul, ← mul_assoc] at h
  exact h

end GlobalTheory.LeftRegularRepresentation

end
