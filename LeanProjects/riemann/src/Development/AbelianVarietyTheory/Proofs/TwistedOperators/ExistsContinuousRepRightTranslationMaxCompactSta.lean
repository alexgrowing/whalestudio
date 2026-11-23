import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeRep

open GlobalTheory.KTypeProj GlobalTheory.Published.AutFin

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem conj_UH (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
  GlobalTheory.Published.AutFin.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) k

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem fr_inv_mul (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem conj_inK (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    GlobalTheory.CuspGK.InK M τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) := by
  refine ⟨conj_UH M τ k, ?_⟩
  have hc : M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) * (M.fr τ)⁻¹ =
      (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK k * (M.fr τ * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
  rw [hc, fr_mul_inv M τ, one_mul, mul_one]
  exact k.2

theorem kAt_one (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) : kAt θ V τ (M.ε τ) (M.fr τ) 1 = 1 := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) * M.fr τ) = 1
  have h1 : Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) = 1 := rfl
  rw [h1, mul_one, fr_inv_mul M τ]
  exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ

theorem kAt_mul (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) (a b : Formalism.REAL.KG (M.ε τ)) :
    kAt θ V τ (M.ε τ) (M.fr τ) (a * b) = kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (a * b) * M.fr τ) =
    atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ) * atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ)
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (conj_UH M τ a) (conj_UH M τ b)]
  have hab : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
  have hsplit : (M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ) =
      (M.fr τ)⁻¹ * Formalism.REAL.toMK a * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK b * M.fr τ := by
    simp only [mul_assoc]
  rw [hsplit, fr_mul_inv M τ, mul_one, hab]
  simp only [mul_assoc]

theorem continuous_kAt (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) :
    Continuous fun k => kAt θ V τ (M.ε τ) (M.fr τ) k := by
  have hK : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hconj : Continuous fun k : Formalism.REAL.KG (M.ε τ) => (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ :=
    (continuous_const.matrix_mul hK).matrix_mul continuous_const
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hconj fun k => conj_UH M τ k

def kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) (hY : KStable θ M Y) (τ : D.what₂.Tau) :
    Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y where
  toFun k := (rTrL (kAt θ V τ (M.ε τ) (M.fr τ) k)).restrict fun f hf => hY τ _ (conj_inK M τ k) f hf
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) 1) = w.1 x
    rw [kAt_one M hθ, mul_one]
  map_mul' a b := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) (a * b)) =
      w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b)
    rw [kAt_mul M hθ, mul_assoc]

theorem isContRep_kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) [FiniteDimensional ℂ Y]
    (hY : KStable θ M Y) (hc : ∀ f ∈ Y, Continuous f) (τ : D.what₂.Tau) : IsContRep (kRep M hθ Y hY τ) := by
  intro ℓ w
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  refine hℓ.comp (continuous_induced_rng.2 (continuous_pi fun x => ?_))
  show Continuous fun k => (w : GA D V → ℂ) (x * kAt θ V τ (M.ε τ) (M.fr τ) k)
  exact (hc _ w.2).comp (continuous_const.mul (continuous_kAt M hθ τ))

end GlobalTheory.KTypeRep

theorem GlobalTheory.KTypeRep.exists_contRep_types : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y → GlobalTheory.KTypeProj.KStable θ M Y → (∀ f ∈ Y, Continuous f) →
    ∀ τ, ∃ ρ : Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y, GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ T : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ),
        (∀ i, ∀ w ∈ Y, T (GlobalTheory.KTypeProj.rhoK θ M i w) = GlobalTheory.KTypeProj.rhoK θ M i (T w)) →
        ∀ w : Y, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) ρ (T w) := by
  intro D θ V S M hθ Y hfin hY hc τ
  haveI := hfin
  refine ⟨GlobalTheory.KTypeRep.kRep M hθ Y hY τ, GlobalTheory.KTypeRep.isContRep_kRep M hθ Y hY hc τ, ?_⟩
  intro T hT w
  refine GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) _ (T ∘ₗ Y.subtype) (fun k u => ?_) w
  exact hT ⟨(τ, (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ), GlobalTheory.KTypeRep.conj_inK M τ k⟩ u.1 u.2

end
