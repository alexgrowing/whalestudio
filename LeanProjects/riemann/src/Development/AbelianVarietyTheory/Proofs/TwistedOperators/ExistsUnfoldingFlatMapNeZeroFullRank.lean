import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicBumpPeriodicUnderAdjointLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterEqRealPartCharOnBumpSupportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhdsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapProductDatumEqUnitriangularIntegralBumpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsIsotropicHomFromFirstMixedCoordinStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassConditionsCoreFromMixedCoordinateFunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinNe

variable {D : D7}

theorem left_inv_of_li {n ρ : ℕ} (x₀ : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x₀.transpose) :
    ∃ L : Matrix (Fin ρ) (Fin n) D.host.E, L * x₀ = 1 := by
  have hinj : Function.Injective (Matrix.toLin' x₀) := by
    show Function.Injective x₀.mulVec
    exact mulVec_injective_iff.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x₀) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  conv_lhs => rw [← LinearMap.toMatrix'_toLin' x₀]
  rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem flat_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∃ Φ ∈ cls dV dW p (rat x₀) y ψ, flatS dV dW s (rat x₀) y Φ ≠ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW s x₀ y hx₀ p hp
  obtain ⟨g, hgv, hg0⟩ := hp.vac₀
  obtain ⟨β₂, hβ₂, hβ₂y, hβ₂per, hβ₂supp⟩ := GlobalTheory.T.exists_adelicBump_periodic_under_adjointLattice D V₀ W W₀ σ dW p.B₂ hp.b₂ y
  obtain ⟨L, hL⟩ := left_inv_of_li x₀ hx₀
  obtain ⟨b, hb, hbx, hb01, hbsupp, hbper⟩ := exists_bump_le (rat x₀) p.A₁ hp.a₁ _
    (GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds D ψ hψ W.rank ρ (rat L) (rat x₀))
  have hpos : ∀ u : UX D ρ, b (rat x₀ ⬝ u.1.1) ≠ 0 → 0 < (star (psiUni ψ u.1)).re := by
    intro u hu
    obtain ⟨r, hr, hrU, hrA⟩ := hbsupp _ hu
    rw [GlobalTheory.T.genericCharacter_eq_realPartChar_on_bumpSupport D ψ V V₀ W W₀ ρ σ dV dW p x₀ L hL hp u r hr hrA]
    simpa only [Set.mem_setOf_eq, add_sub_cancel_left] using hrU
  have hcpt : HasCompactSupport (fun u : UX D ρ => b (rat x₀ ⬝ u.1.1)) := by
    refine HasCompactSupport.intro' (GlobalTheory.T.isCompact_unitriangular_of_rational_mul_mem_compact D W.rank ρ x₀ hx₀ _ (HasCompactSupport.isCompact (f := fun z => (b z : ℂ)) hb.supp))
      ((isClosed_tsupport _).preimage (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val))) ?_
    intro u hu
    by_contra h
    exact hu (subset_tsupport _ (by simpa using h))
  obtain ⟨g', hg', hg'm⟩ := GlobalTheory.T.mixedModelTarget_bump_mul_coreTheta_exists D ψ hψ V₀ W W₀ σ dW s.vT β₂ g hβ₂ hgv.1
  obtain ⟨Φ, hΦ, hΦm⟩ := GlobalTheory.T.exists_thetaFunction_mixedCoordinate_bump_mul_core D ψ hψ V V₀ W ρ dV s.vS (fun z => (b z : ℂ)) g' hb hg'
  have hbper' : ∀ a ∈ p.A₁, ∀ z, (fun z => (b z : ℂ)) (z + a) = (fun z => (b z : ℂ)) z := fun a ha z => by
    simp only [hbper a ha z]
  have hbsupp' : ∀ z, (fun z => (b z : ℂ)) z ≠ 0 → ∃ r : Mx D W.rank ρ, r.map (finPart D) = 0 ∧ z - (rat x₀ + r) ∈ p.A₁ :=
    fun z hz => by
      obtain ⟨r, hr, -, hrA⟩ := hbsupp z (by simpa using hz)
      exact ⟨r, hr, hrA⟩
  obtain ⟨hB₁, hB₂, hvac⟩ := GlobalTheory.T.unfolding_conditions_from_second_mixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vT p (rat x₀) y hp β₂ g g' hgv hg' hg'm hβ₂per hβ₂supp
  obtain ⟨hA₁, hA₂⟩ := GlobalTheory.T.class_conditions_isotropicHom_from_firstMixedCoordinate D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p (rat x₀) hp _ g' Φ hΦ hΦm hbper' hbsupp'
  obtain ⟨hC₁, hC₂, hCv⟩ := GlobalTheory.T.class_conditions_core_from_mixedCoordinateFunction D ψ hψ V V₀ W W₀ ρ σ dV dW s.vS p y _ g' Φ hg' hΦ hΦm hB₁ hB₂ hvac
  refine ⟨Φ, ⟨hΦ, hA₁, hA₂, hC₁, hC₂, hCv⟩, ?_⟩
  exact GlobalTheory.T.flatMap_productDatum_eq_unitriangularIntegral_bump D ψ hψ V V₀ W W₀ ρ σ dV dW s (rat x₀) y b β₂ g g' Φ hg0 hβ₂y hΦm hg'm
    (Complex.continuous_re.comp hb.cont |>.congr fun z => by simp) hbx (fun z => (hb01 z).1) hpos hcpt

end GlobalTheory.AscFinNe

end
