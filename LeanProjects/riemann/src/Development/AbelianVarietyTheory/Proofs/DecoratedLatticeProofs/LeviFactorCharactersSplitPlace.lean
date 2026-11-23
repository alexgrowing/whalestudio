import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceInvariantFormOfWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorsWittParabolicOriginToPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDeterminantsWittLeviFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.LeviSplitChar

theorem circle_eq_one_of_pos {u : Circle} {t : ℝ} (ht : 0 < t) (h : (u : ℂ) = t) : u = 1 := by
  have h1 : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
  apply Circle.ext
  rw [h, h1, Circle.coe_one]
  simp

variable {D : D7}

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  simp [Formalism.L2.Theta.SuppAt, Formalism.L2.Theta.mt]

theorem isDetAt_one (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  simp [Formalism.L2.Theta.IsDetAt, Formalism.L2.Theta.mt]

end GlobalTheory.LeviSplitChar

namespace GlobalTheory.LeviSplitChar

variable {D : D7}

theorem exists_form (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T)
    (hω : IsWeilDatumO ψ S T χS χT om) (hω₀ : IsWeilDatumO ψ S₀ T χS χT om₀)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle)
    (H : ∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 =
      ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0))
    (e : AE D) (he : IsSplitIdem D e) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧
      ∀ a g, SuppAt e S₀ g → ∀ x₀, IsDetAt e S₀ g x₀ → ∃ R : ℝ, 0 < R ∧ ∀ f, IsThetaFunO ψ S T f →
        ℓ (om (d.levi a * d.emb0 g, 1) f) = (R : ℂ) * ((α a : ℂ) * (ξ g : ℂ) * (splitFacO χS χT x₀ 1 : ℂ)) * ℓ f := by
  obtain ⟨ℓ₀, hinv₀, f₀, hf₀, hne₀⟩ := GlobalTheory.T.exists_split_place_half_heisenberg_invariant_form D ψ hω.std S₀ T e he
  obtain ⟨ℓ, hinv, hne, hcmp⟩ := GlobalTheory.T.exists_splitPlace_invariantForm_of_wittCore D ψ hω.std S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hinv₀ ⟨f₀, hf₀, hne₀⟩
  refine ⟨ℓ, hinv, hne, fun a g hg x₀ hx₀ => ?_⟩
  obtain ⟨r₀, hr₀, hsp₀⟩ := hω₀.om_split e he g 1 hg (suppAt_one e T) x₀ 1 hx₀ (isDetAt_one e T)
  obtain ⟨r, hr, hc⟩ := hcmp 1 a
  have hmv := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hω.std).1 S S₀ T ρ d μ 𝓕 hμ
  have hbr := (GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1
  have hm := GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod_pos T.rank a
  refine ⟨r * r₀ * GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a, by positivity, fun f hf => ?_⟩
  have key := hc f (om (d.levi a * d.emb0 g, 1) f)
    ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ) * (r₀ : ℂ) * (splitFacO χS χT x₀ 1 : ℂ))
    hf (hω.om_pres _ f hf) (fun x _ => ?_)
  · rw [key]; push_cast; ring
  · have hmove := (GlobalTheory.T.weil_operators_witt_parabolic_origin_to_point D ψ S S₀ T ρ d χS χT om hω μ 𝓕 hμ f hf x).2.1 a g
    rw [hmove, H a g _ (GlobalTheory.TwistFactorCompare.isTheta_heisO hω.std hf _), ← hbr μ 𝓕 f (x ⬝ a.1), map_smul,
      smul_eq_mul, hsp₀ ℓ₀ hinv₀ _ (hmv f hf _)]
    simp only [Units.val_one, Matrix.one_mul]
    ring

end GlobalTheory.LeviSplitChar

namespace GlobalTheory.LeviSplitChar

theorem levi_chars_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), (∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0)) → ∀ e, IsSplitIdem D e → (∀ g, SuppAt e S₀ g → ξ g = 1) ∧ ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hω hω₀ μ 𝓕 hμ α ξ H e he
  obtain ⟨ℓ, hinv, ⟨f, hf, hℓf⟩, hkey⟩ := exists_form ψ S S₀ T ρ d χS χT om om₀ hω hω₀ μ 𝓕 hμ α ξ H e he
  have hsd := GlobalTheory.T.splitPlace_determinants_wittLeviFactor D S S₀ ρ d e he
  constructor
  · intro g hg
    obtain ⟨hS, x, hx₀, hx⟩ := hsd.1 g hg
    obtain ⟨R, hR, hk⟩ := hkey 1 g hg x hx₀
    obtain ⟨r', hr', hsp⟩ := hω.om_split e he (d.emb0 g) 1 hS (suppAt_one e T) x 1 hx (isDetAt_one e T)
    have h1 := hk f hf
    have h2 := hsp ℓ hinv f hf
    rw [map_one, one_mul] at h1
    rw [h1, map_one, Circle.coe_one] at h2
    have hs : (splitFacO χS χT x 1 : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h3 : (R : ℂ) * (ξ g : ℂ) = r' := by
      have := mul_right_cancel₀ hℓf (by rw [← h2]; ring : ((R : ℂ) * (ξ g : ℂ)) * (splitFacO χS χT x 1 : ℂ) * ℓ f = (r' : ℂ) * (splitFacO χS χT x 1 : ℂ) * ℓ f)
      exact mul_right_cancel₀ hs this
    apply circle_eq_one_of_pos (div_pos hr' hR)
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    push_cast
    rw [← h3]
    field_simp
  · intro a ha
    obtain ⟨hS, x, hx, hχ⟩ := hsd.2 χT T.rank hω.hecT hω.resT a ha
    obtain ⟨R, hR, hk⟩ := hkey a 1 (suppAt_one e S₀) 1 (isDetAt_one e S₀)
    obtain ⟨r', hr', hsp⟩ := hω.om_split e he (d.levi a) 1 hS (suppAt_one e T) x 1 hx (isDetAt_one e T)
    have h1 := hk f hf
    have h2 := hsp ℓ hinv f hf
    rw [map_one, mul_one] at h1
    rw [h1] at h2
    simp only [splitFacO, map_one, inv_one, mul_one, Circle.coe_one, hχ, Circle.coe_mul, Circle.coe_inv] at h2
    have hd : ((χT (Matrix.GeneralLinearGroup.det a) : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h3 : (R : ℂ) * ((α a : ℂ) * (χT (Matrix.GeneralLinearGroup.det a) : ℂ)) = r' := by
      have := mul_right_cancel₀ hℓf h2
      rw [← mul_assoc, this]
      field_simp
    have hu : α a * χT (Matrix.GeneralLinearGroup.det a) = 1 := by
      apply circle_eq_one_of_pos (div_pos hr' hR)
      have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      push_cast
      rw [← h3]
      field_simp
    exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory.LeviSplitChar
