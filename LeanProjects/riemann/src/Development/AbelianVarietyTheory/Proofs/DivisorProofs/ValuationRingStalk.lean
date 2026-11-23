import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme toSpec chartZ)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

theorem valuationRing_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp K)
    [hf : SmoothOfRelativeDimension 1 f] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h : Order.coheight x ≤ 1 := by simpa using GlobalTheory.AffineCover.coheight_le_of_smooth f hf x
  rcases h.eq_or_lt with h | h
  · have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h
    infer_instance
  · have h0 : Order.coheight x = 0 := by simpa using h
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h0.le
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    exact ValuationRing.of_field _

theorem exists_extend {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ}
    (v : Fin (N + 1) → W.toAffine.CoordinateRing) (k : Fin (N + 1)) (hk : v k ≠ 0) :
    ∃ ψ : scheme W ⟶ PSpace K N, ψ ≫ PSpace.str K N = toSpec W ∧
      ∀ (e : W.toAffine.CoordinateRing →+* K), e (v k) ≠ 0 → ∀ hv,
        spMap e ≫ chartZ W ≫ ψ = GlobalTheory.ProjSpace.pt (e.comp (algebraMap K _)) (e ∘ v) hv := by
  let A := W.toAffine.CoordinateRing
  let B := Localization.Away (v k)
  have hu : IsUnit (algebraMap A B (v k)) := IsLocalization.Away.algebraMap_isUnit (v k)
  have hv : Ideal.span (Set.range (algebraMap A B ∘ v)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k, rfl⟩) hu
  have h1 : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization (v k)
  have : IsDomain B := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hk)
  have := isProper_str K N
  have : (PSpace K N).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (PSpace.str K N)]
    infer_instance⟩
  obtain ⟨ψ, h₁, h₂⟩ := GlobalTheory.TorusConst.exists_extension (valuationRing_stalk (toSpec W))
    (spMap (algebraMap A B) ≫ chartZ W) (toSpec W) (PSpace.str K N)
    (GlobalTheory.ProjSpace.pt ((algebraMap A B).comp (algebraMap K A)) _ hv) (by
      rw [GlobalTheory.ProjSpace.pt_str, Category.assoc, GlobalTheory.WeierstrassCurve.chartZ_toSpec, ← Spec.map_comp]
      rfl)
  refine ⟨ψ, h₂, fun e he hv' => ?_⟩
  let e' : B →+* K := IsLocalization.Away.lift (v k) (IsUnit.mk0 _ he)
  have h3 : e'.comp (algebraMap A B) = e := IsLocalization.Away.lift_comp _ _
  have h4 : spMap e = spMap e' ≫ spMap (algebraMap A B) := by
    rw [← Spec.map_comp, ← h3]
    rfl
  rw [h4, Category.assoc, ← Category.assoc (spMap (algebraMap A B)), h₁, GlobalTheory.ProjSpace.spMap_pt]
  congr 1
  · rw [← RingHom.comp_assoc, h3]
  · exact funext fun j => RingHom.congr_fun h3 (v j)

end GlobalTheory.ProjHol
