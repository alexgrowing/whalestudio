import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveClosure

theorem exists_closure_arith_surface_rat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∃ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ p) 1 ∧ z ≫ w = redι Z ≫ ratFibre.fst p ∧ IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
  intro k _ X p D hX Z hZ
  have := hX.isIntegral
  have := hX.finite
  let S : Closeds X := ⟨closure (ratFibre.fst p '' (Z : Set (ratFibre p))), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set X) :=
    (hZ.isIrreducible.image _ (ratFibre.fst p).continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  haveI : IsPreimmersion (ratFibre.fst p) :=
    MorphismProperty.of_isPullback (ratFibre.isPullback p).flip inferInstance
  have hpb0 := (IsPullback.of_hasPullback w (ratFibre.fst p)).paste_vert (ratFibre.isPullback p)
  rw [← Category.assoc] at hpb0
  have hpb1 : IsPullback (pullback.fst w (ratFibre.fst p)) (pullback.snd w (ratFibre.fst p) ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := hpb0
  haveI : IsReduced (pullback ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isReduced_pullback_localization ℤ ℚ (nonZeroDivisors ℤ) _ _
  haveI : IsReduced (pullback w (ratFibre.fst p)) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w (ratFibre.fst p)) = (Z : Set (ratFibre p)) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change ratFibre.fst p ⁻¹' closure (ratFibre.fst p '' (Z : Set (ratFibre p))) = _
    rw [← (ratFibre.fst p).isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w (ratFibre.fst p)) Z hrange
  have hzw : (e.hom ≫ pullback.fst w (ratFibre.fst p)) ≫ w = redι Z ≫ ratFibre.fst p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w (ratFibre.fst p)) (redι Z ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : ℚ →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ ratFibre.snd p).appTop.hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w (ratFibre.fst p)).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  haveI : IsProper (w ≫ p) := by
    obtain ⟨N, i, _, hi⟩ := hproj
    have := isProper_str k N
    exact hi ▸ inferInstance
  haveI : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hX.finite
  haveI : Flat ((w ≫ p) ≫ spMap (Int.castRingHom k)) := (flat_int_iff_charZero _).2 hcW
  have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal S).subscheme = (1 + 1 : ℕ) :=
    IntModel.topologicalKrullDim_eq_succ (O := ℤ) (K := ℚ) Int.not_isField hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w (ratFibre.fst p), inferInstance, hX.of_isClosedImmersion w hcW hdim,
    hzw, hpb⟩

end GlobalTheory.CurveClosure
