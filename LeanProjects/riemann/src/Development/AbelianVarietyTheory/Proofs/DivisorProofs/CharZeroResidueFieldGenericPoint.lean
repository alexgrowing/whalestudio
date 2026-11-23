import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCoverStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]
  {E : X.Modules} {r : ℕ} {h : VMetric p E r}

omit [IsIntegral X] in

theorem charZero_residueField_genericPoint (Y : Scheme.{0}) [IsIntegral Y] (hc : CharZero Γ(Y, ⊤)) :
    CharZero (Y.residueField (genericPoint Y)) := by
  have h₁ : CharZero Y.functionField := charZero_of_injective_ringHom
    (f := (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) (germ_injective_of_isIntegral _ _ _)
  let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue (genericPoint Y)).hom
  exact charZero_of_injective_ringHom f.injective

theorem RegCover.exists_common (hp : IsArithVar p 1) (C₁ C₂ : RegCover p) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (t₁ : Z ⟶ C₁.Y) (t₂ : Z ⟶ C₂.Y),
      t₁ ≫ C₁.ρ = t₂ ≫ C₂.ρ ∧ IsArithVar ((t₁ ≫ C₁.ρ) ≫ p) 1 ∧
      t₁ (genericPoint Z) = genericPoint C₁.Y ∧ t₂ (genericPoint Z) = genericPoint C₂.Y ∧
      t₁.residueDegree (genericPoint Z) ≠ 0 ∧ t₂.residueDegree (genericPoint Z) ≠ 0 := by
  obtain ⟨z, z₁, z₂, d₁, d₂⟩ := GlobalTheory.T.pullback_point_residue_nonzero X C₁.Y C₂.Y C₁.ρ C₂.ρ _ _ (C₁.generic.trans C₂.generic.symm)
    C₁.finite C₂.finite
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint z
  have hs : IsSeparated p := by
    obtain ⟨N, j, _, e⟩ := hp.isProjOver
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hP : IsProjOver (Limits.pullback.fst C₁.ρ C₂.ρ ≫ C₁.ρ ≫ p) := by
    have e : Limits.pullback.fst C₁.ρ C₂.ρ ≫ C₁.ρ ≫ p =
        Limits.pullback.mapDesc C₁.ρ C₂.ρ p ≫ Limits.pullback.fst (C₁.ρ ≫ p) (C₂.ρ ≫ p) ≫ C₁.ρ ≫ p := by
      rw [Limits.pullback.lift_fst_assoc, Category.comp_id]
    rw [e]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ (ProjSpace.isProjOver_pullback C₁.reg.isProjOver C₂.reg.isProjOver)
  have hZ : IsProjOver ((i ≫ Limits.pullback.fst C₁.ρ C₂.ρ ≫ C₁.ρ) ≫ p) := by
    have := ProjSpace.isProjOver_comp_of_isClosedImmersion i hP
    simpa using this
  have g₁ : (i ≫ Limits.pullback.fst C₁.ρ C₂.ρ) (genericPoint Z) = genericPoint C₁.Y := by
    simp [hi, z₁]
  have g₂ : (i ≫ Limits.pullback.snd C₁.ρ C₂.ρ) (genericPoint Z) = genericPoint C₂.Y := by
    simp [hi, z₂]
  have r₁ : (i ≫ Limits.pullback.fst C₁.ρ C₂.ρ).residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact d₁
  have r₂ : (i ≫ Limits.pullback.snd C₁.ρ C₂.ρ).residueDegree (genericPoint Z) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion i, mul_one, hi]
    exact d₂
  have hfl : Flat (((i ≫ Limits.pullback.fst C₁.ρ C₂.ρ ≫ C₁.ρ) ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    have c₁ : CharZero Γ(C₁.Y, ⊤) := (flat_int_iff_charZero _).1 C₁.reg.flat
    have c₂ := charZero_residueField_genericPoint C₁.Y c₁
    have c₃ : CharZero (Z.residueField (genericPoint Z)) := by
      have : ∀ y : C₁.Y, y = genericPoint C₁.Y → CharZero (C₁.Y.residueField y) := by
        rintro _ rfl; exact c₂
      have := this _ g₁
      exact (RingHom.charZero_iff (Scheme.Hom.residueFieldMap _ _).hom.injective).1 this
    exact (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hq : IsArithVar ((i ≫ Limits.pullback.fst C₁.ρ C₂.ρ ≫ C₁.ρ) ≫ p) 1 :=
    ⟨hp.isDomain, hp.finite, inferInstance, hZ, hfl,
      GlobalTheory.T.dimension_of_dominant_flat_cover k C₁.Y Z (C₁.ρ ≫ p) _ 1 C₁.reg.toIsArithVar hZ hfl (i ≫ Limits.pullback.fst C₁.ρ C₂.ρ)
        (by simp) g₁ r₁⟩
  refine ⟨Z, inferInstance, i ≫ Limits.pullback.fst C₁.ρ C₂.ρ, i ≫ Limits.pullback.snd C₁.ρ C₂.ρ, ?_,
    ?_, g₁, g₂, r₁, r₂⟩
  · simp [Limits.pullback.condition]
  · simpa using hq

end GlobalTheory
