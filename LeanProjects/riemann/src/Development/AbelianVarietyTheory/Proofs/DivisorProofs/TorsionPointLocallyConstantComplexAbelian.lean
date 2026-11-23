import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionLocal

lemma comp_pow_overScheme_grpObj {A T : Over (Sp ℂ)} [GrpObj A] (f : T ⟶ A) (g : A ⟶ A) :
    ∀ n : ℕ, f ≫ g ^ n = (f ≫ g) ^ n
  | 0 => by simp [MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj f g n]

theorem locally_eq_const_of_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  intro A _ hA N hN T x hx t
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit ((N : ℂ)) := (Nat.cast_ne_zero.mpr (by omega)).isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨-, hfin, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective (Sp ℂ) A N hA hunit
  set f : A ⟶ A := (𝟙 A) ^ N with hf
  have hTu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  have hxf : x.left ≫ f.left = T.hom ≫ η[A].left := by
    have h1 : x ≫ f = toUnit T ≫ η[A] := by
      rw [hf, comp_pow_overScheme_grpObj, Category.comp_id, hx]; rfl
    have h2 := congrArg (fun h => h.left) h1
    simpa [hTu] using h2
  haveI : IsFinite f.left := hfin
  haveI : Etale f.left := het
  haveI := hA.smooth
  have hη : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  have hfw : f.left ≫ A.hom = A.hom := Over.w f
  have hpt : T.hom t = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  set a := x.left t with ha_def
  have hfa : f.left a = η[A].left (IsLocalRing.closedPoint ℂ) := by
    rw [ha_def, ← Scheme.Hom.comp_apply, hxf, Scheme.Hom.comp_apply, hpt]
  have he : IsClosed ({η[A].left (IsLocalRing.closedPoint ℂ)} : Set A.left) :=
    ((pointEquivClosedPoint A.hom) ⟨η[A].left, hη⟩).2
  haveI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have ha : IsClosed ({a} : Set A.left) := by
    rw [isClosed_singleton_iff_locallyOfFiniteType]
    have h1 : LocallyOfFiniteType (A.left.fromSpecResidueField (f.left a)) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp (hfa ▸ he)
    have h2 : LocallyOfFiniteType (Spec.map (f.left.residueFieldMap a)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.FiniteType.of_finite (residueFieldMap_finite_of_locallyQuasiFinite f.left a)
    have h3 : LocallyOfFiniteType (A.left.fromSpecResidueField a ≫ f.left) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; infer_instance
    exact locallyOfFiniteType_of_comp _ f.left
  let y0 : Sp ℂ ⟶ A.left := pointOfClosedPoint A.hom a ha
  have hy0 : y0 ≫ A.hom = 𝟙 _ := pointOfClosedPoint_comp A.hom a ha
  let y : 𝟙_ (Over (Sp ℂ)) ⟶ A := Over.homMk y0 (by simpa using hy0)
  have hy0f : y0 ≫ f.left = η[A].left := by
    refine ext_of_apply_closedPoint_eq A.hom ?_ hη ?_
    · rw [Category.assoc, hfw, hy0]
    · show f.left (pointOfClosedPoint A.hom a ha (IsLocalRing.closedPoint ℂ)) = _
      exact (congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)).trans hfa
  have hg : x.left ≫ f.left = (T.hom ≫ y0) ≫ f.left := by
    rw [hxf, Category.assoc, hy0f]
  have hψ := Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)
  set ψ := Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
  have hr : (residueFieldIsoBase A.hom a ha).inv ≫ x.left.residueFieldMap t = ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, SpecMap_residueFieldIsoBase_inv]
    erw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    rw [Over.w x]
  have k : T.left.fromSpecResidueField t ≫ x.left = T.left.fromSpecResidueField t ≫ T.hom ≫ y0 := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← hψ]
    simp only [y0, pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp]
    rw [← hr, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let g : T.left ⟶ pullback f.left f.left := pullback.lift x.left (T.hom ≫ y0) hg
  have kg : T.left.fromSpecResidueField t ≫ g =
      (T.left.fromSpecResidueField t ≫ x.left) ≫ pullback.diagonal f.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, k]
  refine ⟨g ⁻¹ᵁ (pullback.diagonal f.left).opensRange, y, ?_, ?_⟩
  · show g t ∈ Set.range (pullback.diagonal f.left)
    have hk := congrArg (fun h => h (IsLocalRing.closedPoint (T.left.residueField t))) kg
    refine ⟨_, ((Scheme.Hom.comp_apply _ _ _).symm.trans hk.symm).trans
      ((Scheme.Hom.comp_apply _ _ _).trans ?_)⟩
    exact congrArg g (Scheme.fromSpecResidueField_apply t _)
  · set U := g ⁻¹ᵁ (pullback.diagonal f.left).opensRange
    have hle : Set.range (U.ι ≫ g) ⊆ Set.range (pullback.diagonal f.left) := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact u.2
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f.left) (U.ι ≫ g) hle
    have h1 := congrArg (· ≫ pullback.fst f.left f.left) hl
    have h2 := congrArg (· ≫ pullback.snd f.left f.left) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, g,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    show U.ι ≫ x.left = U.ι ≫ T.hom ≫ y0
    rw [← h1, h2]

end GlobalTheory.TorsionLocal
