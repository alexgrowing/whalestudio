import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.GeomBijIso

theorem charZero_residueField {K : Type} [Field K] [CharZero K] {T : Scheme.{0}}
    (q : T ⟶ Spec (.of K)) (t : T) : CharZero (T.residueField t) := by
  let φ : CommRingCat.of K ⟶ T.residueField t :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ T.presheaf.germ ⊤ t trivial ≫ T.residue t
  exact charZero_of_injective_ringHom (f := φ.hom) φ.hom.injective

theorem exists_point_over {K : Type} [Field K] [CharZero K] {X T : Scheme.{0}} (f : X ⟶ T)
    (q : T ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hinj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω],
      Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ f)
    (t : T) (x : X) (hx : f x = t) :
    ∃ x₀ : Spec (T.residueField t) ⟶ X, x₀ ≫ f = T.fromSpecResidueField t ∧ x ∈ Set.range x₀ := by
  subst hx
  have := charZero_residueField q (f x)
  letI : Algebra (T.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  obtain ⟨x₀, h₁, h₂, -⟩ := GlobalTheory.OnePoint.exists_point_of_injective (K := T.residueField (f x)) f hinj
    (X.residueField x) (X.fromSpecResidueField x) (T.fromSpecResidueField (f x))
    (by rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; rfl)
  refine ⟨x₀, h₂, ?_⟩
  obtain ⟨s⟩ : Nonempty (Spec (X.residueField x)) := inferInstance
  refine ⟨Spec.map (CommRingCat.ofHom (algebraMap (T.residueField (f x)) (X.residueField x))) s, ?_⟩
  rw [← Scheme.Hom.comp_apply, h₁, Scheme.fromSpecResidueField_apply]

theorem injective_of_geomPts {K : Type} [Field K] [CharZero K] {X T : Scheme.{0}} (f : X ⟶ T)
    (q : T ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hinj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω],
      Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ f) :
    Function.Injective f := by
  intro x₁ x₂ hx
  generalize ht : f x₁ = t at hx
  obtain ⟨a, ha, s₁, h₁⟩ := exists_point_over f q hinj t x₁ ht
  obtain ⟨b, hb, s₂, h₂⟩ := exists_point_over f q hinj t x₂ hx.symm
  have hab : a = b := by
    let Ω := AlgebraicClosure (T.residueField t)
    let g : Spec (.of Ω) ⟶ Spec (T.residueField t) :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω))
    refine GlobalTheory.OnePoint.point_ext (K := T.residueField t) g (hinj Ω ?_)
    show (g ≫ a) ≫ f = (g ≫ b) ≫ f
    simp only [Category.assoc, ha, hb]
  subst hab
  rw [← h₁, ← h₂, Subsingleton.elim s₁ s₂]

theorem isIso_SpecMap_residue_genericPoint (T : Scheme.{0}) [IsIntegral T] :
    IsIso (Spec.map (T.residue (genericPoint T))) := by
  rw [isIso_SpecMap_iff]
  refine ⟨?_, IsLocalRing.residue_surjective⟩
  letI : Field (T.presheaf.stalk (genericPoint T)) := inferInstanceAs (Field T.functionField)
  exact RingHom.injective _

end GlobalTheory.GeomBijIso

namespace GlobalTheory.GeomBijIso

theorem surjective_of_geomPts {X T : Scheme.{0}} (f : X ⟶ T)
    (hb : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      ∃! x : Spec (.of Ω) ⟶ X, x ≫ f = t) : Function.Surjective f := by
  intro t
  let t' : Spec (.of (AlgebraicClosure (T.residueField t))) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
      (AlgebraicClosure (T.residueField t)))) ≫ T.fromSpecResidueField t
  obtain ⟨x, hx, -⟩ := hb _ t'
  obtain ⟨s⟩ : Nonempty (Spec (.of (AlgebraicClosure (T.residueField t)))) := inferInstance
  refine ⟨x s, ?_⟩
  rw [← Scheme.Hom.comp_apply, hx]
  exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)

end GlobalTheory.GeomBijIso

namespace GlobalTheory

open GeomBijIso in

theorem isIso_restrict_of_bijective_geomPts : ∀ (K : Type) [Field K] [CharZero K] (X T : Scheme.{0})
    [IsIntegral X] [IsIntegral T] (f : X ⟶ T) (q : T ⟶ Spec (.of K)), LocallyOfFiniteType f →
    LocallyQuasiFinite f → IsSeparated f → QuasiCompact f →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      ∃! x : Spec (.of Ω) ⟶ X, x ≫ f = t) → ∃ U : T.Opens, Nonempty U ∧ IsIso (f ∣_ U) := by
  intro K _ _ X T _ _ f q hl _ hs _ hb
  have hinj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω],
      Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ f :=
    fun Ω _ _ a b h ↦ (hb Ω (a ≫ f)).unique rfl h.symm
  have hfi : Function.Injective f := injective_of_geomPts f q hinj
  obtain ⟨x, hx⟩ := surjective_of_geomPts f hb (genericPoint T)
  obtain ⟨x₀, hx₀, -⟩ := exists_point_over f q hinj _ x hx
  have := isIso_SpecMap_residue_genericPoint T
  let φ : Spec (T.presheaf.stalk (genericPoint T)) ⟶ X :=
    inv (Spec.map (T.residue (genericPoint T))) ≫ x₀
  have hφ : φ ≫ f = T.fromSpecStalk (genericPoint T) ≫ 𝟙 T := by
    simp only [φ, Category.assoc, hx₀, Scheme.fromSpecResidueField, IsIso.inv_hom_id_assoc,
      Category.comp_id]
  obtain ⟨U, hηU, g, -, hg⟩ := spread_out_of_isGermInjective' (sX := 𝟙 T) (sY := f) φ hφ
  refine ⟨U, ⟨⟨_, hηU⟩⟩, ?_⟩
  have hrange : Set.range g ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    show f (g p) ∈ U
    rw [← Scheme.Hom.comp_apply, hg, Category.comp_id]
    exact p.2
  let g' : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι g hrange
  have hg' : g' ≫ (f ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, hg,
      Category.comp_id, Category.id_comp]
  have : IsClosedImmersion (g' ≫ (f ∣_ U)) := by rw [hg']; infer_instance
  have : IsClosedImmersion g' := IsClosedImmersion.of_comp g' (f ∣_ U)
  have : Surjective g' := by
    refine ⟨fun y ↦ ⟨(f ∣_ U) y, ?_⟩⟩
    apply (f ⁻¹ᵁ U).ι.isOpenEmbedding.injective
    apply hfi
    have key : ∀ z, f ((f ⁻¹ᵁ U).ι z) = U.ι ((f ∣_ U) z) := fun z ↦ by
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
    rw [key, key, ← Scheme.Hom.comp_apply g', hg']
    rfl
  have : IsIso g' := isIso_of_isClosedImmersion_of_surjective g'
  have : IsIso (g' ≫ (f ∣_ U)) := by rw [hg']; infer_instance
  exact IsIso.of_isIso_comp_left g' (f ∣_ U)

end GlobalTheory
