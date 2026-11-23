import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem exists_spMap_of_eq {F : Type} [Field F] {X : Scheme.{0}} (f : Sp F ⟶ X) (y : X)
    (hy : f (closedPoint F) = y) :
    ∃ φ : X.presheaf.stalk y ⟶ CommRingCat.of F, Spec.map φ ≫ X.fromSpecStalk y = f := by
  subst hy
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of F) f⟩

private theorem gpt_apply (X : Scheme.{0}) [IsIntegral X] (x : Sp X.functionField) :
    gpt X x = genericPoint X := by
  obtain rfl : x = closedPoint X.functionField := Subsingleton.elim _ _
  exact Scheme.fromSpecStalk_closedPoint

private theorem apply_eq_genericPoint {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    (f : Sp F ⟶ X) [IsDominant f] (x : Sp F) : f x = genericPoint X := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec _)
  rw [isGenericPoint_def, ← f.denseRange.closure_range]
  congr 1
  ext y
  exact ⟨fun hy => ⟨x, hy.symm⟩, fun ⟨x', hy⟩ => by rw [← hy, Subsingleton.elim x' x]; rfl⟩

private theorem exists_equiv {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W]
    (t : Sp X.functionField ⟶ W) [IsDominant t] (p : W ⟶ X) (h : t ≫ p = gpt X) :
    ∃ ε : X.functionField ≃+* W.functionField, gpt W = spMap ε.toRingHom ≫ t := by
  obtain ⟨φ, hφ⟩ := exists_spMap_of_eq t _ (apply_eq_genericPoint t _)
  have hp : p (genericPoint W) = genericPoint X := by
    obtain ⟨x⟩ : Nonempty (Sp X.functionField) := inferInstance
    rw [← apply_eq_genericPoint t x, ← Scheme.Hom.comp_apply, h, gpt_apply]
  obtain ⟨ψ, hψ⟩ := exists_spMap_of_eq (gpt W ≫ p) (genericPoint X)
    ((Scheme.Hom.comp_apply _ _ _).trans ((congrArg p (gpt_apply W _)).trans hp))
  have e : Spec.map (ψ ≫ φ) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (X.fromSpecStalk (genericPoint X)), Spec.map_comp, Category.assoc]
    erw [hψ]
    rw [Spec.map_id, Category.id_comp, ← Category.assoc]
    erw [hφ]
    exact h
  have e' : ψ ≫ φ = 𝟙 _ := Spec.map_injective e
  have e₁ : ∀ a, φ.hom (ψ.hom a) = a := fun a => congrArg (fun u => u.hom a) e'
  have hinj : Function.Injective (show W.functionField →+* X.functionField from φ.hom) :=
    RingHom.injective _
  have e₂ : ∀ a, ψ.hom (φ.hom a) = a := fun a => hinj (e₁ _)
  let ε : X.functionField ≃+* W.functionField :=
    RingEquiv.ofRingHom ψ.hom φ.hom (RingHom.ext e₂) (RingHom.ext e₁)
  refine ⟨ε, ?_⟩
  have e₃ : φ ≫ ψ = 𝟙 _ := CommRingCat.hom_ext (RingHom.ext e₂)
  rw [← hφ]
  change _ = Spec.map ψ ≫ Spec.map φ ≫ _
  rw [← Spec.map_comp_assoc, e₃, Spec.map_id]
  exact (Category.id_comp _).symm

theorem UpperTheory.exists_normal_proj_common_model :
    ∀ (k : Type) [Field k] [CharZero k] (X₁ X₂ : Scheme.{0}) [IsIntegral X₁] [IsIntegral X₂] (s₁ : X₁ ⟶ Sp k) (s₂ : X₂ ⟶ Sp k) (θ : X₂.functionField →+* X₁.functionField), IsProjOver s₁ → IsProjOver s₂ → spMap θ ≫ gpt X₂ ≫ s₂ = gpt X₁ ≫ s₁ → ∃ (W : Scheme.{0}) (_ : IsIntegral W) (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂) (ε : X₁.functionField ≃+* W.functionField), GlobalTheory.IsNormalScheme W ∧ IsProjOver (p₁ ≫ s₁) ∧ p₂ ≫ s₂ = p₁ ≫ s₁ ∧ gpt W ≫ p₁ = spMap ε.toRingHom ≫ gpt X₁ ∧ gpt W ≫ p₂ = spMap ε.toRingHom ≫ spMap θ ≫ gpt X₂ := by
  intro k _ _ X₁ X₂ _ _ s₁ s₂ θ h₁ h₂ w
  have : IsProper s₁ := ((isProjOver_iff_isProper_and_exists_isAmpleLB s₁).mp h₁).1
  have hP : IsProjOver (pullback.fst s₁ s₂ ≫ s₁) := ProjSpace.isProjOver_pullback h₁ h₂
  have : IsProper (pullback.fst s₁ s₂ ≫ s₁) :=
    ((isProjOver_iff_isProper_and_exists_isAmpleLB _).mp hP).1
  obtain ⟨h, e₁, e₂⟩ : ∃ h : Sp X₁.functionField ⟶ pullback s₁ s₂,
      h ≫ pullback.fst s₁ s₂ = gpt X₁ ∧ h ≫ pullback.snd s₁ s₂ = spMap θ ≫ gpt X₂ :=
    ⟨pullback.lift (gpt X₁) (spMap θ ≫ gpt X₂) (by rw [Category.assoc, w]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : IsFinite h.fromNormalization := by
    refine isFinite_fromNormalization_of_genericPoints (o := .of k) h (pullback.fst s₁ s₂ ≫ s₁)
      (fun x _ => charZero_of_injective_ringHom
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (gpt X₁ ≫ s₁).appTop ≫
          (Sp X₁.functionField).Γevaluation x).hom.injective) fun x _ => ?_
    have h1 : ((h ≫ pullback.fst s₁ s₂).stalkMap x).hom.EssFiniteType := by
      rw [e₁]
      exact (RingHom.FiniteType.of_surjective _
        (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType
    rw [Scheme.Hom.stalkMap_comp] at h1
    exact RingHom.EssFiniteType.residueFieldMap (.of_comp _ h1)
  obtain ⟨ε, hε⟩ := exists_equiv h.toNormalization (h.fromNormalization ≫ pullback.fst s₁ s₂)
    (by simp [e₁])
  refine ⟨h.normalization, inferInstance, h.fromNormalization ≫ pullback.fst s₁ s₂,
    h.fromNormalization ≫ pullback.snd s₁ s₂, ε, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]
    exact isProjOver_comp_of_isFinite _ hP
  · rw [Category.assoc, Category.assoc, pullback.condition]
  · rw [hε]; simp [e₁]
  · rw [hε]; simp [e₂]
