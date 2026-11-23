import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersDlogMinorsGe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitsZpowSurjective

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

theorem exists_extend_character {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.DivisibleUnits.target
  | exact _root_.GlobalTheory.DivisibleUnits.target
  | (apply _root_.GlobalTheory.DivisibleUnits.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.DivisibleUnits.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DivisibleUnits.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DivisibleUnits.target ..)

variable {O : Type} [CommRing O]

theorem exists_ptMap {A R : Type} [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    (c : specO O R ⟶ specO O A) : ∃ φ : A →ₐ[O] R, c = ptMap φ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of R) c.left
  have w := Over.w c
  change c.left ≫ Spec.map _ = Spec.map _ at w
  rw [← hψ, ← Spec.map_comp] at w
  have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  exact ⟨⟨ψ.hom, fun r => RingHom.congr_fun w' r⟩, Over.OverMorphism.ext hψ.symm⟩

theorem exists_finite_free [IsLocalRing O] (Z : Over (Spec (CommRingCat.of O))) [IsFinite Z.hom] [Flat Z.hom] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A), Module.Finite O A ∧ Module.Free O A ∧
      Nonempty (specO O A ≅ Z) := by
  haveI : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let g : CommRingCat.of O ⟶ Γ(Z.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ Z.hom.appTop
  letI : Algebra O Γ(Z.left, ⊤) := g.hom.toAlgebra
  have hw : Z.left.isoSpec.inv ≫ Z.hom = Spec.map g := by
    rw [Iso.inv_comp_eq, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]
  haveI h1 : IsFinite (Spec.map g) := hw ▸ inferInstance
  haveI h2 : Flat (Spec.map g) := hw ▸ inferInstance
  have h3 : g.hom.Finite := (IsFinite.SpecMap_iff g).1 h1
  have h4 : g.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  haveI : Module.Finite O Γ(Z.left, ⊤) := h3
  haveI : Module.Flat O Γ(Z.left, ⊤) := h4
  exact ⟨Γ(Z.left, ⊤), inferInstance, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing,
    ⟨Over.isoMk Z.left.isoSpec.symm hw⟩⟩

theorem exists_algHom_valuationSubring {F : Type} [Field F] (W : ValuationSubring F) {A : Type} [CommRing A]
    [Algebra W A] [Module.Finite W A] (φ : A →ₐ[W] F) : ∃ ψ : A →ₐ[W] W, φ = (Algebra.ofId W F).comp ψ := by
  have h : ∀ a, φ a ∈ (⊥ : Subalgebra W F) := fun a => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := W) a).map φ)
    exact Algebra.mem_bot.2 ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective (R := W) (A := F) Subtype.val_injective
  refine ⟨(e : (⊥ : Subalgebra W F) →ₐ[W] W).comp (φ.codRestrict ⊥ h), AlgHom.ext fun a => ?_⟩
  obtain ⟨y, hy⟩ := e.symm.surjective (φ.codRestrict ⊥ h a)
  show φ a = algebraMap W F (e (φ.codRestrict ⊥ h a))
  rw [← hy, e.apply_symm_apply]
  exact (congrArg Subtype.val hy).symm.trans ((e.symm.commutes y ▸ rfl : ((e.symm y : (⊥ : Subalgebra W F)) : F) = _))

theorem isAdicComplete_of_pow_le {I J : Ideal O} [IsAdicComplete I O] {a b : ℕ} (h₁ : I ^ a ≤ J) (h₂ : J ^ b ≤ I) :
    IsAdicComplete J O := by
  letI : TopologicalSpace O := I.adicTopology
  haveI : IsTopologicalRing O := (I.ringFilterBasis).isTopologicalRing
  letI : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  haveI : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  have hI : IsAdic I := rfl
  have hJ : IsAdic J := by
    rw [isAdic_iff] at hI ⊢
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · refine AddSubgroup.isOpen_mono (H₁ := (I ^ (a * n)).toAddSubgroup) (H₂ := (J ^ n).toAddSubgroup) ?_ (hI.1 _)
      intro x hx
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₁ n hx
    · obtain ⟨n, hn⟩ := hI.2 s hs
      refine ⟨b * n, fun x hx => hn ?_⟩
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₂ n hx
  exact hJ.isAdicComplete_iff.2 (hI.isAdicComplete_iff.1 inferInstance)

section Val
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem exists_pow_mem_span (a b : TWO.Ov v) (ha : ¬ IsUnit a) (hb : b ≠ 0) :
    ∃ n : ℕ, a ^ n ∈ Ideal.span {b} := by
  by_cases ha0 : a = 0
  · exact ⟨1, by simp [ha0]⟩
  have hbF : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
  have haF : (a : F) ≠ 0 := fun h => ha0 (Subtype.ext h)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 haF)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 hbF)
  have hr0 : 0 < r := by
    have h0 : (0 : ℚ) ≤ r := by have := TWO.v_nonneg v a; rw [← hr] at this; exact_mod_cast this
    refine lt_of_le_of_ne h0 fun h => ha ?_
    have hi : (a : F)⁻¹ ∈ TWO.Ov v := by
      refine TWO.exists_weight_basis_filtration (a := v a) ?_ (by rw [← hr, ← h]; rfl)
      rw [← AddValuation.map_mul, mul_inv_cancel₀ haF, AddValuation.map_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ haF))
  obtain ⟨n, hn⟩ := Archimedean.arch s hr0
  have hq : (a : F) ^ n / b ∈ TWO.Ov v := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
      ((AddValuation.ne_top_iff v).2 (div_ne_zero (pow_ne_zero n haF) hbF))
    have e : v ((a : F) ^ n / b * b) = v ((a : F) ^ n) := by rw [div_mul_cancel₀ _ hbF]
    rw [AddValuation.map_mul, AddValuation.map_pow, ← ht, ← hs, ← hr] at e
    have e' : t + s = n • r := by exact_mod_cast e
    rw [TWO.mem_Ov, ← ht]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t)
  exact ⟨n, Ideal.mem_span_singleton'.2 ⟨⟨_, hq⟩, Subtype.ext (by
    show (a : F) ^ n / b * b = ((a ^ n : TWO.Ov v) : F)
    rw [div_mul_cancel₀ _ hbF]; rfl)⟩⟩

end Val

end GlobalTheory.TorsionCharacter
