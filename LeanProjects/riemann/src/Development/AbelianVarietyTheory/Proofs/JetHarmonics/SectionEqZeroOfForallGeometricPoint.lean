import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorEqZeroOfForallGeometricPoint
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlatPoints

theorem isPullback_whiskerRight_left {S : Scheme.{0}} {T H : Over S} (q : T ⟶ H) (Y : Over S) :
    IsPullback (pullback.fst T.hom Y.hom) (q ▷ Y).left q.left (pullback.fst H.hom Y.hom) := by
  refine (IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst T.hom Y.hom)
    (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q)
    (IsPullback.of_hasPullback H.hom Y.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback T.hom Y.hom).flip

theorem section_eq_zero_of_cover {X : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}}
    (u : ∀ i, Z i ⟶ X) [∀ i, IsOpenImmersion (u i)] (hu : ∀ x : X, ∃ i z, u i z = x)
    (W : X.Opens) (f : Γ(X, W)) (h : ∀ i, ((u i).app W).hom f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W f 0 fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := hu x
  have hinj : Function.Injective ((u i).stalkMap z).hom :=
    (asIso ((u i).stalkMap z)).commRingCatIsoToRingEquiv.injective
  change (X.presheaf.germ W _ hx).hom f = (X.presheaf.germ W _ hx).hom 0
  apply hinj
  rw [Scheme.Hom.germ_stalkMap_apply, h i]
  simp

theorem eq_zero_of_forall_point (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)] (a : A)
    (ha : ∀ φ : A →ₐ[O] F, φ a = 0) : a = 0 := by
  have := tensor_eq_zero_of_forall_geometric_point O F hinj A O (a ⊗ₜ 1) (fun φ => by simp [ha φ])
  simpa using congrArg (TensorProduct.rid O A) this

theorem finite_algHom (O F : Type) [CommRing O] [Field F] [Algebra O F] (A : Type) [CommRing A]
    [Algebra O A] [Module.Finite O A] : Finite (A →ₐ[O] F) := by
  have : Finite (TensorProduct O F A →ₐ[F] F) := inferInstance
  exact Finite.of_equiv _ (Algebra.TensorProduct.liftEquivRight O F A F).symm

theorem affine_case (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)]
    (H Y : Over (Spec (CommRingCat.of O))) (e : specO O A ≅ H) [Flat Y.hom]
    (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W))
    (h : ∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) : f = 0 := by
  have := finite_algHom O F A
  let Φ : A →ₐ[O] ((A →ₐ[O] F) → F) := Pi.algHom O (fun _ => F) (fun φ => φ)
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact eq_zero_of_forall_point O F hinj A a fun φ => congrFun ha φ
  let q : specO O ((A →ₐ[O] F) → F) ⟶ H := ptMap Φ ≫ e.hom
  have h1 : IsSchemeTheoreticallyDominant (ptMap Φ).left :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hΦ
  have h2 : QuasiCompact (ptMap Φ).left :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom Φ.toRingHom)))
  have h0 : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h3 : IsSchemeTheoreticallyDominant q.left := by
    change IsSchemeTheoreticallyDominant ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have h4 : QuasiCompact q.left := by
    change QuasiCompact ((ptMap Φ).left ≫ e.hom.left)
    infer_instance
  have hp := isPullback_whiskerRight_left q Y
  have h5 : IsSchemeTheoreticallyDominant (q ▷ Y).left := .of_isPullback hp
  have h6 : QuasiCompact (q ▷ Y).left := MorphismProperty.of_isPullback hp h4
  apply (q ▷ Y).left.app_injective W
  rw [map_zero]
  let u : (A →ₐ[O] F) → (specO O F ⟶ specO O ((A →ₐ[O] F) → F)) :=
    fun φ => ptMap (Pi.evalAlgHom O (fun _ => F) φ)
  have hu : ∀ φ, IsOpenImmersion (u φ).left := fun φ =>
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun _ : A →ₐ[O] F => CommRingCat.of F) φ))))
  have hu' : ∀ φ, IsOpenImmersion (u φ ▷ Y).left := fun φ =>
    MorphismProperty.of_isPullback (isPullback_whiskerRight_left (u φ) Y) (hu φ)
  refine section_eq_zero_of_cover (fun φ => (u φ ▷ Y).left) (fun x => ?_) _ _ (fun φ => ?_)
  · obtain ⟨φ, p, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := fun _ : A →ₐ[O] F => F) (pullback.fst (specO O ((A →ₐ[O] F) → F)).hom Y.hom x)
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_whiskerRight_left (u φ) Y) p x hp
    exact ⟨φ, z, hz⟩
  · have := h (u φ ≫ q)
    rw [MonoidalCategory.comp_whiskerRight] at this
    exact this

end GlobalTheory.FlatPoints

namespace GlobalTheory

theorem section_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (H Y : Over (Spec (CommRingCat.of O))), IsFinite H.hom → Flat H.hom → IsReduced (specO O F ⊗ H).left → Flat Y.hom → ∀ (W : (H ⊗ Y).left.Opens) (f : Γ((H ⊗ Y).left, W)), (∀ c : specO O F ⟶ H, ((c ▷ Y).left.app W).hom f = 0) → f = 0 := by
  intro O F _ _ _ _ hinj H Y hfin hflat hred hY W f h
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  letI : Algebra O Γ(H.left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ(H.left, ⊤) ≅ H := Over.isoMk H.left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have h2 : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ(H.left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have : Module.Flat O Γ(H.left, ⊤) := (Flat.SpecMap_iff (f := ψ)).mp h2
  have h0 : IsIso (specO O F ◁ e.hom).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.hom)))
  have h3 : IsReduced (specO O F ⊗ specO O Γ(H.left, ⊤)).left :=
    isReduced_of_isOpenImmersion (specO O F ◁ e.hom).left
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ(H.left, ⊤)))) :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ(H.left, ⊤)).inv _ h3
  have : _root_.IsReduced (TensorProduct O F Γ(H.left, ⊤)) := (affine_isReduced_iff _).mp h4
  exact FlatPoints.affine_case O F hinj Γ(H.left, ⊤) H Y e W f h

end GlobalTheory
