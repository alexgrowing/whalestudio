import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatConst

theorem exists_section (Y : Scheme.{0}) {K : Type} (W : K → Y.Opens) (hW : ⨆ i, W i = ⊤)
    (κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Y) → D)
    (hκ : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D' (Spec.map φ ≫ x) = φ (κ D x)) :
    ∃ s : Γ(Y, ⊤), ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Y), (∃ i, ⊤ ≤ x ⁻¹ᵁ W i) →
      κ D x = (Scheme.ΓSpecIso D).hom (x.appTop s) := by
  let J : Type := {U : Y.affineOpens // ∃ i, U.1 ≤ W i}
  let U : J → Y.Opens := fun j ↦ j.1.1
  have hsm : ∀ j : J, ∃ i, ⊤ ≤ j.1.2.fromSpec ⁻¹ᵁ W i := fun j ↦ by
    obtain ⟨i, hi⟩ := j.2
    refine ⟨i, ?_⟩
    rw [← j.1.2.fromSpec_preimage_self]
    exact fun _ h ↦ hi h
  have hcov : ∀ y : Y, ∃ j : J, y ∈ U j := fun y ↦ by
    have hy : y ∈ ⨆ i, W i := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨V, hV, hyV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hi
    exact ⟨⟨⟨V, hV⟩, i, hle⟩, hyV⟩
  let sf : ∀ j : J, Γ(Y, U j) := fun j ↦ κ _ j.1.2.fromSpec
  have hgerm : ∀ (j : J) (y : Y) (hy : y ∈ U j),
      Y.presheaf.germ (U j) y hy (sf j) = κ _ (Y.fromSpecStalk y) := fun j y hy ↦ by
    rw [← j.1.2.fromSpecStalk_eq_fromSpecStalk hy]
    exact (hκ _ _ _ _ (hsm j)).symm
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hcov y)) sf (fun a b ↦ by
      refine TopCat.Presheaf.section_ext Y.sheaf _ _ _ fun y hy ↦ ?_
      exact ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm a y hy.1)).trans
        ((Y.presheaf.germ_res_apply _ y hy _).trans (hgerm b y hy.2)).symm)
  have hnat : ∀ (D D' : CommRingCat.{0}) (φ : D ⟶ D') (x : Spec D ⟶ Y),
      (Scheme.ΓSpecIso D').hom ((Spec.map φ ≫ x).appTop s) = φ ((Scheme.ΓSpecIso D).hom (x.appTop s)) := by
    intro D D' φ x
    rw [Scheme.Hom.comp_appTop]
    exact congrArg (fun f ↦ CommRingCat.Hom.hom f (x.appTop s)) (Scheme.ΓSpecIso_naturality φ)
  have hj : ∀ j : J, κ _ j.1.2.fromSpec = (Scheme.ΓSpecIso _).hom (j.1.2.fromSpec.appTop s) := fun j ↦ by
    have h1 : j.1.2.fromSpec.appTop ≫ (Scheme.ΓSpecIso _).hom = Y.presheaf.map (homOfLE le_top).op := by
      have h0 := congrArg (fun q ↦ (Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop q ≫ (Scheme.ΓSpecIso _).hom)
        j.1.2.fromSpec_toSpecΓ
      simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Category.assoc,
        Iso.inv_hom_id_assoc] at h0
      exact h0
    exact (hs j).symm.trans (congrArg (fun f ↦ CommRingCat.Hom.hom f s) h1).symm
  refine ⟨s, fun D x hx ↦ Module.eq_of_localization_maximal (R := D) (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap D (Localization.AtPrime P)) _ _ fun P hP ↦ ?_⟩
  let φ : D ⟶ CommRingCat.of (Localization.AtPrime P) := CommRingCat.ofHom (algebraMap D _)
  refine (hκ _ _ φ x hx).symm.trans (Eq.trans ?_ (hnat _ _ φ x))
  obtain ⟨j, hy⟩ := hcov ((Spec.map φ ≫ x) (IsLocalRing.closedPoint (CommRingCat.of (Localization.AtPrime P))))
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem _ hy
  have hr : Set.range (Spec.map φ ≫ x) ⊆ Set.range j.1.2.fromSpec := by
    rw [j.1.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have : z ∈ (Spec.map φ ≫ x) ⁻¹ᵁ U j := by rw [htop]; trivial
    exact this
  haveI : IsOpenImmersion j.1.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec (U := j.1.1) j.1.2
  have hf := IsOpenImmersion.lift_fac j.1.2.fromSpec _ hr
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift j.1.2.fromSpec _ hr)
  rw [← hψ] at hf
  rw [← hf]
  exact (hκ _ _ ψ _ (hsm j)).trans ((congrArg ψ (hj j)).trans (hnat _ _ ψ _).symm)

theorem const_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → Function.Surjective X.hom.appTop.hom → ∀ k : Fn0 X, IsCob W (Fn1.zero X) k → ∃ r : R, ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), Sm W x → k D x = algebraMap R D r := by
  intro R _ X K W hW hs k hk
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ X.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ X.left), @Pt R _ X D _ (al D x) := fun D x ↦
    Over.homMk x (Spec.map_preimage (R := CommRingCat.of R) (x ≫ X.hom)).symm
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ X.left) → D := fun D x ↦ @k D _ (al D x) (pt D x)
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
      (x : Pt X D) (x' : Pt X D'), Sm W x → spMap φ ≫ x.left = x'.left → k D' x' = φ (k D x) := by
    intro D _ _ D' _ _ φ x x' hx h
    have h1 : x.left ≫ X.hom = spMap (algebraMap R D) := Over.w x
    have h2 : x'.left ≫ X.hom = spMap (algebraMap R D') := Over.w x'
    have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
      apply Spec.map_injective
      rw [Spec.map_comp]
      change spMap φ ≫ spMap _ = spMap _
      rw [← h1, ← h2, ← h, Category.assoc]
    let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
    have h4 := hk D D' ψ x hx
    have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
    rw [h5] at h4
    exact (sub_eq_zero.1 h4.symm)
  obtain ⟨s, hs'⟩ := exists_section X.left W hW κ fun D D' φ x hx ↦
    @key D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom (pt D x) (pt D' _) hx rfl
  obtain ⟨r, rfl⟩ := hs s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom r, fun D _ inst x hx ↦ ?_⟩
  have h1 : κ (CommRingCat.of D) x.left = k D x :=
    @key D _ inst D _ (al (CommRingCat.of D) x.left) (RingHom.id D) x (pt (CommRingCat.of D) x.left) hx (by
      change Spec.map (𝟙 _) ≫ _ = _
      rw [Spec.map_id, Category.id_comp]; rfl)
  rw [← h1, hs' (CommRingCat.of D) x.left hx]
  have h2 : x.left ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R D)) := Over.w x
  have h3 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R D))
  rw [← h2, Scheme.Hom.comp_appTop] at h3
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3

end GlobalTheory.PtExt.NatConst
