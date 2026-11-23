import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

variable {Y X : Scheme.{0}} [IsIntegral Y] [IsIntegral X]

theorem theta_stalk {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    (a : X.presheaf.stalk (π y)) :
    θ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a) := by
  obtain ⟨l, h₁, h₂⟩ := h
  rw [Category.comp_id] at h₁
  subst h₁
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes y)
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (π y))
  have e₁ : Spec.map sY ≫ Y.fromSpecStalk y = gp Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : π.stalkMap y ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (π y)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  exact (congrArg (fun f => CommRingCat.Hom.hom f a) e₂).symm

theorem theta_fnOf {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ)
    (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hU s) = fnOf (π ⁻¹ᵁ U) hU' (π.app U s) := by
  have hU'' : π (genericPoint Y) ∈ U := hU'
  rw [← algebraMap_germ (x := π (genericPoint Y)) hU'' s, theta_stalk h,
    Scheme.Hom.germ_stalkMap_apply]
  exact algebraMap_germ hU' _

theorem regAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨a, rfl⟩ := hu
  exact ⟨_, (theta_stalk h y a).symm⟩

theorem unitAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : UnitAt (π y) u) : UnitAt y (θ u) := by
  obtain ⟨a, ha, rfl⟩ := hu
  exact ⟨_, ha.map _, (theta_stalk h y a).symm⟩

theorem preimage_regSet {π : Y ⟶ X} [Flat π] {θ : X.functionField →+* Y.functionField}
    (h : PFF (𝟙 _) π θ) (y : Y) : θ ⁻¹' (regSet y) = regSet (π y) := by
  ext u
  refine ⟨fun ⟨c, hc⟩ => ?_, fun hu => regAt_theta h y hu⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (π y)) u
  have hb0 : algebraMap _ X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  letI := (π.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (π y)) (Y.presheaf.stalk y) := Flat.stalkMap π y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap y).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π y))
    (B := Y.presheaf.stalk y)
  have e : π.stalkMap y a = c * π.stalkMap y b := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_mul, hc, ← theta_stalk h, ← theta_stalk h, ← map_mul, div_mul_cancel₀ _ hb0]
  have hm : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk y) (Ideal.span {b}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, e.symm⟩
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨d, by rw [map_mul, mul_div_cancel_right₀ _ hb0]⟩

theorem spMap_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) : spMap (GlobalTheory.Desc.cst p) = gp X ≫ p := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    simp
  conv_rhs => rw [h, gp, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

theorem comp_cst {V : Scheme.{0}} {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {p : X ⟶ Sp R}
    {q : Y ⟶ Sp R₁} {i : V ⟶ Y} {φ : V ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF i φ θ)
    (w : φ ≫ p = (i ≫ q) ≫ spMap ρ) : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst q).comp ρ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap ((GlobalTheory.Desc.cst q).comp ρ) := by
    have e1 : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap θ ≫ spMap (GlobalTheory.Desc.cst p) := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((GlobalTheory.Desc.cst q).comp ρ) = spMap (GlobalTheory.Desc.cst q) ≫ spMap ρ := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, spMap_cst, spMap_cst, ← Category.assoc, ← h₂, ← h₁]
    simp only [Category.assoc, w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem regAt_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) : RegAt x (GlobalTheory.Desc.cst p r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem unitAt_cst_iff {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    UnitAt x (GlobalTheory.Desc.cst p r) ↔ r ∉ (p x).asIdeal := by
  refine (unitAt_fnOf_iff (U := ⊤) trivial trivial _).trans ?_
  change x ∈ X.basicOpen (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ↔ _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

end GlobalTheory.Desc.GaussPt
