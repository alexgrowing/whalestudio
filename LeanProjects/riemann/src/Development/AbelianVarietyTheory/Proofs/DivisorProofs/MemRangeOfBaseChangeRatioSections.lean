import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_tmul_one_eq {K L B : Type} [Field K] [Field L] [CommRing B] [Algebra K L]
    [Algebra K B] (b₁ b₂ : B) (l : L) (hb : b₂ ≠ 0) (h : b₁ ⊗ₜ[K] (1 : L) = b₂ ⊗ₜ[K] l) :
    l ∈ Set.range (algebraMap K L) := by
  by_contra hl
  have hx : l ∉ (K ∙ (1 : L)) := by
    intro hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    exact hl ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩
  obtain ⟨f, hf, hp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have h1 : f 1 = 0 := by
    have : f 1 ∈ (K ∙ (1 : L)).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self 1)
    rw [hp] at this
    simpa using this
  have h2 := congrArg ((TensorProduct.rid K B).toLinearMap ∘ₗ LinearMap.lTensor B f) h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul, h1, zero_smul] at h2
  exact hb ((smul_eq_zero.1 h2.symm).resolve_left hf)

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem exists_affine_res_ne_zero {X : Scheme.{0}} {U : X.Opens} (f : Γ(X, U)) (hf : f ≠ 0) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U), X.presheaf.map (homOfLE hVU).op f ≠ 0 := by
  have : ∃ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (TopCat.Presheaf.section_ext X.sheaf U f 0 (fun x hx => by rw [map_zero]; exact hc x hx))
  obtain ⟨x, hx, hne⟩ := this
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U) hx
  refine ⟨V, hV, hVU, fun h0 => hne ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) x hxV, h0, map_zero]

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

theorem fromSpec_appLE_hom {X : Scheme.{0}} {U V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ U)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso Γ(X, V)).hom.hom ((hV.fromSpec.appLE U ⊤ e).hom f) =
      (X.presheaf.map (homOfLE hVU).op).hom f := by
  have : hV.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom =
      X.presheaf.map (homOfLE hVU).op := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_of_le hV U hVU, Category.assoc, Category.assoc,
      Category.assoc, ← Functor.map_comp_assoc]
    have h' : ((homOfLE le_top).op ≫ (homOfLE e).op :
        Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [h', CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  rw [← this]
  rfl

theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst hfg; rfl

end GlobalTheory.ConstDescent

namespace GlobalTheory.ConstDescent

open TensorProduct

theorem mem_range_of_pullback_eq {K L : Type} [Field K] [Field L] (ψ : K →+* L) {X : Scheme.{0}}
    (h : X ⟶ Sp K) (U : X.Opens) (f₁ f₂ : Γ(X, U)) (l : L) (hf : f₂ ≠ 0)
    (heq : ((pullback.fst h (spMap ψ)).app U).hom f₁ =
      ((pullback.fst h (spMap ψ)).app U).hom f₂ * resTop _ (scal (pullback.snd h (spMap ψ)) l)) :
    l ∈ Set.range ψ := by
  obtain ⟨V, hV, hVU, hne⟩ := exists_affine_res_ne_zero f₂ hf
  let B : CommRingCat := Γ(X, V)
  let e : Spec B ⟶ X := hV.fromSpec
  let α : CommRingCat.of K ⟶ B := Spec.preimage (e ≫ h)
  letI : Algebra K B := α.hom.toAlgebra
  letI : Algebra K L := ψ.toAlgebra
  let Z : CommRingCat := CommRingCat.of (B ⊗[K] L)
  let a : Spec Z ⟶ Spec B := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  let b : Spec Z ⟶ Sp L :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom)
  have hcomm : (a ≫ e) ≫ h = b ≫ spMap ψ := by
    rw [Category.assoc, ← Spec.map_preimage (e ≫ h)]
    simp only [a, b, spMap, ← Spec.map_comp]
    congr 1
    ext x
    show (algebraMap K B x) ⊗ₜ[K] (1 : L) = (1 : B) ⊗ₜ[K] (algebraMap K L x)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let k : Spec Z ⟶ pullback h (spMap ψ) := pullback.lift (a ≫ e) b hcomm
  have hk1 : k ≫ pullback.fst h (spMap ψ) = a ≫ e := pullback.lift_fst _ _ _
  have hk2 : k ≫ pullback.snd h (spMap ψ) = b := pullback.lift_snd _ _ _
  have heU : ⊤ ≤ e ⁻¹ᵁ U := by
    intro z _
    show e z ∈ U
    apply hVU
    have hr : e z ∈ Set.range hV.fromSpec := ⟨z, rfl⟩
    rw [hV.range_fromSpec] at hr
    exact hr
  have hk : ⊤ ≤ k ⁻¹ᵁ ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) := by
    intro z _
    show (pullback.fst h (spMap ψ)) (k z) ∈ U
    rw [← Scheme.Hom.comp_apply, hk1, Scheme.Hom.comp_apply]
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)

  have heU' : ⊤ ≤ (a ≫ e) ⁻¹ᵁ U := by
    intro z _
    exact heU (show a z ∈ (⊤ : (Spec B).Opens) from trivial)
  have key1m : (pullback.fst h (spMap ψ)).app U ≫ k.appLE _ ⊤ hk =
      e.appLE U ⊤ heU ≫ (Scheme.ΓSpecIso B).hom ≫
        CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso Z).inv := by
    refine (Scheme.Hom.comp_appLE k _ U ⊤ hk).symm.trans ?_
    refine (appLE_congr hk1 U ⊤ _ heU').trans ?_
    refine (Scheme.Hom.appLE_comp_appLE a e U ⊤ ⊤ heU (fun _ _ => trivial)).symm.trans ?_
    congr 1
    refine (appLE_top_top a _).trans ?_
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact Scheme.ΓSpecIso_naturality _
  have key2m : (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ (pullback.snd h (spMap ψ)).appTop ≫
      k.appTop = CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[K] B ⊗[K] L).toRingHom ≫
        (Scheme.ΓSpecIso Z).inv := by
    rw [← Scheme.Hom.comp_appTop, hk2, ← Scheme.ΓSpecIso_inv_naturality]
  have key1 : ∀ s : Γ(X, U), (k.appLE _ ⊤ hk).hom (((pullback.fst h (spMap ψ)).app U).hom s) =
      (Scheme.ΓSpecIso Z).inv.hom
        (((Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom s)) ⊗ₜ[K] (1 : L)) := fun s =>
    congrArg (fun φ => φ.hom s) key1m
  have key2 : (k.appLE _ ⊤ hk).hom (resTop _ (scal (pullback.snd h (spMap ψ)) l)) =
      (Scheme.ΓSpecIso Z).inv.hom ((1 : B) ⊗ₜ[K] l) := by
    have e1 : ∀ c, (k.appLE _ ⊤ hk).hom (resTop ((pullback.fst h (spMap ψ)) ⁻¹ᵁ U) c) =
        k.appTop.hom c := by
      intro c
      show ((pullback h (spMap ψ)).presheaf.map _ ≫ k.appLE _ ⊤ hk).hom c = _
      rw [Scheme.Hom.map_appLE, appLE_top_top]
    rw [e1]
    exact congrArg (fun φ => φ.hom l) key2m
  have h3 := congrArg (k.appLE _ ⊤ hk).hom heq
  rw [map_mul, key1, key1, key2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    _root_.one_mul] at h3
  have inj : Function.Injective (Scheme.ΓSpecIso Z).inv.hom := fun x y hxy => by
    simpa using congrArg (Scheme.ΓSpecIso Z).hom.hom hxy
  have h4 := inj h3
  have hb : (Scheme.ΓSpecIso B).hom.hom ((e.appLE U ⊤ heU).hom f₂) ≠ 0 := by
    rw [fromSpec_appLE_hom hV hVU heU f₂]
    exact hne
  obtain ⟨c, hc⟩ := mem_range_of_tmul_one_eq _ _ l hb h4
  exact ⟨c, hc⟩

end GlobalTheory.ConstDescent
