import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing

noncomputable section

theorem continuous_equiv_symm_of_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ Y) (h : X ≃ₜ Y) (he : ∀ x, e x = h x) : Continuous e.symm :=
  h.symm.continuous.congr fun y ↦ e.injective (by rw [e.apply_symm_apply, he, h.apply_symm_apply])

def unitsContinuousMulEquiv {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃* B) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    Aˣ ≃ₜ* Bˣ where
  toMulEquiv := Units.mapEquiv e
  continuous_toFun := Units.continuous_map (f := e.toMonoidHom) h₁
  continuous_invFun := Units.continuous_map (f := e.symm.toMonoidHom) h₂

def continuousMulEquivProdCongr {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e₁ : A ≃ₜ* B) (e₂ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  toMulEquiv := MulEquiv.prodCongr e₁.toMulEquiv e₂.toMulEquiv
  continuous_toFun := by
    exact (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd)
  continuous_invFun := by
    exact (e₁.symm.continuous.comp continuous_fst).prodMk (e₂.symm.continuous.comp continuous_snd)

def openSubgroupEquivQuotient {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H N : Subgroup G) (hH : IsOpen (H : Set G)) (hinf : H ⊓ N = ⊥)
    (hsup : H ⊔ N = ⊤) : H ≃ₜ* G ⧸ N :=
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h2 : (h : G) ∈ H ⊓ N := ⟨h.2, (QuotientGroup.eq_one_iff _).1 hh⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ H ⊔ N := hsup ▸ Subgroup.mem_top g
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup.1 hg
    refine ⟨⟨h, hh⟩, ?_⟩
    show ((h : G) : G ⧸ N) = ((h * n : G) : G ⧸ N)
    exact QuotientGroup.eq.2 (by rwa [inv_mul_cancel_left])
  let e : H ≃* G ⧸ N := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hc : Continuous e := QuotientGroup.continuous_mk.comp continuous_subtype_val
  have ho : IsOpenMap e := QuotientGroup.isOpenMap_coe.comp hH.isOpenMap_subtype_val
  { toMulEquiv := e
    continuous_toFun := hc
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }

@[simp]
theorem openSubgroupEquivQuotient_apply {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H N : Subgroup G) (hH : IsOpen (H : Set G)) (hinf : H ⊓ N = ⊥)
    (hsup : H ⊔ N = ⊤) (h : H) :
    openSubgroupEquivQuotient H N hH hinf hsup h = ((h : G) : G ⧸ N) :=
  rfl

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

def localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) (x : standardOpenSubgroup K) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨((x : IdeleGroup K) : 𝔸[K]).2 v, ((mem_standardOpenSubgroup K).1 x.2 v).1⟩
  inv := ⟨(((x : IdeleGroup K)⁻¹ : IdeleGroup K) : 𝔸[K]).2 v,
    ((mem_standardOpenSubgroup K).1 x.2 v).2⟩
  val_inv := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).mul_inv)
  inv_val := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).inv_mul)

@[simp]
theorem coe_localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) (x : standardOpenSubgroup K) :
    (((localIntegerUnit v x : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
      v.adicCompletion K) = ((x : IdeleGroup K) : 𝔸[K]).2 v :=
  rfl

theorem continuous_localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localIntegerUnit (K := K) v) := by
  rw [Units.continuous_iff]
  constructor
  · exact ((Units.continuous_val.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _
  · exact ((Units.continuous_coe_inv.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _

def ofIntegerUnits (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) : IdeleGroup K where
  val := ((a : InfiniteAdeleRing K),
    _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ (u v : v.adicCompletionIntegers K))
  inv := (((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
    _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ ((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ))
  val_inv := Prod.ext a.mul_inv (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).mul_inv))
  inv_val := Prod.ext a.inv_mul (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).inv_mul))

@[simp]
theorem coe_ofIntegerUnits_fst (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    ((ofIntegerUnits a u : IdeleGroup K) : 𝔸[K]).1 = a :=
  rfl

@[simp]
theorem coe_ofIntegerUnits_snd (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((ofIntegerUnits a u : IdeleGroup K) : 𝔸[K]).2 v =
      ((u v : v.adicCompletionIntegers K) : v.adicCompletion K) :=
  rfl

theorem ofIntegerUnits_mem (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    ofIntegerUnits a u ∈ standardOpenSubgroup K :=
  (mem_standardOpenSubgroup K).2 fun v ↦
    ⟨(u v : v.adicCompletionIntegers K).2, (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K).2⟩

theorem continuous_ofIntegerUnits :
    Continuous (fun p : (InfiniteAdeleRing K)ˣ ×
        (Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) ↦
      ofIntegerUnits p.1 p.2) := by
  rw [Units.continuous_iff]
  constructor
  · exact (Units.continuous_val.comp continuous_fst).prodMk
      (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp
        (continuous_pi fun v ↦ Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)))
  · exact (Units.continuous_coe_inv.comp continuous_fst).prodMk
      (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp
        (continuous_pi fun v ↦
          Units.continuous_coe_inv.comp ((continuous_apply v).comp continuous_snd)))

variable (K) in

def standardOpenSubgroupEquiv :
    standardOpenSubgroup K ≃ₜ* (InfiniteAdeleRing K)ˣ ×
      Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ where
  toFun x := (toInfinite K (x : IdeleGroup K), fun v ↦ localIntegerUnit v x)
  invFun p := ⟨ofIntegerUnits p.1 p.2, ofIntegerUnits_mem p.1 p.2⟩
  left_inv _ := Subtype.ext (Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl))))
  right_inv _ := Prod.ext (Units.ext rfl) (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (map_mul (toInfinite K) (x : IdeleGroup K) y)
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := ((continuous_toInfinite K).comp continuous_subtype_val).prodMk
    (continuous_pi fun v ↦ continuous_localIntegerUnit v)
  continuous_invFun := continuous_ofIntegerUnits.subtype_mk _

@[simp]
theorem standardOpenSubgroupEquiv_apply_fst (x : standardOpenSubgroup K) :
    (standardOpenSubgroupEquiv K x).1 = toInfinite K (x : IdeleGroup K) :=
  rfl

@[simp]
theorem standardOpenSubgroupEquiv_apply_snd (x : standardOpenSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (standardOpenSubgroupEquiv K x).2 v = localIntegerUnit v x :=
  rfl

@[simp]
theorem coe_standardOpenSubgroupEquiv_symm_apply
    (p : (InfiniteAdeleRing K)ˣ × Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    (((standardOpenSubgroupEquiv K).symm p : standardOpenSubgroup K) : IdeleGroup K) =
      ofIntegerUnits p.1 p.2 :=
  rfl

end IdeleGroup

end

end GroundTheory.Global
