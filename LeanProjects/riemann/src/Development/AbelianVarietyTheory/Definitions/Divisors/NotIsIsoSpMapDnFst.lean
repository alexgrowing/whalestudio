import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

variable {S : Scheme.{0}}

def ptMap {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    Over.mk (spMap φ ≫ s) ⟶ Over.mk s := Over.homMk (spMap φ)

@[simp] theorem ptMap_left {C C' : Type} [CommRing C] [CommRing C'] (s : Sp C ⟶ S) (φ : C →+* C') :
    (ptMap s φ).left = spMap φ := rfl

abbrev dnInl (k : Type) [CommRing k] : k →+* DualNumber k := algebraMap k (DualNumber k)

abbrev dnFst (k : Type) [CommRing k] : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

structure Milnor {T T₁ T₂ T₀ : Scheme.{0}} (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T) (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) : Prop where
  aff : IsAffine T
  aff₁ : IsAffine T₁
  aff₂ : IsAffine T₂
  closed : IsClosedImmersion k₂
  w : k₁ ≫ j₁ = k₂ ≫ j₂
  cart : IsPullback j₁.appTop j₂.appTop k₁.appTop k₂.appTop

variable (A : Over S) [GrpObj A] {U : Over S} (M : LB (A ⊗ U).left)

def FieldChart : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (T : Over S) (_ : T ⟶ Over.mk s) (N : LB (A ⊗ T).left),
    Fam A N → ChartAt A M N

def TanLift : Prop :=
  ∀ (k : Type) [Field k] (s : Sp k ⟶ S) (N : LB (A ⊗ Over.mk (spMap (dnInl k) ≫ s)).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) ⟶ U, Same A N M (ptMap _ (dnFst k)) u₀ →
      ∃ u : Over.mk (spMap (dnInl k) ≫ s) ⟶ U, Same A N M (𝟙 _) u

def SmallLift : Prop :=
  ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C →
    (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (s : Sp C ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N →
    ∀ u₀ : Over.mk (spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ s) ⟶ U,
      Same A N M (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) u₀ → ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u

variable {A M}

theorem FieldChart.of_isChart (h : IsChart A M) : FieldChart A M := fun _ _ _ _ T _ N hN ↦ h.chart T N hN

theorem Milnor.id (T : Scheme.{0}) [IsAffine T] : Milnor (𝟙 T) (𝟙 T) (𝟙 T) (𝟙 T) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, rfl, by
    simpa using IsPullback.of_id_fst (f := 𝟙 Γ(T, ⊤))⟩

theorem Milnor.of_isPullback {R R₁ R₂ R₀ : CommRingCat.{0}} {a : R ⟶ R₁} {b : R ⟶ R₂} {c : R₁ ⟶ R₀} {d : R₂ ⟶ R₀}
    (h : IsPullback a b c d) (hd : Function.Surjective d) :
    Milnor (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d) where
  aff := inferInstance
  aff₁ := inferInstance
  aff₂ := inferInstance
  closed := IsClosedImmersion.spec_of_surjective d hd
  w := by rw [← Spec.map_comp, ← Spec.map_comp, h.w]
  cart := h.of_iso (Scheme.ΓSpecIso R).symm (Scheme.ΓSpecIso R₁).symm (Scheme.ΓSpecIso R₂).symm
    (Scheme.ΓSpecIso R₀).symm (by simp) (by simp) (by simp) (by simp)

theorem dnFst_surjective (k : Type) [CommRing k] : Function.Surjective (dnFst k) :=
  fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩

theorem dnFst_not_injective (k : Type) [CommRing k] [Nontrivial k] : ¬ Function.Injective (dnFst k) := fun h ↦ by
  have h1 : (DualNumber.eps : DualNumber k) = 0 := h (by rw [map_zero]; rfl)
  have h2 := congrArg TrivSqZeroExt.snd h1
  simp at h2

theorem Milnor.dualNumber (k : Type) [CommRing k] :
    Milnor (Spec.map (pullback.fst (CommRingCat.ofHom (dnFst k)) (CommRingCat.ofHom (dnFst k))))
      (Spec.map (pullback.snd (CommRingCat.ofHom (dnFst k)) (CommRingCat.ofHom (dnFst k))))
      (spMap (dnFst k)) (spMap (dnFst k)) :=
  Milnor.of_isPullback (IsPullback.of_hasPullback _ _) (dnFst_surjective k)

omit [GrpObj A] in

theorem lift_of_chartAt {C C' : Type} [CommRing C] [IsLocalRing C] [CommRing C'] [Nontrivial C'] (s : Sp C ⟶ S)
    (φ : C →+* C') (hφ : Function.Surjective φ) (N : LB (A ⊗ Over.mk s).left) (h : ChartAt A M N)
    (u₀ : Over.mk (spMap φ ≫ s) ⟶ U) (h₀ : Same A N M (ptMap s φ) u₀) :
    ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  obtain ⟨W, hW⟩ := h
  refine (hW _ (𝟙 _)).2 fun z ↦ ?_
  haveI : IsLocalRing C' := IsLocalRing.of_surjective' φ hφ
  haveI : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  have h1 := (hW _ (ptMap s φ)).1 ⟨u₀, h₀⟩ (IsLocalRing.closedPoint C')
  have h2 : IsLocalRing.closedPoint C ∈ (W : TopologicalSpace.Opens (PrimeSpectrum C)) := by
    rw [← IsLocalRing.comap_closedPoint φ]; exact h1
  have h3 := (IsLocalRing.closedPoint_mem_iff (R := C) W).1 h2
  rw [h3]; trivial

theorem TanLift.of_isChart (h : IsChart A M) : TanLift A M := fun k _ _ N hN u₀ h₀ ↦
  lift_of_chartAt _ (dnFst k) (dnFst_surjective k) N (h.chart _ N hN) u₀ h₀

theorem SmallLift.of_isChart (h : IsChart A M) : SmallLift A M := fun C _ _ e he _ s N hN u₀ h₀ ↦ by
  haveI : Nontrivial (C ⧸ Ideal.span {e}) := Ideal.Quotient.nontrivial_iff.2 (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact he)
  exact lift_of_chartAt s _ Ideal.Quotient.mk_surjective N (h.chart _ N hN) u₀ h₀

theorem not_isIso_spMap_dnFst (k : Type) [CommRing k] [Nontrivial k] : ¬ IsIso (spMap (dnFst k)) := by
  intro h
  have : IsIso (CommRingCat.ofHom (dnFst k)).op := by
    have : IsIso (Scheme.Spec.map (CommRingCat.ofHom (dnFst k)).op) := h
    exact isIso_of_reflects_iso _ Scheme.Spec
  have : IsIso (CommRingCat.ofHom (dnFst k)) := (isIso_op_iff _).1 this
  exact dnFst_not_injective k (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (dnFst k))).1

theorem dnFst_comp_dnInl (k : Type) [CommRing k] : (dnFst k).comp (dnInl k) = RingHom.id k := by
  ext x; rfl

end GlobalTheory.DualOpen
