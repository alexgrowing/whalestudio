import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainFibFinite
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.TangentStalk

theorem ker_eq_maximalIdeal {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g : R →+* k) (hg : g.comp j = RingHom.id k) : RingHom.ker g = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g
    (fun c => ⟨j c, RingHom.congr_fun hg c⟩))

theorem ringHom_eq_of_comp_eq_id {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g₁ g₂ : R →+* k) (h₁ : g₁.comp j = RingHom.id k) (h₂ : g₂.comp j = RingHom.id k) : g₁ = g₂ := by
  ext a
  have hm : a - j (g₁ a) ∈ RingHom.ker g₂ := by
    rw [ker_eq_maximalIdeal j g₂ h₂, ← ker_eq_maximalIdeal j g₁ h₁, RingHom.mem_ker, map_sub,
      show g₁ (j (g₁ a)) = g₁ a from RingHom.congr_fun h₁ (g₁ a), sub_self]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  rw [hm]
  exact (RingHom.congr_fun h₂ (g₁ a)).symm

theorem tangent_eq_stalk_dual : ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (x₀ : A.left), x₀ ∈ Set.range (η[A]).left.base →
    ∃ jk : k →+* A.left.presheaf.stalk x₀,
      (∀ a : A.left.presheaf.stalk x₀, ∃ c : k, a - jk c ∈ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀)) ∧
      (∀ ψ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ.comp jk = algebraMap k (DualNumber k) →
        ∃ v : epsR k ⟶ A, IsTangent v ∧ v.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ∧
      (∀ ψ₁ ψ₂ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ₁.comp jk = algebraMap k (DualNumber k) →
        ψ₂.comp jk = algebraMap k (DualNumber k) →
        Spec.map (CommRingCat.ofHom ψ₁) ≫ A.left.fromSpecStalk x₀ = Spec.map (CommRingCat.ofHom ψ₂) ≫ A.left.fromSpecStalk x₀ →
        ψ₁ = ψ₂) := by
  intro k _ A _ x₀ hx
  obtain ⟨pt, rfl⟩ := hx
  have hpt : pt = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  subst hpt
  let s : Sp k ⟶ A.left := (η[A]).left
  have hsA : s ≫ A.hom = 𝟙 _ := (η[A]).w.trans rfl
  have hr : Spec.map (Scheme.stalkClosedPointTo s) ≫ A.left.fromSpecStalk _ = s :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  have hJ := Spec.map_preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom)

  set r := Scheme.stalkClosedPointTo s with hrdef
  set J := Spec.preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom) with hJdef
  have hrJ : J ≫ r = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hJ, ← Category.assoc, hr, hsA, Spec.map_id]
  have hcomp : r.hom.comp J.hom = RingHom.id k := congrArg CommRingCat.Hom.hom hrJ
  have hfst : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
      ψ.comp J.hom = algebraMap k (DualNumber k) →
      ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ψ).comp J.hom = RingHom.id k := by
    intro ψ hψ
    rw [RingHom.comp_assoc, hψ]
    ext c
    simp
  refine ⟨J.hom, fun a => ⟨r.hom a, ?_⟩, fun ψ hψ => ?_, fun ψ₁ ψ₂ h₁ h₂ h => ?_⟩
  · rw [← ker_eq_maximalIdeal J.hom r.hom hcomp, RingHom.mem_ker, map_sub,
      show r.hom (J.hom (r.hom a)) = r.hom a from RingHom.congr_fun hcomp _, sub_self]
  · refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _) ?_, ?_, rfl⟩
    · show Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ ≫ A.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      rw [← hJ, ← Spec.map_comp, ← hψ]
      rfl
    · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ = s
      rw [← Category.assoc, ← Spec.map_comp, ← hr]
      congr 2
      ext1
      exact ringHom_eq_of_comp_eq_id J.hom _ _ (hfst ψ hψ) hcomp
  · have hloc : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
        ψ.comp J.hom = algebraMap k (DualNumber k) → IsLocalHom ψ := by
      intro ψ hψ
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have hm : a ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
      rw [← ker_eq_maximalIdeal J.hom _ (hfst ψ hψ), RingHom.mem_ker] at hm
      have hu := TrivSqZeroExt.isUnit_iff_isUnit_fst.1 ha
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        TrivSqZeroExt.fstHom_apply] at hm
      rw [hm] at hu
      exact not_isUnit_zero hu
    have e1 := hloc ψ₁ h₁
    have e2 := hloc ψ₂ h₂
    have hinj := (SpecToEquivOfLocalRing A.left (CommRingCat.of (DualNumber k))).symm.injective
      (a₁ := ⟨_, CommRingCat.ofHom ψ₁, e1⟩) (a₂ := ⟨_, CommRingCat.ofHom ψ₂, e2⟩) h
    have := eq_of_heq (Sigma.mk.inj_iff.mp hinj).2
    exact congrArg (fun f => f.1.hom) this
end GlobalTheory.TangentStalk
