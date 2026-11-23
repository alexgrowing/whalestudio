import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem Pt.f_congr {Z W : Scheme.{0}} {x y : Pt A B L M Z} (h : x = y) (k : W ⟶ pullback A.hom x.t)
    (k' : W ⟶ pullback A.hom y.t) (h1 : k ≫ pullback.fst _ _ = k' ≫ pullback.fst _ _)
    (h2 : k ≫ pullback.snd _ _ = k' ≫ pullback.snd _ _) : k ≫ x.f = k' ≫ y.f := by
  subst h
  have : k = k' := pullback.hom_ext h1 h2
  subst this
  rfl

theorem homFixRep_of_universal (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left)
    (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X) :
    (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) →
      ∃ (R : HomFixRep A B L M) (e : R.H ≅ X), e.hom ≫ u.t = R.π := by
  intro hu
  obtain ⟨A', B', iA, iB, φA, φB, Φ, hA, hB, hΦ, hI, e, e1, e2, e3⟩ := u.wit
  refine ⟨@HomFixRep.mk S A B _ _ L M X u.t A' iA B' iB φA φB hA hB Φ hΦ hI ?_, Iso.refl X, Category.id_comp _⟩
  intro T t A'' B'' _ _ φA' φB' Φ' hA' hB' hΦ' hI'
  let x : Pt A B L M T := Pt.ofData t A'' B'' φA' φB' Φ' hA' hB' hΦ' hI'
  have hxf : x.f = hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' := rfl

  have key : ∀ (h : T ⟶ X) (ψA : A''.left ⟶ A'.left), h ≫ u.t = t → ψA ≫ φA = φA' →
      ψA ≫ A'.hom = A''.hom ≫ h → Φ'.left ≫ φB' = ψA ≫ Φ.left ≫ φB → u.map hL hM h = x := by
    intro h ψA ht hψ1 hψ2 hf
    refine Pt.ext' ht ?_
    show pullback.lift (pullback.fst A.hom t) (pullback.snd A.hom t) (by rw [pullback.condition, ht])
      ≫ pmap A u.t h ≫ u.f = (hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' : pullback A.hom t ⟶ B.left)
    rw [← cancel_epi hA'.1.isoPullback.hom, Iso.hom_inv_id_assoc]
    have hk : hA'.1.isoPullback.hom ≫ pullback.lift (pullback.fst A.hom t) (pullback.snd _ _)
        (by rw [pullback.condition, ht] : _ = _ ≫ h ≫ u.t) ≫ pmap A u.t h = ψA ≫ e := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst, e1, hψ1]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2, hψ2]
        rw [← Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [← Category.assoc, ← Category.assoc, Category.assoc _ _ (pmap A u.t h), hk, Category.assoc, e3, hf]
  obtain ⟨c, hc, hcu⟩ := hu T x
  have hct : c ≫ u.t = t := congrArg Pt.t hc
  have wA : φA' ≫ A.hom = (A''.hom ≫ c) ≫ u.t := by rw [hA'.1.w, Category.assoc, hct]
  have wB : φB' ≫ B.hom = (B''.hom ≫ c) ≫ u.t := by rw [hB'.1.w, Category.assoc, hct]
  let ψA := hA.1.lift φA' (A''.hom ≫ c) wA
  let ψB := hB.1.lift φB' (B''.hom ≫ c) wB
  have hψA1 : ψA ≫ φA = φA' := hA.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A'.hom = A''.hom ≫ c := hA.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB = φB' := hB.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B'.hom = B''.hom ≫ c := hB.1.lift_snd _ _ _
  have gA : IsGrpPullback A'' A' c ψA := IsGrpPullback.cancel hA (hA'.congr hct.symm hψA1.symm) hψA2
  have gB : IsGrpPullback B'' B' c ψB := IsGrpPullback.cancel hB (hB'.congr hct.symm hψB1.symm) hψB2

  have hfc : Φ'.left ≫ φB' = ψA ≫ e ≫ u.f := by
    have h0 := Pt.f_congr hc
      (pullback.lift φA' A''.hom (by rw [hA'.1.w, hct]) : A''.left ⟶ pullback A.hom (c ≫ u.t))
      (hA'.1.isoPullback.hom : A''.left ⟶ pullback A.hom t)
      ((pullback.lift_fst _ _ _).trans hA'.1.isoPullback_hom_fst.symm)
      ((pullback.lift_snd _ _ _).trans hA'.1.isoPullback_hom_snd.symm)
    have hk : pullback.lift φA' A''.hom (by rw [hA'.1.w, hct]) ≫ pmap A u.t c = ψA ≫ e := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, e1, hψA1]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2, hψA2]
    change _ ≫ pmap A u.t c ≫ u.f = (hA'.1.isoPullback.hom : A''.left ⟶ pullback A.hom t) ≫
      (hA'.1.isoPullback.inv ≫ Φ'.left ≫ φB' : pullback A.hom t ⟶ B.left) at h0
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hk, Category.assoc] at h0
    exact h0.symm
  have hcomm : Φ'.left ≫ ψB = ψA ≫ Φ.left := by
    apply hB.1.hom_ext
    · rw [Category.assoc, hψB1, Category.assoc, hfc, e3]
    · rw [Category.assoc, hψB2, ← Category.assoc, Over.w Φ', Category.assoc, Over.w Φ, hψA2]
  refine ⟨c, ⟨hct, ψA, ψB, gA, gB, hψA1, hψB1, hcomm⟩, ?_⟩
  rintro h ⟨ht, χA, χB, kA, kB, kA1, kB1, kcomm⟩
  have hx : u.map hL hM h = x := key h χA ht kA1 kA.1.w (by
    rw [← kB1, ← Category.assoc, kcomm, Category.assoc])
  exact (hcu h hx)

end GlobalTheory.EndLoc.HomGlue
