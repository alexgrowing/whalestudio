import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsStrictlySemistableIff
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SmChart

open MvPolynomial

noncomputable def subst {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin n) O :=
  Fin.cases (C ϖ) (fun j => X j) i

@[simp] theorem subst_zero {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : subst ϖ n 0 = C ϖ := rfl
@[simp] theorem subst_succ {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (j : Fin n) : subst ϖ n j.succ = X j := rfl

theorem prod_lt_one {O : Type} [CommRing O] (n : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (X i : MvPolynomial (Fin (n + 1)) O)) = X 0 := by
  have : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext (by simpa using h)
    · rintro rfl; simp
  rw [this, Finset.prod_singleton]

noncomputable abbrev gen {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {X 0 - C ϖ}

theorem subst_vanish {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ a ∈ gen ϖ n, (aeval (subst ϖ n)).toRingHom a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_sub, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X, aeval_C, subst_zero,
    algebraMap_eq, sub_self, mul_zero]

noncomputable def quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (aeval (subst ϖ n)).toRingHom (subst_vanish ϖ n)

noncomputable def quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) :=
  (Ideal.Quotient.mk _).comp (rename Fin.succ).toRingHom

theorem quotMap_mk {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (a : MvPolynomial (Fin (n + 1)) O) :
    quotMap ϖ n (Ideal.Quotient.mk _ a) = aeval (subst ϖ n) a := rfl

theorem quotMap_quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (quotInv ϖ n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    simp [quotInv, quotMap_mk]

theorem quotInv_quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotInv ϖ n).comp (quotMap ϖ n) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [RingHom.comp_apply, quotMap_mk, aeval_X, subst_zero, RingHom.id_apply]
      simp only [quotInv, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_C]
      rw [Ideal.Quotient.eq]
      rw [← neg_sub]; exact neg_mem (Ideal.subset_span rfl)
    · simp [quotInv, quotMap_mk]

theorem quotMap_bijective {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Function.Bijective (quotMap ϖ n) :=
  ⟨Function.LeftInverse.injective (g := quotInv ϖ n) (fun a => congr($(quotInv_quotMap ϖ n) a)),
    Function.RightInverse.surjective (g := quotInv ϖ n) (fun a => congr($(quotMap_quotInv ϖ n) a))⟩

theorem quotMap_algebraMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (algebraMap O _) = C := by
  refine RingHom.ext fun c => ?_
  change quotMap ϖ n (Ideal.Quotient.mk _ (C c)) = C c
  rw [quotMap_mk, aeval_C, algebraMap_eq]

end GlobalTheory.SmChart

open GlobalTheory.SmChart in

theorem GlobalTheory.SSG.chartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) →
    GlobalTheory.SSG.ChartAt ϖ p x := by
  intro O _ ϖ X p V x hx hsm
  set f := V.ι ≫ p with hf
  let x' : V.toScheme := ⟨x, hx⟩
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.toScheme.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x')
  have hW : IsAffineOpen W := hW
  have e : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hφ : (f.appLE ⊤ W e).hom.Smooth := f.smooth_appLE (isAffineOpen_top _) hW e
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hφ
  obtain ⟨s, hs, hfs⟩ := hφ
  have hs' := iSup_basicOpen_of_span_eq_top W (s : Set Γ(V.toScheme, W)) hs
  have hmem : x' ∈ (⨆ i ∈ (s : Set Γ(V.toScheme, W)), V.toScheme.basicOpen i) := hs'.symm ▸ hxW
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x' ∈ V.toScheme.basicOpen r := by simpa using hmem
  have hW' : IsAffineOpen (V.toScheme.basicOpen r) := hW.basicOpen r
  have e' : V.toScheme.basicOpen r ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  haveI : IsLocalization.Away r Γ(V.toScheme, V.toScheme.basicOpen r) := hW.isLocalization_basicOpen r
  have hst : (f.appLE ⊤ _ e').hom.IsStandardSmooth := by
    rw [← f.appLE_map e (homOfLE (V.toScheme.basicOpen_le r)).op]
    exact hfs r hr _
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hst
  let c : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hc : Function.Bijective c := (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.bijective
  let k := V.ι.appIso (V.toScheme.basicOpen r)
  have hk : Function.Bijective k.inv.hom := k.symm.commRingCatIsoToRingEquiv.bijective
  have hU : IsAffineOpen (V.ι ''ᵁ V.toScheme.basicOpen r) := hW'.image_of_isOpenImmersion V.ι
  have hxU : x ∈ V.ι ''ᵁ V.toScheme.basicOpen r := ⟨x', hxr, rfl⟩
  have hcomp : p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top ≫ k.hom = f.appLE ⊤ _ e' := by
    have h1 := Scheme.Hom.appLE_comp_appLE V.ι p ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) (V.toScheme.basicOpen r)
      le_top (V.ι.preimage_image_eq _).ge
    have h2 : k.hom = V.ι.appLE _ _ (V.ι.preimage_image_eq _).ge := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]; rfl
    rw [h2]; exact h1
  refine ⟨_, hU, hxU, n + 1, 1, le_rfl, by omega, ?_⟩
  rw [prod_lt_one]
  refine ⟨k.inv.hom.comp (g.comp ((MvPolynomial.map c).comp (quotMap ϖ n))), ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (quotMap_bijective ϖ n))
          (RingHom.Etale.of_bijective ⟨MvPolynomial.map_injective _ hc.1, MvPolynomial.map_surjective _ hc.2⟩))
        hg) (RingHom.Etale.of_bijective hk)
  · refine RingHom.ext fun a => ?_
    change k.inv.hom (g (MvPolynomial.map c (quotMap ϖ n (algebraMap O _ a)))) =
      (p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top).hom (c a)
    rw [show quotMap ϖ n (algebraMap O _ a) = MvPolynomial.C a from congr($(quotMap_algebraMap ϖ n) a),
      MvPolynomial.map_C, show g (MvPolynomial.C (c a)) = (f.appLE ⊤ _ e').hom (c a) from congr($hgC (c a)),
      ← hcomp]
    simp
