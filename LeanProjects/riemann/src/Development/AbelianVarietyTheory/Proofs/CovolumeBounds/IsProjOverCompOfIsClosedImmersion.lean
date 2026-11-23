import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionSigmaDesc

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace

variable {R : Type} [CommRing R] {N : ℕ} {A B : Type} [CommRing A] [CommRing B] {Y Z : Scheme.{0}}

theorem isUnit_of_basicOpen_eq {U : Y.Opens} (s : Γ(Y, U)) (h : Y.basicOpen s = U) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

theorem fromSpec_appLE_self {U : Y.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

def spOpen (a : A) : (Sp A).Opens := PrimeSpectrum.basicOpen a

theorem mem_spOpen {a : A} {x : Sp A} : x ∈ spOpen a ↔ a ∉ x.asIdeal := Iff.rfl

theorem iSup_spOpen_eq_top_iff {ι : Type} {v : ι → A} :
    ⨆ i, spOpen (v i) = ⊤ ↔ Ideal.span (Set.range v) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff

def fnOn (W : (Sp A).Opens) : A →+* Γ(Sp A, W) :=
  (resG (Sp A) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem resG_fnOn {W V : (Sp A).Opens} (h : V ≤ W) (a : A) : resG _ h (fnOn W a) = fnOn V a :=
  resG_resG _ _ _

theorem basicOpen_fnOn (W : (Sp A).Opens) (a : A) :
    (Sp A).basicOpen (fnOn W a) = W ⊓ spOpen a := by
  refine (Scheme.basicOpen_res _ _ _).trans ?_
  exact congrArg (W ⊓ ·) (basicOpen_eq_of_affine (R := .of A) a)

theorem fnOn_top_bijective : Function.Bijective (fnOn (A := A) ⊤) := by
  have : ⇑(fnOn (A := A) ⊤) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    funext fun a => resG_self (X := Sp A) le_top _
  rw [this]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv

theorem fromSpec_eq_spMap_fnOn {W : (Sp A).Opens} (hW : IsAffineOpen W) :
    hW.fromSpec = spMap (R' := Γ(Sp A, W)) (fnOn W) := by
  have h := IsAffineOpen.map_fromSpec (isAffineOpen_top (Sp A)) hW (homOfLE le_top).op
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem map_irrelevant_eval₂Hom (c : R →+* A) {v : Fin (N + 1) → A} (hv : Ideal.span (Set.range v) = ⊤) :
    (HomogeneousIdeal.irrelevant (grading R N)).toIdeal.map (eval₂Hom c v) = ⊤ := by
  rw [eq_top_iff, ← hv, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← eval₂Hom_X' c v i]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem R N i))

def pt (c : R →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) : Sp A ⟶ PSpace R N :=
  ProjPoint.ofHom (grading R N) (eval₂Hom c v) (map_irrelevant_eval₂Hom c hv)

section

variable (c : R →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)

@[reassoc] theorem pt_str : pt c v hv ≫ PSpace.str R N = spMap c := by
  rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun r => eval₂Hom_C c v r

theorem pt_preimage_basicOpen {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    pt c v hv ⁻¹ᵁ Proj.basicOpen (grading R N) f = spOpen (eval₂ c v f) :=
  ProjPoint.ofHom_preimage_basicOpen _ _ _ hn hf

theorem pt_preimage_chart (i : Fin (N + 1)) : pt c v hv ⁻¹ᵁ chart R N i = spOpen (v i) := by
  rw [pt_preimage_basicOpen c v hv one_pos (isHomogeneous_X R i), eval₂_X]

include hv in

theorem span_range_comp_eq_top (ψ : A →+* B) : Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
  rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]

@[reassoc] theorem spMap_pt (ψ : A →+* B) :
    spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
  refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
  unfold pt
  congr 1
  exact ringHom_ext (fun r => by simp) (fun i => by simp)

@[reassoc] theorem pt_baseChange {R₀ : Type} [CommRing R₀] (φ : R₀ →+* R) :
    pt c v hv ≫ baseChange N φ = pt (c.comp φ) v hv := by
  refine (ProjPoint.ofHom_map _ _ _ _).trans ?_
  unfold pt
  congr 1
  exact ringHom_ext (fun r => by simp) (fun i => by simp)

theorem fromSpec_chart (i : Fin (N + 1)) : (isAffineOpen_chart R N i).fromSpec =
    Spec.map (Proj.awayToSection (grading R N) (X i)) ≫
      Proj.awayι (grading R N) (X i) (X_mem R N i) one_pos := by
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
  refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
  exact (Proj.basicOpenIsoSpec (grading R N) (X i) (X_mem R N i) one_pos).hom_inv_id.symm

theorem awayToSection_ratioAway (i j : Fin (N + 1)) :
    (Proj.awayToSection (grading R N) (X i)).hom (ratioAway R N i j) = ratio R N i j := by
  rw [ratioAway, awayToSection_mk]
  exact frac_eq (by ring)

theorem pullRatio_spMap_awayι (i j : Fin (N + 1)) (ρ : HomogeneousLocalization.Away (grading R N) (X i) →+* A)
    (h : ⊤ ≤ (spMap ρ ≫ Proj.awayι (grading R N) (X i) (X_mem R N i) one_pos) ⁻¹ᵁ chart R N i) :
    pullRatio (spMap ρ ≫ Proj.awayι (grading R N) (X i) (X_mem R N i) one_pos) ⊤ i h j =
      fnOn ⊤ (ρ (ratioAway R N i j)) := by
  have : IsIso (Proj.awayToSection (grading R N) (X i)) :=
    (Proj.basicOpenIsoAway (grading R N) (X i) (X_mem R N i) one_pos).isIso_hom
  have h2 : spMap ρ ≫ Proj.awayι (grading R N) (X i) (X_mem R N i) one_pos =
      ofChartHom i (inv (Proj.awayToSection (grading R N) (X i)) ≫ CommRingCat.ofHom ρ ≫
        (Scheme.ΓSpecIso (.of A)).inv) := by
    rw [ofChartHom, fromSpec_chart, ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
  rw [pullRatio_of_eq h2 h (ofChartHom_preimage _ _), pullRatio, ofChartHom_appLE, ← awayToSection_ratioAway,
    ← CommRingCat.comp_apply, IsIso.hom_inv_id_assoc]
  exact (resG_self (X := Sp A) le_top _).symm

theorem pullRatio_pt_top_mul (i j : Fin (N + 1)) (hu : IsUnit (v i)) (h : ⊤ ≤ pt c v hv ⁻¹ᵁ chart R N i) :
    pullRatio (pt c v hv) ⊤ i h j * fnOn ⊤ (v i) = fnOn ⊤ (v j) := by
  have hu' : IsUnit (eval₂Hom c v (X i)) := by rwa [eval₂Hom_X']
  have h2 : pt c v hv = spMap (ProjPoint.awayLift (grading R N) (eval₂Hom c v) (X i) hu') ≫ _ :=
    ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem R N i) hu'
  have h4 := ProjPoint.awayLift_mk_mul (grading R N) (eval₂Hom c v) hu' (X_mem R N i) 1 (X j) (X_mem R N j)
  rw [pullRatio_of_eq h2 h (h2 ▸ h), pullRatio_spMap_awayι, ← map_mul]
  refine congrArg _ ?_
  simpa only [ratioAway, eval₂Hom_X', pow_one] using h4

theorem pullRatio_pt_mul {W : (Sp A).Opens} (i j : Fin (N + 1)) (h : W ≤ pt c v hv ⁻¹ᵁ chart R N i) :
    pullRatio (pt c v hv) W i h j * fnOn W (v i) = fnOn W (v j) := by
  have e := pt_preimage_chart c v hv i
  have key : ∀ (U : (Sp A).Opens) (hU : IsAffineOpen U) (h : U ≤ pt c v hv ⁻¹ᵁ chart R N i),
      pullRatio (pt c v hv) U i h j * fnOn U (v i) = fnOn U (v j) := by
    intro U hU h
    have hu : IsUnit (fnOn U (v i)) := isUnit_of_basicOpen_eq _ (by rw [basicOpen_fnOn, ← e, inf_eq_left.2 h])
    have h0 : ⊤ ≤ spMap (R' := Γ(Sp A, U)) (fnOn U) ⁻¹ᵁ U := by
      rw [← fromSpec_eq_spMap_fnOn hU, hU.fromSpec_preimage_self]
    have h1 : (spMap (R' := Γ(Sp A, U)) (fnOn U)).appLE U ⊤ h0 = (Scheme.ΓSpecIso _).inv := by
      exact (appLE_of_eq (fromSpec_eq_spMap_fnOn hU).symm _ _ h0 hU.fromSpec_preimage_self.ge).trans
        (fromSpec_appLE_self hU)
    have h2 : ∀ a, fnOn ⊤ a = ((spMap (R' := Γ(Sp A, U)) (fnOn U)).appLE U ⊤ h0).hom a := fun a => by
      rw [h1]
      exact resG_self (X := Sp Γ(Sp A, U)) le_top _
    refine fnOn_top_bijective.1 ?_
    have h3 := spMap_pt (B := Γ(Sp A, U)) c v hv (fnOn U)
    have h4 : ⊤ ≤ (spMap (R' := Γ(Sp A, U)) (fnOn U) ≫ pt c v hv) ⁻¹ᵁ chart R N i :=
      h0.trans ((spMap (R' := Γ(Sp A, U)) (fnOn U)).preimage_mono h)
    rw [map_mul, h2, appLE_pullRatio, pullRatio_of_eq h3 h4 (h3 ▸ h4)]
    exact pullRatio_pt_top_mul _ _ _ i j hu _
  have := congrArg (resG _ h) (key _ (e ▸ (IsAffineOpen.Spec_basicOpen (R := .of A) (v i) : IsAffineOpen (spOpen (v i)))) le_rfl)
  rwa [map_mul, resG_pullRatio, resG_fnOn, resG_fnOn] at this

end

theorem eq_zero_of_fnOn_eq_zero {ι : Type} {v : ι → A} (hv : Ideal.span (Set.range v) = ⊤) {a : A}
    (h : ∀ i, fnOn (spOpen (v i)) a = 0) : a = 0 := by
  refine fnOn_top_bijective.1 ((ext_germ fun y hy => ?_).trans (map_zero _).symm)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1
    ((iSup_spOpen_eq_top_iff.2 hv).ge (Set.mem_univ y))
  have := congrArg ((Sp A).presheaf.germ (spOpen (v i)) y hi).hom (h i)
  rwa [← resG_fnOn (le_top : _ ≤ ⊤), germ_resG, map_zero, ← map_zero ((Sp A).presheaf.germ ⊤ y hy).hom] at this

theorem exists_unit_smul_of_mul_eq {ι : Type} [Finite ι] {v w : ι → A} (hv : Ideal.span (Set.range v) = ⊤)
    (hw : Ideal.span (Set.range w) = ⊤) (h : ∀ i j, v i * w j = v j * w i) : ∃ u : Aˣ, w = u • v := by
  have := Fintype.ofFinite ι
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hv.ge (Submodule.mem_top (x := 1)))
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hw.ge (Submodule.mem_top (x := 1)))
  have h1 : ∀ j, (∑ i, a i * w i) * v j = w j := fun j => by
    rw [Finset.sum_mul, ← one_mul (w j), ← ha, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, mul_assoc, h i j, mul_comm (w i)]
  have h2 : (∑ i, a i * w i) * ∑ j, b j * v j = 1 := by
    rw [Finset.mul_sum, ← hb]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_left_comm, h1]
  exact ⟨Units.mkOfMulEqOne _ _ h2, funext fun j => (h1 j).symm⟩

theorem span_range_units_smul {ι : Type} {v : ι → A} (hv : Ideal.span (Set.range v) = ⊤) (u : Aˣ) :
    Ideal.span (Set.range (u • v)) = ⊤ := by
  rw [eq_top_iff, ← hv, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have := Ideal.mul_mem_left _ (u⁻¹ : Aˣ).val (Ideal.subset_span ⟨i, rfl⟩ : (u • v) i ∈ Ideal.span (Set.range (u • v)))
  rwa [Pi.smul_apply, Units.smul_def u (v i), smul_eq_mul, Units.inv_mul_cancel_left] at this

theorem pt_units_smul (c : R →+* A) {v : Fin (N + 1) → A} (hv : Ideal.span (Set.range v) = ⊤) (u : Aˣ) :
    pt c (u • v) (span_range_units_smul hv u) = pt c v hv :=
  ProjPoint.ofHom_eq_of_scale _ _ _ u.val fun n f hf => by
    have := ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous c v u.val hf
    rw [coe_eval₂Hom, coe_eval₂Hom, mul_comm, ← this]
    congr 1
    exact funext fun i => mul_comm _ _

theorem pt_eq_pt_iff (c : R →+* A) {v w : Fin (N + 1) → A} (hv : Ideal.span (Set.range v) = ⊤)
    (hw : Ideal.span (Set.range w) = ⊤) : pt c v hv = pt c w hw ↔ ∃ u : Aˣ, w = u • v := by
  refine ⟨fun h => exists_unit_smul_of_mul_eq hv hw fun i j => ?_, ?_⟩
  · refine sub_eq_zero.1 (eq_zero_of_fnOn_eq_zero hv fun k => ?_)
    have hk := (pt_preimage_chart c v hv k).ge
    have e := fun l => pullRatio_pt_mul c w hw k l (h ▸ hk)
    simp only [← pullRatio_of_eq h hk] at e
    rw [map_sub, map_mul, map_mul, ← pullRatio_pt_mul c v hv k i hk, ← pullRatio_pt_mul c v hv k j hk,
      ← e i, ← e j]
    ring
  · rintro ⟨u, rfl⟩
    exact (pt_units_smul c hv u).symm

theorem eq_pt {c : R →+* A} {v : Fin (N + 1) → A} (hv : Ideal.span (Set.range v) = ⊤) {φ : Sp A ⟶ PSpace R N}
    (hφ : φ ≫ PSpace.str R N = spMap c) (h : ∀ i, spOpen (v i) ≤ φ ⁻¹ᵁ chart R N i)
    (H : ∀ i j, pullRatio φ _ i (h i) j * fnOn _ (v i) = fnOn _ (v j)) : φ = pt c v hv := by
  refine hom_ext (hφ.trans (pt_str c v hv).symm) fun y => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1
    ((iSup_spOpen_eq_top_iff.2 hv).ge (Set.mem_univ y))
  refine ⟨_, hi, i, h i, (pt_preimage_chart c v hv i).ge, fun j => ?_⟩
  refine (isUnit_of_basicOpen_eq (fnOn _ (v i)) (by rw [basicOpen_fnOn, inf_idem])).mul_right_cancel ?_
  rw [H, pullRatio_pt_mul]

theorem exists_eq_pt_of_isGen (c : R →+* A) (φ : Sp A ⟶ PSpace R N) (hφ : φ ≫ PSpace.str R N = spMap c)
    (t : ((O1 R N).pull φ).Gen) (ht : t.IsGen) :
    ∃ (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤), φ = pt c v hv := by
  have hL := LB.isLB_pull (O1_isLB R N) φ
  let a := ReciprocityTheory.ChartRestriction.G.DVR.genSec t ht
  have ha : ⊤ ≤ nonzeroLocus a := (nonzeroLocus_genSec hL t ht).ge
  choose v hv using fun j => fnOn_top_bijective.2 (resG _ ha (secRatio a (secPull (coord R N j) φ)))
  have hb : ∀ j, spOpen (v j) = φ ⁻¹ᵁ chart R N j := fun j => by
    have := basicOpen_fnOn ⊤ (v j)
    rw [hv, top_inf_eq] at this
    refine this.symm.trans ((Scheme.basicOpen_res _ _ _).trans ?_)
    rw [basicOpen_secRatio, nonzeroLocus_secPull, nonzeroLocus_coord, top_le_iff.1 ha, top_inf_eq, top_inf_eq]
    rfl
  have hspan : Ideal.span (Set.range v) = ⊤ := by
    refine iSup_spOpen_eq_top_iff.1 ((iSup_congr hb).trans ?_)
    exact (isCoordFamily_pullRatio φ).cover
  refine ⟨v, hspan, eq_pt hspan hφ (fun i => (hb i).le) fun i j => ?_⟩
  have hW : spOpen (v i) ≤ ((O1 R N).pull φ).U fun _ => i :=
    (hb i).le.trans (pull_U (O1 R N) φ fun _ => i).ge
  have e : ∀ l, pullRatio φ _ i (hb i).le l = fnOn _ (v l) * resG _ hW (a.f fun _ => i) := fun l => by
    rw [← resG_fnOn (le_top : _ ≤ ⊤), hv, resG_resG]
    exact (resG_secPull_coord φ l (fun _ => i) hW).symm.trans (secRatio_on a _ (fun _ => i) _ hW)
  rw [e j, mul_assoc, mul_comm _ (fnOn _ (v i)), ← e i, pullRatio_self, mul_one]

theorem exists_eq_pt [Subsingleton (CommRing.Pic A)] (c : R →+* A) (φ : Sp A ⟶ PSpace R N)
    (hφ : φ ≫ PSpace.str R N = spMap c) :
    ∃ (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤), φ = pt c v hv :=
  (GlobalTheory.LB.exists_isGen_of_subsingleton_pic (LB.isLB_pull (O1_isLB R N) φ)).elim fun t ht =>
    exists_eq_pt_of_isGen c φ hφ t ht

abbrev Unimodular (A : Type) [CommRing A] (N : ℕ) : Type :=
  {v : Fin (N + 1) → A // Ideal.span (Set.range v) = ⊤}

def unitSetoid (A : Type) [CommRing A] (N : ℕ) : Setoid (Unimodular A N) where
  r v w := ∃ u : Aˣ, w.1 = u • v.1
  iseqv := ⟨fun _ => ⟨1, (one_smul _ _).symm⟩, fun ⟨u, h⟩ => ⟨u⁻¹, by rw [h, inv_smul_smul]⟩,
    fun ⟨u, h⟩ ⟨u', h'⟩ => ⟨u' * u, by rw [h', h, mul_smul]⟩⟩

def ptEquiv [Subsingleton (CommRing.Pic A)] (c : R →+* A) (N : ℕ) :
    Quotient (unitSetoid A N) ≃ {φ : Sp A ⟶ PSpace R N // φ ≫ PSpace.str R N = spMap c} :=
  Equiv.ofBijective (Quotient.lift (fun v => ⟨pt c v.1 v.2, pt_str c v.1 v.2⟩)
      fun v w h => Subtype.ext ((pt_eq_pt_iff c v.2 w.2).2 h))
    ⟨fun a b => Quotient.inductionOn₂ a b fun v w h =>
        Quotient.sound ((pt_eq_pt_iff c v.2 w.2).1 (congrArg Subtype.val h)),
      fun φ => (exists_eq_pt c φ.1 φ.2).elim fun v h => h.elim fun hv e =>
        ⟨Quotient.mk _ ⟨v, hv⟩, Subtype.ext e.symm⟩⟩

@[simp] theorem ptEquiv_mk [Subsingleton (CommRing.Pic A)] (c : R →+* A) (v : Unimodular A N) :
    (ptEquiv c N (Quotient.mk _ v)).1 = pt c v.1 v.2 := rfl

theorem span_range_eq_top_iff_of_isLocalRing [IsLocalRing A] {ι : Type} {v : ι → A} :
    Ideal.span (Set.range v) = ⊤ ↔ ∃ i, IsUnit (v i) := by
  refine ⟨fun h => ?_, fun ⟨i, hi⟩ => Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi⟩
  by_contra! H
  refine (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h.ge.trans (Ideal.span_le.2 ?_)))
  rintro _ ⟨i, rfl⟩
  exact H i

theorem span_range_eq_top_iff_ne_zero {K : Type} [Field K] {ι : Type} {v : ι → K} :
    Ideal.span (Set.range v) = ⊤ ↔ v ≠ 0 := by
  simp only [span_range_eq_top_iff_of_isLocalRing, isUnit_iff_ne_zero, Function.ne_iff, Pi.zero_apply]

theorem pt_eq_pt_of_injective (c : R →+* A) {ψ : A →+* B} (hψ : Function.Injective ψ) {v w : Fin (N + 1) → A}
    (hv : Ideal.span (Set.range v) = ⊤) (hw : Ideal.span (Set.range w) = ⊤)
    (h : spMap ψ ≫ pt c v hv = spMap ψ ≫ pt c w hw) : pt c v hv = pt c w hw := by
  rw [spMap_pt, spMap_pt, pt_eq_pt_iff] at h
  obtain ⟨u, hu⟩ := h
  refine (pt_eq_pt_iff c hv hw).2 (exists_unit_smul_of_mul_eq hv hw fun i j => hψ ?_)
  have e : ∀ k, ψ (w k) = u.val * ψ (v k) := congrFun hu
  rw [map_mul, map_mul, e, e]
  ring

section Valuation

variable {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

variable (V) in

theorem exists_smul_eq_primitive {ι : Type} [Finite ι] {v : ι → K} (hv : v ≠ 0) :
    ∃ (u : Kˣ) (w : ι → V), (∃ i, w i = 1) ∧ algebraMap V K ∘ w = u • v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  have : Nonempty ι := ⟨k⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => ValuationRing.valuation V K (v j)
  have h0 : v i ≠ 0 := fun h => hk (by
    have := hi k
    rwa [h, map_zero, le_zero_iff, map_eq_zero] at this)
  have h1 : ∀ j, ∃ a : V, algebraMap V K a = (v i)⁻¹ * v j := fun j =>
    (ValuationRing.mem_integer_iff V K _).1 (by
      rw [Valuation.mem_integer_iff, map_mul, map_inv₀]
      exact inv_mul_le_one_of_le₀ (hi j) zero_le)
  choose w hw using h1
  refine ⟨(Units.mk0 _ h0)⁻¹, w, ⟨i, IsFractionRing.injective V K ?_⟩, funext fun j => hw j⟩
  rw [hw, inv_mul_cancel₀ h0, map_one]

theorem exists_primitive_eq (c : R →+* V) (φ : Sp K ⟶ PSpace R N)
    (hφ : φ ≫ PSpace.str R N = spMap ((algebraMap V K).comp c)) :
    ∃ (w : Fin (N + 1) → V) (hw : Ideal.span (Set.range w) = ⊤), (∃ i, w i = 1) ∧
      spMap (algebraMap V K) ≫ pt c w hw = φ := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_pt _ φ hφ
  obtain ⟨u, w, ⟨i, hi⟩, e⟩ := exists_smul_eq_primitive V (span_range_eq_top_iff_ne_zero.1 hv)
  refine ⟨w, span_range_eq_top_iff_of_isLocalRing.2 ⟨i, hi ▸ isUnit_one⟩, ⟨i, hi⟩, ?_⟩
  rw [spMap_pt]
  exact ((pt_eq_pt_iff _ _ _).2 ⟨u, e⟩).symm

theorem existsUnique_extend (c : R →+* V) (φ : Sp K ⟶ PSpace R N)
    (hφ : φ ≫ PSpace.str R N = spMap ((algebraMap V K).comp c)) :
    ∃! ψ : Sp V ⟶ PSpace R N, ψ ≫ PSpace.str R N = spMap c ∧ spMap (algebraMap V K) ≫ ψ = φ := by
  obtain ⟨w, hw, -, e⟩ := exists_primitive_eq c φ hφ
  refine ⟨pt c w hw, ⟨pt_str c w hw, e⟩, fun ψ hψ => ?_⟩
  obtain ⟨w', hw', rfl⟩ := exists_eq_pt c ψ hψ.1
  exact pt_eq_pt_of_injective c (IsFractionRing.injective V K) hw' hw (hψ.2.trans e.symm)

theorem existsUnique_extend_of_isProjOver {f : Y ⟶ Sp R} (hf : IsProjOver f) (c : R →+* V) (φ : Sp K ⟶ Y)
    (hφ : φ ≫ f = spMap ((algebraMap V K).comp c)) :
    ∃! ψ : Sp V ⟶ Y, ψ ≫ f = spMap c ∧ spMap (algebraMap V K) ≫ ψ = φ := by
  have hp : IsProper f := ReciprocityTheory.ChartRestriction.G.Geo.Tor.projProper R Y f hf
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f :=
    { R := V, K := K, i₁ := φ, i₂ := spMap c, commSq := ⟨by rw [hφ, ← Spec.map_comp]; rfl⟩ }
  obtain ⟨U⟩ := hv S
  refine ⟨U.default.l, ⟨U.default.fac_right, U.default.fac_left⟩, fun ψ hψ => ?_⟩
  exact congrArg CommSq.LiftStruct.l (U.uniq ⟨ψ, hψ.2, hψ.1⟩)

end Valuation

section ProjMap

variable {S T σ τ : Type} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] [CommRing T] [SetLike τ T]
  [AddSubgroupClass τ T] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (g : 𝒜 →+*ᵍ ℬ)

theorem exists_mem_of_surjective (hg : Function.Surjective g) {n : ℕ} {b : T} (hb : b ∈ ℬ n) :
    ∃ a ∈ 𝒜 n, g a = b := by
  obtain ⟨a, rfl⟩ := hg b
  refine ⟨DirectSum.decompose 𝒜 a n, (DirectSum.decompose 𝒜 a n).2, ?_⟩
  rw [GradedRingHom.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ hb]

theorem irrelevant_le_map_of_surjective (hg : Function.Surjective g) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g :=
  (HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun n hn b hb => by
    obtain ⟨a, ha, rfl⟩ := exists_mem_of_surjective g hg hb
    exact Ideal.mem_map_of_mem g.toRingHom (HomogeneousIdeal.mem_irrelevant_of_mem _ hn ha)

theorem awayMap_surjective (hg : Function.Surjective g) {d : ℕ} {s : S} (hs : s ∈ 𝒜 d) :
    Function.Surjective (HomogeneousLocalization.Away.map g s) := by
  intro x
  obtain ⟨n, b, hb, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (g.2 hs) x
  obtain ⟨a, ha, rfl⟩ := exists_mem_of_surjective g hg hb
  exact ⟨HomogeneousLocalization.Away.mk 𝒜 hs n a ha, HomogeneousLocalization.Away.map_mk ..⟩

theorem isClosedImmersion_projMap (hg : Function.Surjective g)
    (h : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    IsClosedImmersion (Proj.map g h) := by
  have key : ∀ (d : ℕ) (hd : 0 < d) (s : S) (hs : s ∈ 𝒜 d),
      IsClosedImmersion (pullback.snd (Proj.map g h) (Proj.awayι 𝒜 s hs hd)) := fun d hd s hs => by
    have H := IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map g h hd s hs)
      (by rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen])
    have := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map g s)) (awayMap_surjective g hg hs)
    rw [← H.flip.isoPullback_inv_snd]
    infer_instance
  exact IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (Proj.affineOpenCover 𝒜).openCover
    fun s => key _ s.1.2 _ s.2.2

end ProjMap

theorem exists_lift_of_cover {X : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (φ : Y ⟶ X) {κ : Type}
    (U : κ → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hc : ⨆ i, U i = ⊤)
    (H : ∀ i s, (ι.app (U i)).hom s = 0 → (φ.app (U i)).hom s = 0) : ∃ ψ : Y ⟶ Z, ψ ≫ ι = φ := by
  have loc : ∀ i, ∃ ψ : (φ ⁻¹ᵁ U i).toScheme ⟶ Z, ψ ≫ ι = (φ ⁻¹ᵁ U i).ι ≫ φ := fun i => by
    let ρ := (ι.app (U i)).hom.liftOfSurjective (ι.app_surjective _ (hU i)) ⟨(φ.app (U i)).hom, H i⟩
    have hρ : ι.app (U i) ≫ CommRingCat.ofHom ρ = φ.app (U i) :=
      CommRingCat.hom_ext (RingHom.liftOfSurjective_comp _ _ _)
    refine ⟨(φ ⁻¹ᵁ U i).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ρ) ≫ ((hU i).preimage ι).fromSpec, ?_⟩
    rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec ι (hU i) _ le_rfl,
      ← Scheme.Hom.app_eq_appLE, ← Spec.map_comp_assoc, hρ, Scheme.Hom.app_eq_appLE,
      Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
  choose ψ hψ using loc
  have hc' : ⨆ i, φ ⁻¹ᵁ U i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  refine ⟨(Y.openCoverOfIsOpenCover _ hc').glueMorphisms ψ fun i j => ?_, ?_⟩
  · exact (cancel_mono ι).1 ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hψ i)).trans
      ((pullback.condition_assoc _).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (hψ j))).symm)))
  · refine (Y.openCoverOfIsOpenCover _ hc').hom_ext _ _ fun i => ?_
    exact (Scheme.Cover.ι_glueMorphisms_assoc _ _ _ i _).trans (hψ i)

variable (I : HomogeneousIdeal (grading R N))

scoped instance gradedAlgebraQuot : GradedAlgebra (quotGrading (grading R N) I.toIdeal) :=
  quotGradedAlgebra _ I.isHomogeneous

abbrev VPlus : Scheme.{0} := Proj (quotGrading (grading R N) I.toIdeal)

def quotHom : grading R N →+*ᵍ quotGrading (grading R N) I.toIdeal where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem hf := mk_mem_quotGrading _ _ hf

theorem quotHom_eq_zero_iff {f : MvPolynomial (Fin (N + 1)) R} : quotHom I f = 0 ↔ f ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

def vPlusι : VPlus I ⟶ PSpace R N :=
  Proj.map (quotHom I) (irrelevant_le_map_of_surjective _ Ideal.Quotient.mk_surjective)

instance isClosedImmersion_vPlusι : IsClosedImmersion (vPlusι I) :=
  isClosedImmersion_projMap _ Ideal.Quotient.mk_surjective _

theorem isProjOver_vPlus : IsProjOver (vPlusι I ≫ PSpace.str R N) := ⟨N, vPlusι I, inferInstance, rfl⟩

theorem vPlusι_app_formOn_eq_zero_iff (i : Fin (N + 1)) {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f.IsHomogeneous n) :
    ((vPlusι I).app (chart R N i)).hom (formOn (chart R N i) i le_rfl n f hf) = 0 ↔ ∃ m, X i ^ m * f ∈ I := by
  have hf' : f ∈ grading R N (n • 1) := by simpa using hf
  have e : formOn (chart R N i) i le_rfl n f hf = (Proj.awayToSection (grading R N) (X i)).hom
      (HomogeneousLocalization.Away.mk _ (X_mem R N i) n f hf') := by
    rw [awayToSection_mk]
    exact frac_eq rfl
  have e' := congrArg (fun ψ => ψ.hom (HomogeneousLocalization.Away.mk _ (X_mem R N i) n f hf'))
    (Proj.awayToSection_comp_appLE (quotHom I)
      (irrelevant_le_map_of_surjective _ Ideal.Quotient.mk_surjective) (X_mem R N i))
  have inj := (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway _ (quotHom I (X i))
    ((quotHom I).2 (X_mem R N i)) one_pos).hom).1
  rw [e, Scheme.Hom.app_eq_appLE]
  refine (iff_of_eq (congrArg (· = 0) e')).trans ((map_eq_zero_iff _ inj).trans ?_)
  change HomogeneousLocalization.Away.map (quotHom I) (X i) _ = 0 ↔ _
  rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨_, m, rfl⟩, hm⟩
    exact ⟨m, (quotHom_eq_zero_iff I).1 (by simpa using hm)⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨_, m, rfl⟩, by simpa using (quotHom_eq_zero_iff I).2 hm⟩

theorem exists_comp_vPlusι_iff (φ : Y ⟶ PSpace R N) :
    (∃ ψ : Y ⟶ VPlus I, ψ ≫ vPlusι I = φ) ↔ ∀ (i : Fin (N + 1)) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
      (hf : f.IsHomogeneous n), f ∈ I → (φ.app (chart R N i)).hom (formOn (chart R N i) i le_rfl n f hf) = 0 := by
  constructor
  · rintro ⟨ψ, rfl⟩ i n f hf hI
    exact (congrArg (ψ.app _).hom ((vPlusι_app_formOn_eq_zero_iff I i hf).2 ⟨0, by simpa using hI⟩)).trans
      (map_zero _)
  · intro H
    refine exists_lift_of_cover _ φ _ (isAffineOpen_chart R N) (iSup_chart R N) fun i s hs => ?_
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Proj.basicOpenIsoAway (grading R N) (X i) (X_mem R N i) one_pos).hom).2 s
    obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) x
    have hf' : f.IsHomogeneous n := by simpa using hf
    have e : (Proj.awayToSection (grading R N) (X i)).hom
        (HomogeneousLocalization.Away.mk _ (X_mem R N i) n f hf) = formOn (chart R N i) i le_rfl n f hf' := by
      rw [awayToSection_mk]
      exact frac_eq rfl
    obtain ⟨m, hm⟩ := (vPlusι_app_formOn_eq_zero_iff I i hf').1 ((congrArg _ e).symm.trans hs)
    refine (congrArg _ (e.trans ?_)).trans (H i (m + n) _ ((isHomogeneous_X_pow i m).mul hf') hm)
    exact frac_eq (by ring)

theorem appLE_pt_formOn_mul (c : R →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)
    {W : (Sp A).Opens} (i : Fin (N + 1)) (h : W ≤ pt c v hv ⁻¹ᵁ chart R N i) {n : ℕ}
    {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    ((pt c v hv).appLE (chart R N i) W h).hom (formOn (chart R N i) i le_rfl n f hf) * fnOn W (v i) ^ n =
      fnOn W (eval₂ c v f) := by
  have e := congrArg (fun t => t f) (appLE_comp_aeval_ratio (φ := pt c v hv) (hi := h))
  have e' : (baseRingHom (pt c v hv ≫ PSpace.str R N) W).hom = (fnOn W).comp c := by
    rw [pt_str]
    exact congrArg CommRingCat.Hom.hom
      (baseRingHom_comp_SpecMap (𝟙 (Sp A)) (CommRingCat.ofHom c) W)
  rw [e'] at e
  rw [formOn_eq_aeval, eval₂_comp_left]
  refine (congrArg (· * _) e).trans ?_
  refine (ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous ((fnOn W).comp c)
    (pullRatio (pt c v hv) W i h) (fnOn W (v i)) hf).symm.trans ?_
  exact congrArg (fun w => eval₂ ((fnOn W).comp c) w f) (funext fun j => pullRatio_pt_mul c v hv i j h)

theorem exists_comp_vPlusι_eq_pt_iff (c : R →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) :
    (∃ ψ : Sp A ⟶ VPlus I, ψ ≫ vPlusι I = pt c v hv) ↔ ∀ f ∈ I, eval₂ c v f = 0 := by
  constructor
  · intro H f hf
    rw [exists_comp_vPlusι_iff] at H
    have key : ∀ n (g : MvPolynomial (Fin (N + 1)) R), g.IsHomogeneous n → g ∈ I → eval₂ c v g = 0 :=
      fun n g hg hI => eq_zero_of_fnOn_eq_zero hv fun i => by
        rw [← appLE_pt_formOn_mul c v hv i (pt_preimage_chart c v hv i).ge hg]
        exact mul_eq_zero_of_left ((congrArg (resG _ (pt_preimage_chart c v hv i).ge) (H i n g hg hI)).trans
          (map_zero _)) _
    rw [← sum_homogeneousComponent f, ← coe_eval₂Hom, map_sum]
    exact Finset.sum_eq_zero fun n _ => key n _ (homogeneousComponent_isHomogeneous n f)
      (decomposition.decompose'_apply f n ▸ I.isHomogeneous n hf)
  · intro H
    refine (exists_comp_vPlusι_iff I _).2 fun i n f hf hI => ?_
    have e := appLE_pt_formOn_mul c v hv i le_rfl hf
    have hu : IsUnit (fnOn (pt c v hv ⁻¹ᵁ chart R N i) (v i)) :=
      isUnit_of_basicOpen_eq _ (by rw [basicOpen_fnOn, pt_preimage_chart, inf_idem])
    rw [H f hI, map_zero, (hu.pow n).mul_left_eq_zero] at e
    rwa [Scheme.Hom.app_eq_appLE]

theorem mem_range_vPlusι_iff (x : PSpace R N) : x ∈ Set.range (vPlusι I) ↔ I ≤ x.asHomogeneousIdeal := by
  constructor
  · rintro ⟨y, rfl⟩ f hf
    change quotHom I f ∈ y.asHomogeneousIdeal
    rw [(quotHom_eq_zero_iff I).2 hf]
    exact zero_mem _
  · intro hx
    obtain ⟨ψ, hψ⟩ := (exists_comp_vPlusι_iff I ((PSpace R N).fromSpecResidueField x)).2 fun i n f hf hI => by
      refine (basicOpen_eq_bot_iff _).1 ?_
      rw [← Scheme.preimage_basicOpen, basicOpen_formOn, eq_bot_iff]
      intro z hz
      refine (hz.2 ?_).elim
      rw [show ((PSpace R N).fromSpecResidueField x) z = x from Scheme.fromSpecResidueField_apply x z]
      exact hx hI
    exact ⟨ψ (IsLocalRing.closedPoint _), (Scheme.Hom.comp_apply ψ _ _).symm.trans
      (hψ ▸ Scheme.fromSpecResidueField_apply x _)⟩

theorem range_vPlusι : Set.range (vPlusι I) = ProjectiveSpectrum.zeroLocus (grading R N) I :=
  Set.ext fun x => mem_range_vPlusι_iff I x

theorem exists_eq_pt_vPlus [Subsingleton (CommRing.Pic A)] (c : R →+* A) (ψ : Sp A ⟶ VPlus I)
    (hψ : ψ ≫ vPlusι I ≫ PSpace.str R N = spMap c) :
    ∃ (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      (∀ f ∈ I, eval₂ c v f = 0) ∧ ψ ≫ vPlusι I = pt c v hv := by
  obtain ⟨v, hv, e⟩ := exists_eq_pt c (ψ ≫ vPlusι I) (by rw [Category.assoc, hψ])
  exact ⟨v, hv, (exists_comp_vPlusι_eq_pt_iff I c v hv).1 ⟨ψ, e⟩, e⟩

theorem isProjOver_comp_of_isClosedImmersion (g : Z ⟶ Y) [IsClosedImmersion g] {f : Y ⟶ Sp R}
    (h : IsProjOver f) : IsProjOver (g ≫ f) := by
  obtain ⟨N, φ, _, rfl⟩ := h
  exact ⟨N, g ≫ φ, inferInstance, Category.assoc _ _ _⟩

theorem isProjOver_of_isPullback_spMap {R' : Type} [CommRing R'] (c : R →+* R') {g : Z ⟶ Y} {f' : Z ⟶ Sp R'}
    {f : Y ⟶ Sp R} (H : IsPullback g f' f (spMap c)) (h : IsProjOver f) : IsProjOver f' := by
  obtain ⟨N, φ, hφ, rfl⟩ := h
  have P := isPullback_baseChange N c
  let ψ := P.lift (g ≫ φ) f' (by rw [Category.assoc, H.w])
  have hψ : ψ ≫ PSpace.str R' N = f' := P.lift_snd _ _ _
  have Q : IsPullback g ψ φ (baseChange N c) := IsPullback.of_bot (hψ.symm ▸ H) (P.lift_fst _ _ _).symm P
  exact ⟨N, ψ, MorphismProperty.of_isPullback Q hφ, hψ⟩

theorem isProjOver_pullback_snd {R' : Type} [CommRing R'] (c : R →+* R') {f : Y ⟶ Sp R} (h : IsProjOver f) :
    IsProjOver (pullback.snd f (spMap c)) :=
  isProjOver_of_isPullback_spMap c (IsPullback.of_hasPullback _ _) h

theorem isProjOver_pullback {f : Y ⟶ Sp R} {g : Z ⟶ Sp R} (hf : IsProjOver f) (hg : IsProjOver g) :
    IsProjOver (pullback.fst f g ≫ f) :=
  isProjOver_of_isPullback (IsPullback.of_hasPullback f g) hf hg

section Linear

variable (R) {M : ℕ} {e : Fin (N + 1) → Fin (M + 1)} (he : Function.Injective e)

def killHom : grading R M →+*ᵍ grading R N where
  __ := (killCompl (R := R) he).toRingHom
  map_mem {n f} hf := by
    have := IsHomogeneous.aeval (n := 1) hf (fun k => killCompl (R := R) he (X k)) fun k => by
      rw [killCompl, aeval_X]
      split_ifs
      exacts [isHomogeneous_X _ _, isHomogeneous_zero _ _ _]
    rw [one_mul] at this
    exact (congrArg (fun φ => IsHomogeneous (φ f) n) (aeval_unique (killCompl (R := R) he))).mpr this

theorem killHom_surjective : Function.Surjective (killHom R he) :=
  fun p => ⟨rename e p, killCompl_rename_app he p⟩

def linearι : PSpace R N ⟶ PSpace R M :=
  Proj.map (killHom R he) (irrelevant_le_map_of_surjective _ (killHom_surjective R he))

instance isClosedImmersion_linearι : IsClosedImmersion (linearι R he) :=
  isClosedImmersion_projMap _ (killHom_surjective R he) _

theorem linearι_preimage_chart (i : Fin (N + 1)) : linearι R he ⁻¹ᵁ chart R M (e i) = chart R N i :=
  congrArg (Proj.basicOpen (grading R N)) ((congrArg (killCompl he) (rename_X e i).symm).trans
    (killCompl_rename_app he _))

theorem linearι_preimage_chart_of_notMem {k : Fin (M + 1)} (hk : k ∉ Set.range e) :
    linearι R he ⁻¹ᵁ chart R M k = ⊥ := by
  have : killHom R he (X k) = 0 := (aeval_X _ k).trans (dif_neg hk)
  exact (congrArg (Proj.basicOpen (grading R N)) this).trans (Proj.basicOpen_zero _)

@[reassoc] theorem linearι_str : linearι R he ≫ PSpace.str R M = PSpace.str R N := by
  refine (Proj.mapAffineOpenCover (killHom R he)
    (irrelevant_le_map_of_surjective _ (killHom_surjective R he))).openCover.hom_ext _ _ fun s => ?_
  have key : ∀ (d : ℕ) (hd : 0 < d) (s : MvPolynomial (Fin (M + 1)) R) (hs : s ∈ grading R M d),
      Proj.awayι (grading R N) (killHom R he s) ((killHom R he).2 hs) hd ≫ linearι R he ≫ PSpace.str R M =
        Proj.awayι (grading R N) (killHom R he s) ((killHom R he).2 hs) hd ≫ PSpace.str R N := by
    intro d hd s hs
    rw [linearι, Proj.awayι_comp_map_assoc _ _ hd s hs, PSpace.str, PSpace.str, Proj.awayι_toSpecZero_assoc,
      Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    refine RingHom.ext fun r => HomogeneousLocalization.val_injective _ ?_
    refine (congrArg HomogeneousLocalization.val (HomogeneousLocalization.Away.map_mk (killHom R he) s hs 0 (C r)
      ((zero_smul ℕ d).symm ▸ isHomogeneous_C _ r))).trans ?_
    rw [HomogeneousLocalization.Away.val_mk]
    exact congrArg (Localization.mk · _) (killCompl_C he r)
  exact key _ s.1.2 _ s.2.2

end Linear

theorem isProjOver_sigmaDesc {ι : Type} [Finite ι] {T : ι → Scheme.{0}} (f : ∀ i, T i ⟶ Sp R)
    (h : ∀ i, IsProjOver (f i)) : IsProjOver (Sigma.desc f) := by
  choose n φ hφ e using h
  obtain ⟨M, ⟨a⟩⟩ := Finite.exists_equiv_fin (Σ i, Fin (n i + 1))
  let b : ∀ i, Fin (n i + 1) → Fin (M + 1) := fun i k => (a ⟨i, k⟩).castSucc
  have hb : ∀ i, Function.Injective (b i) := fun i k l hkl =>
    sigma_mk_injective (β := fun i => Fin (n i + 1)) (a.injective (Fin.castSucc_injective _ hkl))
  refine ⟨M, Sigma.desc fun i => φ i ≫ linearι R (hb i),
    isClosedImmersion_sigmaDesc _ (fun i => inferInstance) fun i j hij => ?_, ?_⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    obtain ⟨k, hk⟩ := exists_mem_chart R (n i) (φ i x)
    have h1 : (φ i ≫ linearι R (hb i)) x ∈ chart R M (b i k) := (linearι_preimage_chart R (hb i) k).ge hk
    rw [← hy] at h1
    refine (linearι_preimage_chart_of_notMem R (hb j) (k := b i k) ?_).le (x := φ j y) h1
    rintro ⟨l, hl⟩
    exact hij (congrArg Sigma.fst (a.injective (Fin.castSucc_injective _ hl))).symm
  · refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc, linearι_str, e]

theorem isProjOver_coprodDesc {f : Y ⟶ Sp R} {g : Z ⟶ Sp R} (hf : IsProjOver f) (hg : IsProjOver g) :
    IsProjOver (coprod.desc f g) := by
  refine isProjOver_of_isIso_comp (coprodIsoSigma Y Z).inv ?_
  convert isProjOver_sigmaDesc (T := fun i : ULift.{0} WalkingPair => i.1.casesOn Y Z)
    (fun i => Sigma.ι (fun i : ULift.{0} WalkingPair => (i.1.casesOn Y Z : Scheme.{0})) i ≫
      (coprodIsoSigma Y Z).inv ≫ coprod.desc f g) ?_ using 1
  · exact Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc]
  · rintro ⟨_ | _⟩
    · rwa [← Category.assoc, ι_left_coprodIsoSigma_inv, coprod.inl_desc]
    · rwa [← Category.assoc, ι_right_coprodIsoSigma_inv, coprod.inr_desc]

theorem isProjOver_of_disjoint_cover {ι : Type} [Finite ι] (f : Y ⟶ Sp R) (U : ι → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (hd : Pairwise fun i j => Disjoint (U i) (U j)) (h : ∀ i, IsProjOver ((U i).ι ≫ f)) : IsProjOver f := by
  have h1 : IsOpenImmersion (Sigma.desc fun i => (U i).ι) :=
    isOpenImmersion_sigmaDesc _ _ fun i j hij => by
      simpa [Function.onFun, ← Opens.coe_disjoint] using hd hij
  have : IsIso (Sigma.desc fun i => (U i).ι) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (top_le_iff.1 fun y _ => by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU.ge (Set.mem_univ y))
      exact ⟨Sigma.ι (fun i => (U i).toScheme) i ⟨y, hi⟩, (Scheme.Hom.comp_apply _ _ _).symm.trans
        (by rw [Sigma.ι_desc]; rfl)⟩)
  refine isProjOver_of_isIso_comp (Sigma.desc fun i => (U i).ι) ?_
  convert isProjOver_sigmaDesc _ h using 1
  exact Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_desc_assoc, Sigma.ι_desc]

theorem pt_linearι {M : ℕ} {e : Fin (N + 1) → Fin (M + 1)} (he : Function.Injective e) (c : R →+* A)
    (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)
    (hw : Ideal.span (Set.range (Function.extend e v 0)) = ⊤) :
    pt c v hv ≫ linearι R he = pt c (Function.extend e v 0) hw := by
  refine (ProjPoint.ofHom_map _ _ _ _).trans ?_
  unfold pt
  congr 1
  refine ringHom_ext (fun r => ?_) (fun k => ?_)
  · exact (congrArg (eval₂Hom c v) (killCompl_C he r)).trans ((eval₂Hom_C _ _ r).trans (eval₂Hom_C _ _ r).symm)
  · rw [eval₂Hom_X']
    by_cases hk : k ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hk
      rw [he.extend_apply]
      exact (congrArg (eval₂Hom c v) ((congrArg (killCompl he) (rename_X e i).symm).trans
        (killCompl_rename_app he _))).trans (eval₂Hom_X' _ _ i)
    · rw [Function.extend_apply' _ _ _ hk]
      exact (congrArg (eval₂Hom c v) ((aeval_X _ k).trans (dif_neg hk))).trans (map_zero _)

variable (R N) in

theorem points_and_stability :
    (∀ (A : Type) [CommRing A] [Algebra R A],
      (∀ (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
        pt (algebraMap R A) v hv ≫ PSpace.str R N = spMap (algebraMap R A) ∧
        (∀ i, pt (algebraMap R A) v hv ⁻¹ᵁ chart R N i = PrimeSpectrum.basicOpen (v i)) ∧
        (∀ (B : Type) [CommRing B] [Algebra R B] (ψ : A →ₐ[R] B), ∃ h : Ideal.span (Set.range (ψ ∘ v)) = ⊤,
          spMap (ψ : A →+* B) ≫ pt (algebraMap R A) v hv = pt (algebraMap R B) (ψ ∘ v) h) ∧
        ∀ (w : Fin (N + 1) → A) (hw : Ideal.span (Set.range w) = ⊤),
          pt (algebraMap R A) v hv = pt (algebraMap R A) w hw ↔ ∃ u : Aˣ, w = u • v) ∧
      ((IsLocalRing A ∨ Subsingleton (CommRing.Pic A)) → ∀ φ : Sp A ⟶ PSpace R N,
        φ ≫ PSpace.str R N = spMap (algebraMap R A) →
          ∃ (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤), φ = pt (algebraMap R A) v hv)) ∧
    (∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
      (c : R →+* V) (φ : Sp K ⟶ PSpace R N), φ ≫ PSpace.str R N = spMap ((algebraMap V K).comp c) →
        (∃ (w : Fin (N + 1) → V) (hw : Ideal.span (Set.range w) = ⊤), (∃ i, w i = 1) ∧
          spMap (algebraMap V K) ≫ pt c w hw = φ) ∧
        ∃! ψ : Sp V ⟶ PSpace R N, ψ ≫ PSpace.str R N = spMap c ∧ spMap (algebraMap V K) ≫ ψ = φ) ∧
    (∀ (R' : Type) [CommRing R'] (c : R →+* R') (Y : Scheme.{0}) (f : Y ⟶ Sp R),
      IsProjOver f → IsProjOver (pullback.snd f (spMap c))) ∧
    (∀ (Y Z : Scheme.{0}) (g : Z ⟶ Y) (f : Y ⟶ Sp R), IsClosedImmersion g → IsProjOver f → IsProjOver (g ≫ f)) ∧
    (∀ (ι : Type) [Finite ι] (T : ι → Scheme.{0}) (f : ∀ i, T i ⟶ Sp R),
      (∀ i, IsProjOver (f i)) → IsProjOver (Sigma.desc f)) ∧
    (∀ (Y Z : Scheme.{0}) (f : Y ⟶ Sp R) (g : Z ⟶ Sp R),
      IsProjOver f → IsProjOver g → IsProjOver (pullback.fst f g ≫ f)) ∧
    ∀ I : HomogeneousIdeal (grading R N), IsClosedImmersion (vPlusι I) ∧
      Set.range (vPlusι I) = ProjectiveSpectrum.zeroLocus (grading R N) I ∧
      ∀ (A : Type) [CommRing A] (c : R →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
        (∃ ψ : Sp A ⟶ VPlus I, ψ ≫ vPlusι I = pt c v hv) ↔ ∀ f ∈ I, eval₂ c v f = 0 := by
  refine ⟨fun A _ _ => ⟨fun v hv => ⟨pt_str _ v hv, pt_preimage_chart _ v hv, fun B _ _ ψ =>
      ⟨span_range_comp_eq_top v hv (ψ : A →+* B), ?_⟩, fun w hw => pt_eq_pt_iff _ hv hw⟩, fun h φ hφ => ?_⟩,
    fun V K _ _ _ _ _ _ c φ hφ => ⟨exists_primitive_eq c φ hφ, existsUnique_extend c φ hφ⟩,
    fun _ _ c _ _ h => isProjOver_pullback_snd c h,
    fun _ _ g _ _ h => isProjOver_comp_of_isClosedImmersion g h,
    fun _ _ _ f h => isProjOver_sigmaDesc f h, fun _ _ _ _ => isProjOver_pullback,
    fun I => ⟨inferInstance, range_vPlusι I, fun _ _ => exists_comp_vPlusι_eq_pt_iff I⟩⟩
  · rw [spMap_pt]
    congr 1
    exact ψ.comp_algebraMap
  · have : Subsingleton (CommRing.Pic A) := h.elim (fun _ => inferInstance) id
    exact exists_eq_pt _ φ hφ

example (h : Ideal.span (Set.range ![(2 : ℤ), 3]) = ⊤) (h' : Ideal.span (Set.range ![(-2 : ℤ), -3]) = ⊤) :
    pt (RingHom.id ℤ) ![2, 3] h = pt (RingHom.id ℤ) ![-2, -3] h' :=
  (pt_eq_pt_iff _ h h').2 ⟨-1, by decide⟩

end GlobalTheory.ProjSpace
