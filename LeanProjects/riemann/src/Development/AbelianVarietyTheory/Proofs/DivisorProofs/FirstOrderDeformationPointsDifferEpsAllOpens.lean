import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS.EpsDiff

open GlobalTheory.FlagMod (ev_spMap spMap_ev tau tau_le le_preimage_comp le_preimage_map)

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {B : Type} [CommRing B]

abbrev mkE (ε : B) : B →+* B ⧸ Ideal.span {ε} := Ideal.Quotient.mk _

def FR (ε : B) : Subring (B × DualNumber (B ⧸ Ideal.span {ε})) :=
  RingHom.eqLocus ((mkE ε).comp (RingHom.fst _ _))
    ((TrivSqZeroExt.fstHom (B ⧸ Ideal.span {ε}) _ _).toRingHom.comp (RingHom.snd _ _))

theorem mem_FR {ε : B} {r : B × DualNumber (B ⧸ Ideal.span {ε})} : r ∈ FR ε ↔ mkE ε r.1 = r.2.fst := Iff.rfl

def p1 (ε : B) : FR ε →+* B := (RingHom.fst _ _).comp (FR ε).subtype

def p2 (ε : B) : FR ε →+* DualNumber (B ⧸ Ideal.span {ε}) := (RingHom.snd _ _).comp (FR ε).subtype

theorem FR_ext {ε : B} {r s : FR ε} (h1 : p1 ε r = p1 ε s) (h2 : p2 ε r = p2 ε s) : r = s :=
  Subtype.ext (Prod.ext h1 h2)

theorem epsFibreProduct_quotient_fst_eq_dual_fst {ε : B} (r : FR ε) : mkE ε (p1 ε r) = (p2 ε r).fst := r.2

def liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : C →+* FR ε := (a.prod b).codRestrict (FR ε) h

theorem fst_comp_liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : (p1 ε).comp (liftFR a b h) = a := rfl

theorem snd_comp_liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : (p2 ε).comp (liftFR a b h) = b := rfl

theorem exists_liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : ∃ q : C →+* FR ε, (p1 ε).comp q = a ∧ (p2 ε).comp q = b :=
  ⟨liftFR a b h, rfl, rfl⟩

def mulE {ε : B} (hε : ε * ε = 0) : (B ⧸ Ideal.span {ε}) →ₗ[B] B :=
  Submodule.liftQ _ (LinearMap.mul B B ε) (by
    intro c hc
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    simp only [LinearMap.mem_ker, LinearMap.mul_apply']
    rw [← _root_.mul_assoc, _root_.mul_comm ε d, _root_.mul_assoc, hε, MulZeroClass.mul_zero])

theorem mulE_mk {ε : B} (hε : ε * ε = 0) (c : B) : mulE hε (mkE ε c) = ε * c := rfl

def sg {ε : B} (hε : ε * ε = 0) : FR ε →+* B where
  toFun r := p1 ε r + mulE hε (p2 ε r).snd
  map_one' := by simp
  map_zero' := by simp
  map_add' r s := by
    simp only [map_add, TrivSqZeroExt.snd_add]
    ring
  map_mul' r s := by
    obtain ⟨c, hc⟩ : ∃ c, mkE ε c = (p2 ε r).snd := Ideal.Quotient.mk_surjective _
    obtain ⟨d, hd⟩ : ∃ d, mkE ε d = (p2 ε s).snd := Ideal.Quotient.mk_surjective _
    have e : (p2 ε (r * s)).snd = mkE ε (p1 ε r * d + c * p1 ε s) := by
      rw [map_mul, DualNumber.snd_mul, map_add, map_mul, map_mul, hc, hd, epsFibreProduct_quotient_fst_eq_dual_fst, epsFibreProduct_quotient_fst_eq_dual_fst]
    rw [e, ← hc, ← hd, map_mul, mulE_mk, mulE_mk, mulE_mk]
    linear_combination (-(c * d)) * hε

theorem sg_apply {ε : B} (hε : ε * ε = 0) (r : FR ε) : sg hε r = p1 ε r + mulE hε (p2 ε r).snd := rfl

theorem epsFibreProductSnd_surjective (ε : B) : Function.Surjective (p2 ε) := by
  intro w
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective w.fst
  exact ⟨⟨(b, w), hb⟩, rfl⟩

theorem specMap_epsFibreProductSnd_surjective {ε : B} (hε : ε * ε = 0) : Function.Surjective (spMap (p2 ε)) := by
  intro q
  have hk : RingHom.ker (p2 ε) ≤ q.asIdeal := by
    intro r hr
    have hr' : p2 ε r = 0 := hr
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have h1 : mkE ε (p1 ε r) = 0 := by rw [epsFibreProduct_quotient_fst_eq_dual_fst, hr']; rfl
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have : r ^ 2 = 0 := by
      apply FR_ext
      · rw [map_pow, ← hd, map_zero]
        linear_combination (d * d) * hε
      · rw [map_pow, hr', map_zero]; simp
    rw [this]; exact zero_mem _
  have := _root_.range_comap_of_surjective _ (p2 ε) (epsFibreProductSnd_surjective ε)
  have hq : q ∈ Set.range (PrimeSpectrum.comap (p2 ε)) := by
    rw [this]; exact hk
  exact hq

theorem top_le_preimage_of_epsFibreSnd_comp {ε : B} (hε : ε * ε = 0) {Y : Scheme.{0}} {T : Sp (FR ε) ⟶ Y} {O : Y.Opens}
    (h : ⊤ ≤ (spMap (p2 ε) ≫ T) ⁻¹ᵁ O) : ⊤ ≤ T ⁻¹ᵁ O := by
  intro p _
  obtain ⟨q, rfl⟩ := specMap_epsFibreProductSnd_surjective hε p
  exact h (Set.mem_univ q)

theorem pt_ext {ε : B} {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {a b : Sp (FR ε) ⟶ Y}
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h1 : spMap (p1 ε) ≫ a = spMap (p1 ε) ≫ b)
    (h2 : spMap (p2 ε) ≫ a = spMap (p2 ε) ≫ b) : a = b := by
  have e1 := GlobalTheory.FlagMod.ev_congr h1 U (le_preimage_comp _ ha) (le_preimage_comp _ hb)
  have e2 := GlobalTheory.FlagMod.ev_congr h2 U (le_preimage_comp _ ha) (le_preimage_comp _ hb)
  rw [ev_spMap _ _ _ ha, ev_spMap _ _ _ hb] at e1 e2
  have e : ev a U ha = ev b U hb := RingHom.ext fun f =>
    FR_ext (RingHom.congr_fun e1 f) (RingHom.congr_fun e2 f)
  rw [← spMap_ev a hU ha, ← spMap_ev b hU hb, e]

end GlobalTheory.CechKS.EpsDiff

namespace GlobalTheory.CechKS

open EpsDiff
open GlobalTheory.FlagMod (ev_spMap spMap_ev tau tau_le le_preimage_comp le_preimage_map)

theorem valR_sub_eq_eps_mul_of_affine : ∀ {K : Type} [Field K] {A : Over (Sp K)} {A' : Over (Sp (DualNumber K))} {i : A.left ⟶ A'.left} (hi : i ≫ A'.hom = A.hom ≫ GlobalTheory.DeRham.epsRed K) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) (U : X.affineOpens) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (Ω : Z.affineOpens) (hΩ : Ω.1 ≤ h ⁻¹ᵁ U.1) {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (S : Sp (DualNumber B) ⟶ A.left) (hS : S ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp (baseMap K B))) (hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x) (l₁ l₂ : Sp B ⟶ A'.left) (hl₁ : l₁ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hl₂ : l₂ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hΩ₁ : ⊤ ≤ (l₁ ≫ m') ⁻¹ᵁ Ω.1) (hΩ₂ : ⊤ ≤ (l₂ ≫ m') ⁻¹ᵁ Ω.1) (h₂ : ∀ f, ∃ c : B, valR (l₂ ≫ m') Ω.1 f = valR (x ≫ m) Ω.1 f + algebraMap (DualNumber K) B DualNumber.eps * c) (h₁₂ : ∀ f, valR (l₁ ≫ m') Ω.1 f - valR (l₂ ≫ m') Ω.1 f = algebraMap (DualNumber K) B DualNumber.eps * (valR (S ≫ m) Ω.1 f).snd) (O : A'.left.Opens) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (f : Γ(A'.left, O)), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * (valR S (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  intro K _ A A' i hi X Z h y1 m m' hm' him U hU' Ω hΩ B _ _ x hxΩ S hS hSx l₁ l₂ hl₁ hl₂ hΩ₁ hΩ₂ h₂ h₁₂ O hxO f
  set ε : B := algebraMap (DualNumber K) B DualNumber.eps with hεd
  have hε : ε * ε = 0 := by rw [hεd, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hmkε : mkE ε ε = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε)
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := hxΩ
  have hSxm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S ≫ m = x ≫ m := by rw [← Category.assoc, hSx]
  have hSm : ⊤ ≤ (S ≫ m) ⁻¹ᵁ Ω.1 := le_preimage_of_red hSxm hxm
  have hSO : ⊤ ≤ S ⁻¹ᵁ (i ⁻¹ᵁ O) := le_preimage_of_red hSx hxO
  have hfst : ∀ g, (ev (S ≫ m) Ω.1 hSm g).fst = ev (x ≫ m) Ω.1 hxm g := fun g => by
    rw [GlobalTheory.FlagMod.ev_congr hSxm.symm Ω.1 hxm (le_preimage_comp _ hSm), ev_spMap _ _ _ hSm]
    rfl
  obtain ⟨q, hqa, hqb⟩ := exists_liftFR (ev (l₂ ≫ m') Ω.1 hΩ₂) ((dualMap (mkE ε)).comp (ev (S ≫ m) Ω.1 hSm))
    (fun g => by
      obtain ⟨c, hc⟩ := h₂ g
      rw [valR_eq_ev _ _ hΩ₂, valR_eq_ev _ _ hxm] at hc
      rw [hc, map_add, map_mul, hmkε, MulZeroClass.zero_mul, add_zero, ← hfst]
      simp [dualMap])
  let j2 : DualNumber K →+* DualNumber (B ⧸ Ideal.span {ε}) :=
    ((dualMap (mkE ε)).comp ((algebraMap B (DualNumber B)).comp (baseMap K B))).comp
      (TrivSqZeroExt.fstHom K K K).toRingHom
  have hj2 : ∀ a, j2 a = TrivSqZeroExt.inl (mkE ε (baseMap K B a.fst)) := fun a => by
    ext <;> simp [j2, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨j, hja, hjb⟩ := exists_liftFR (algebraMap (DualNumber K) B) j2 (fun a => by
    have ha : a = algebraMap K (DualNumber K) a.fst + DualNumber.eps * algebraMap K (DualNumber K) a.snd := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [hj2, TrivSqZeroExt.fst_inl]
    conv_lhs => rw [ha]
    rw [map_add, map_mul, ← hεd, map_add, map_mul, hmkε, MulZeroClass.zero_mul, add_zero]
    rfl)
  have b1 : spMap (p1 ε) ≫ spMap j = l₂ ≫ A'.hom := by rw [spc, hl₂, hja]
  have b2 : spMap (p2 ε) ≫ spMap j = (spMap (dualMap (mkE ε)) ≫ S ≫ i) ≫ A'.hom := by
    rw [Category.assoc, Category.assoc, hi, ← Category.assoc S, hS, ← Category.assoc, spc, spc]
    rw [hjb]
    exact (spc (TrivSqZeroExt.fstHom K K K).toRingHom
      ((dualMap (mkE ε)).comp ((algebraMap B (DualNumber B)).comp (baseMap K B)))).symm
  have b3 : spMap (sg hε) ≫ spMap j = l₁ ≫ A'.hom := by
    rw [spc, hl₁]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    have e1 : p1 ε (j a) = algebraMap (DualNumber K) B a := RingHom.congr_fun hja a
    have e2 : p2 ε (j a) = j2 a := RingHom.congr_fun hjb a
    rw [RingHom.comp_apply, sg_apply, e1, e2, hj2, TrivSqZeroExt.snd_inl, map_zero, add_zero]
  have z1 : spMap (p1 ε) ≫ spMap q ≫ tau Ω.2 = l₂ ≫ m' := by
    rw [← Category.assoc, spc, hqa]
    exact spMap_ev _ Ω.2 hΩ₂
  have z2 : spMap (p2 ε) ≫ spMap q ≫ tau Ω.2 = (spMap (dualMap (mkE ε)) ≫ S ≫ i) ≫ m' := by
    rw [Category.assoc, Category.assoc, him, ← Category.assoc, spc, hqb, ← spc, Category.assoc]
    exact congrArg _ (spMap_ev (S ≫ m) Ω.2 hSm)
  have z3 : spMap (sg hε) ≫ spMap q ≫ tau Ω.2 = l₁ ≫ m' := by
    rw [← Category.assoc, spc]
    have : (sg hε).comp q = ev (l₁ ≫ m') Ω.1 hΩ₁ := by
      refine RingHom.ext fun g => ?_
      have e := h₁₂ g
      rw [valR_eq_ev _ _ hΩ₂, valR_eq_ev _ _ hΩ₁, valR_eq_ev _ _ hSm] at e
      have e' : (dualMap (mkE ε) (ev (S ≫ m) Ω.1 hSm g)).snd = mkE ε (ev (S ≫ m) Ω.1 hSm g).snd := by
        simp [dualMap]
      have e1 : p1 ε (q g) = ev (l₂ ≫ m') Ω.1 hΩ₂ g := RingHom.congr_fun hqa g
      have e2 : p2 ε (q g) = dualMap (mkE ε) (ev (S ≫ m) Ω.1 hSm g) := RingHom.congr_fun hqb g
      rw [RingHom.comp_apply, sg_apply, e1, e2, e', mulE_mk, ← e]
      ring
    rw [this]
    exact spMap_ev _ Ω.2 hΩ₁
  have hw : (spMap q ≫ tau Ω.2) ≫ h = spMap j ≫ y1 := by
    refine pt_ext U.2 (le_preimage_map h hΩ (le_preimage_comp _ (tau_le Ω.2 le_rfl))) (le_preimage_comp _ hU') ?_ ?_
    · rw [← Category.assoc, z1, ← Category.assoc, b1, Category.assoc, Category.assoc, hm'.w]
    · rw [← Category.assoc, z2, ← Category.assoc (spMap (p2 ε)), b2, Category.assoc _ m', Category.assoc _ A'.hom,
        hm'.w]
  obtain ⟨T, T1, T2⟩ : ∃ T : Sp (FR ε) ⟶ A'.left, T ≫ m' = spMap q ≫ tau Ω.2 ∧ T ≫ A'.hom = spMap j :=
    ⟨hm'.lift _ _ hw, hm'.lift_fst _ _ hw, hm'.lift_snd _ _ hw⟩
  have t1 : spMap (p1 ε) ≫ T = l₂ :=
    hm'.hom_ext (by rw [Category.assoc, T1, z1]) (by rw [Category.assoc, T2, b1])
  have t2 : spMap (p2 ε) ≫ T = spMap (dualMap (mkE ε)) ≫ S ≫ i :=
    hm'.hom_ext (by rw [Category.assoc, T1, z2]) (by rw [Category.assoc, T2, b2])
  have t3 : spMap (sg hε) ≫ T = l₁ :=
    hm'.hom_ext (by rw [Category.assoc, T1, z3]) (by rw [Category.assoc, T2, b3])
  have hSi : ⊤ ≤ (S ≫ i) ⁻¹ᵁ O := hSO
  have hT : ⊤ ≤ T ⁻¹ᵁ O := top_le_preimage_of_epsFibreSnd_comp hε (by rw [t2]; exact le_preimage_comp _ hSi)
  have v2 := GlobalTheory.FlagMod.ev_congr t2 O (le_preimage_comp _ hT) (le_preimage_comp _ hSi)
  rw [ev_spMap _ _ _ hT, ev_spMap _ _ _ hSi] at v2
  have v2' : p2 ε (ev T O hT f) = dualMap (mkE ε) (ev (S ≫ i) O hSi f) := RingHom.congr_fun v2 f
  have e' : (dualMap (mkE ε) (ev (S ≫ i) O hSi f)).snd = mkE ε (ev (S ≫ i) O hSi f).snd := by
    simp [dualMap]
  rw [← valR_comp_app, valR_eq_ev _ _ hSi, ← t1, ← t3, valR_eq_ev _ _ (le_preimage_comp _ hT),
    valR_eq_ev _ _ (le_preimage_comp _ hT), ev_spMap _ _ _ hT, ev_spMap _ _ _ hT, RingHom.comp_apply,
    RingHom.comp_apply, sg_apply, v2', e', mulE_mk]
  ring

end GlobalTheory.CechKS

end
