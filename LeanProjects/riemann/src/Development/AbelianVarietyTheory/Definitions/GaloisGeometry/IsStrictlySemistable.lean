import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSSFun
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableModel

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.LogCris

variable {O : Type} [CommRing O]

def ptFun (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k] (κ : O →+* k) :
    CommRingCat.{0} ⥤ Type where
  obj B := PtOver X q κ B
  map {B B'} φ := TypeCat.ofHom fun z => ⟨(φ.hom.comp z.1.1, Spec.map φ ≫ z.1.2), by
    rw [Category.assoc, z.2, ← Spec.map_comp]; rfl⟩
  map_id B := by
    ext z
    · rfl
    · change Spec.map (𝟙 B) ≫ z.1.2 = z.1.2
      rw [Spec.map_id, Category.id_comp]
  map_comp f g := by
    ext z
    · rfl
    · simp

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.evalAt_res {B : Type} [CommRing B] {X : Scheme.{0}}
    (y : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (hV : V ≤ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ V) (a : Γ(X, U)) :
    _root_.GlobalTheory.Cris.evalAt y V h' (X.presheaf.map (homOfLE hV).op a) = _root_.GlobalTheory.Cris.evalAt y U h a := by
  simp only [_root_.GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in
private theorem gammaSpecIso_hom_appLE_spec_map {A C : CommRingCat.{0}} (χ : A ⟶ C)
    (e : (⊤ : (Spec C).Opens) ≤ Spec.map χ ⁻¹ᵁ ⊤) (b : Γ(Spec A, ⊤)) :
    (Scheme.ΓSpecIso C).hom ((Spec.map χ).appLE ⊤ ⊤ e b) = χ ((Scheme.ΓSpecIso A).hom b) := by
  have h1 : (Spec.map χ).appLE ⊤ ⊤ e = (Spec.map χ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h1, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.evalAt_map {B B' : CommRingCat.{0}} {X : Scheme.{0}} (φ : B ⟶ B')
    (y : Spec B ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U) (a : Γ(X, U)) :
    _root_.GlobalTheory.Cris.evalAt (B := B') (Spec.map φ ≫ y) U h' a =
      φ.hom (_root_.GlobalTheory.Cris.evalAt (B := B) y U h a) := by
  simp only [_root_.GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) y U ⊤ ⊤ h le_top, CommRingCat.comp_apply]
  exact gammaSpecIso_hom_appLE_spec_map φ _ _

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.evalAt_base {B : Type} [CommRing B] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k]
    (κ : O →+* k) (ψ : k →+* B) (y : Spec (CommRingCat.of B) ⟶ X)
    (hy : y ≫ q = Spec.map (CommRingCat.ofHom (ψ.comp κ))) {U : X.Opens} (h : ⊤ ≤ y ⁻¹ᵁ U) (a : O) :
    _root_.GlobalTheory.Cris.evalAt y U h ((q.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) =
      ψ (κ a) := by
  simp only [_root_.GlobalTheory.Cris.evalAt, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (q.appLE ⊤ U le_top) (y.appLE U ⊤ h),
    Scheme.Hom.appLE_comp_appLE y q ⊤ U ⊤ le_top h]
  have key : ∀ (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of O)),
      f = Spec.map (CommRingCat.ofHom (ψ.comp κ)) → ∀ e,
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom (f.appLE ⊤ ⊤ e ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) =
        ψ (κ a) := by
    rintro f rfl e
    rw [gammaSpecIso_hom_appLE_spec_map]
    simp
  exact key _ hy _

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.LogCris.le_preimage_inf {B : Type} [CommRing B] {X : Scheme.{0}}
    (y : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ V) : ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) :=
  le_inf h h'

theorem le_preimage_map {B B' : CommRingCat.{0}} {X : Scheme.{0}} (φ : B ⟶ B') (y : Spec B ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ U) : ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U :=
  fun p _ => h (Set.mem_univ ((Spec.map φ) p))

structure SSAtlas (ϖ : O) (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) (ι A : Type) [Fintype ι] where

  U : A → X.Opens
  affine : ∀ α, IsAffineOpen (U α)
  cover : (⨆ α, U α) = ⊤

  F : ∀ α, ι → Γ(X, U α)

  G : ∀ α β, ι → Γ(X, U α ⊓ U β)ˣ
  prod_F : ∀ α, ∏ i, F α i = (q.appLE ⊤ (U α) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)
  F_eq : ∀ α β i, X.presheaf.map (homOfLE inf_le_left).op (F α i) =
      (G α β i : Γ(X, U α ⊓ U β)) * X.presheaf.map (homOfLE inf_le_right).op (F β i)
  nzd : ∀ α i, F α i ∈ nonZeroDivisors Γ(X, U α)
  chart : ∀ α (x : X), x ∈ U α → ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (hV : V ≤ U α) (m r : ℕ) (_ : 1 ≤ r)
      (_ : r ≤ m) (c : Fin r ↪ ι)
      (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < r),
        MvPolynomial.X j) - MvPolynomial.C ϖ}) →+* Γ(X, V)),
      ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ V le_top).hom ∧
      (∀ j : Fin r, ∃ u : Γ(X, V)ˣ, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (Fin.castLE (by omega) j))) =
        u * X.presheaf.map (homOfLE hV).op (F α (c j))) ∧
      ∀ i, i ∉ Set.range c → IsUnit (X.presheaf.map (homOfLE hV).op (F α i))
  G_self : ∀ α i, G α α i = 1
  G_comp : ∀ α β γ i,
    X.presheaf.map (homOfLE (inf_le_left : U α ⊓ U β ⊓ U γ ≤ U α ⊓ U β)).op (G α β i : Γ(X, U α ⊓ U β)) *
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U α ⊓ U β ⊓ U γ ≤ U β ⊓ U γ)).op (G β γ i : Γ(X, U β ⊓ U γ)) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U α ⊓ U β ⊓ U γ ≤ U α ⊓ U γ)).op (G α γ i : Γ(X, U α ⊓ U γ))
  prod_G : ∀ α β, ∏ i, G α β i = 1

namespace SSAtlas

variable {ϖ : O} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι A : Type} [Fintype ι]
  (C : SSAtlas ϖ X q ι A) {k : Type} [CommRing k] (κ : O →+* k)

open Classical in

def logFun : LogFun k (κ ϖ) where
  ι := ι
  A := A
  Pt := ptFun X q κ
  str z := z.1.1
  str_map _ _ := rfl
  In α _ z := ⊤ ≤ z.1.2 ⁻¹ᵁ C.U α
  in_map := @fun _ _ _ φ y h => le_preimage_map φ y.1.2 h
  f α i B z := if h : ⊤ ≤ z.1.2 ⁻¹ᵁ C.U α then GlobalTheory.Cris.evalAt (B := B) z.1.2 (C.U α) h (C.F α i) else 0
  f_map {α} i B B' φ y h := by
    rw [dif_pos h, dif_pos (show ⊤ ≤ ((ptFun X q κ).map φ y).1.2 ⁻¹ᵁ C.U α from le_preimage_map φ y.1.2 h)]
    exact evalAt_map φ y.1.2 h _ _
  g α β i B z := if h : ⊤ ≤ z.1.2 ⁻¹ᵁ (C.U α ⊓ C.U β) then
      Units.map (GlobalTheory.Cris.evalAt (B := B) z.1.2 (C.U α ⊓ C.U β) h : Γ(X, C.U α ⊓ C.U β) →* B) (C.G α β i) else 1
  g_map {α β} i B B' φ y hα hβ := by
    have h := le_preimage_inf y.1.2 hα hβ
    rw [dif_pos h, dif_pos (show ⊤ ≤ ((ptFun X q κ).map φ y).1.2 ⁻¹ᵁ (C.U α ⊓ C.U β) from le_preimage_map φ y.1.2 h)]
    ext
    exact evalAt_map φ y.1.2 h _ _
  f_eq {α β} i B y hα hβ := by
    have h := le_preimage_inf y.1.2 hα hβ
    rw [dif_pos hα, dif_pos hβ, dif_pos h, Units.coe_map, MonoidHom.coe_coe,
      ← evalAt_res y.1.2 inf_le_left hα h, ← evalAt_res y.1.2 inf_le_right hβ h, ← map_mul, C.F_eq]
  g_self {α} i B y hα := by
    rw [dif_pos (le_preimage_inf y.1.2 hα hα), C.G_self, map_one]
  g_comp {α β γ} i B y hα hβ hγ := by
    have h12 := le_preimage_inf y.1.2 hα hβ
    have h23 := le_preimage_inf y.1.2 hβ hγ
    have h13 := le_preimage_inf y.1.2 hα hγ
    have h123 := le_preimage_inf y.1.2 h12 hγ
    rw [dif_pos h12, dif_pos h23, dif_pos h13]
    ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
    rw [← evalAt_res y.1.2 inf_le_left h12 h123, ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h23 h123,
      ← evalAt_res y.1.2 (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h13 h123,
      ← map_mul, C.G_comp]
  prod_f {α} B y hα := by
    simp only [dif_pos hα]
    rw [← map_prod, C.prod_F]
    exact evalAt_base q κ y.1.1 y.1.2 y.2 hα ϖ
  prod_g {α β} B y hα hβ := by
    simp only [dif_pos (le_preimage_inf y.1.2 hα hβ)]
    rw [← map_prod, C.prod_G, map_one]

end SSAtlas

namespace SSAtlas

variable {ϖ : O} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι A : Type} [Fintype ι]
  {k : Type} [CommRing k] (κ : O →+* k)

theorem isStrictlySemistable (C : SSAtlas ϖ X q ι A) : GlobalTheory.Et.IsStrictlySemistable ϖ q := by
  intro x
  have hx : x ∈ (⨆ α, C.U α) := C.cover ▸ trivial
  obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨V, hVa, hxV, -, m, r, h1, h2, -, ψ, het, hcomp, -, -⟩ := C.chart α x hα
  exact ⟨V, hVa, hxV, m, r, h1, h2, ψ, het, hcomp⟩

open Classical in

theorem isSSFun_logFun (C : SSAtlas ϖ X q ι A) : IsSSFun ϖ X q κ (C.logFun κ) := by
  refine ⟨C.isStrictlySemistable, fun B => Equiv.refl _, C.U, C.F, C.G, C.affine, C.cover, C.prod_F, C.F_eq, C.nzd,
    C.chart, fun φ y => rfl, fun {B} y => ⟨rfl, fun α => ⟨Iff.rfl, fun h => ⟨fun i => dif_pos h, fun β h' i => ?_⟩⟩⟩⟩
  change ((if h : ⊤ ≤ y.1.2 ⁻¹ᵁ (C.U α ⊓ C.U β) then
      Units.map (GlobalTheory.Cris.evalAt (B := B) y.1.2 (C.U α ⊓ C.U β) h : Γ(X, C.U α ⊓ C.U β) →* B) (C.G α β i)
      else 1 : Bˣ) : B) = _
  rw [dif_pos (show ⊤ ≤ y.1.2 ⁻¹ᵁ (C.U α ⊓ C.U β) from h')]
  rfl

end SSAtlas

namespace SSAtlas

variable {ϖ : O} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι A : Type} [Fintype ι]
  {k : Type} [CommRing k] (κ : O →+* k)

theorem logFun_In (C : SSAtlas ϖ X q ι A) (α : A) {B : CommRingCat.{0}} (y : (C.logFun κ).Pt.obj B) :
    (C.logFun κ).In α y ↔ ⊤ ≤ (show PtOver X q κ B from y).1.2 ⁻¹ᵁ C.U α := Iff.rfl

theorem logFun_f (C : SSAtlas ϖ X q ι A) (α : A) (i : ι) {B : CommRingCat.{0}} (y : PtOver X q κ B)
    (h : ⊤ ≤ y.1.2 ⁻¹ᵁ C.U α) : (C.logFun κ).f α i (B := B) y = GlobalTheory.Cris.evalAt y.1.2 (C.U α) h (C.F α i) :=
  dif_pos h

theorem logFun_g (C : SSAtlas ϖ X q ι A) (α β : A) (i : ι) {B : CommRingCat.{0}} (y : PtOver X q κ B)
    (h : ⊤ ≤ y.1.2 ⁻¹ᵁ (C.U α ⊓ C.U β)) :
    ((C.logFun κ).g α β i (B := B) y : B) = GlobalTheory.Cris.evalAt y.1.2 (C.U α ⊓ C.U β) h (C.G α β i) := by
  classical
  change ((if h : ⊤ ≤ y.1.2 ⁻¹ᵁ (C.U α ⊓ C.U β) then
      Units.map (GlobalTheory.Cris.evalAt (B := B) y.1.2 (C.U α ⊓ C.U β) h : Γ(X, C.U α ⊓ C.U β) →* B) (C.G α β i)
      else 1 : Bˣ) : B) = _
  rw [dif_pos h]
  rfl

end SSAtlas

section Model

variable (ϖ : O)

set_option autoImplicit false in
variable {O : Type} [CommRing O] (ϖ : O) in

theorem _root_.GlobalTheory.LogCris.model_mul_eq_zero {m r : ℕ} (hϖ : ϖ ∈ nonZeroDivisors O)
    (g : _root_.GlobalTheory.Et.ssModel O ϖ m r)
    (h : algebraMap O _ ϖ * g = 0) : g = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  set S := Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)
  set d : Fin m →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1
  have hX : (∏ i ∈ S, MvPolynomial.X i : MvPolynomial (Fin m) O) = MvPolynomial.monomial d 1 := by
    simp only [d, MvPolynomial.X, MvPolynomial.monomial_sum_one]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  have h2 : MvPolynomial.C ϖ * g ∈
      Ideal.span {(∏ i ∈ S, MvPolynomial.X i : MvPolynomial (Fin m) O) - MvPolynomial.C ϖ} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact h
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton'.mp h2
  rw [hX] at hp
  have hc : ∀ s, ϖ ∣ MvPolynomial.coeff s p := by
    intro s
    have := congrArg (MvPolynomial.coeff (d + s)) hp
    rw [mul_sub, MvPolynomial.coeff_sub, mul_comm p (MvPolynomial.monomial d 1), mul_comm p (MvPolynomial.C ϖ),
      MvPolynomial.coeff_monomial_mul, one_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at this
    exact ⟨MvPolynomial.coeff (d + s) g + MvPolynomial.coeff (d + s) p, by rw [mul_add, ← this]; ring⟩
  obtain ⟨q, hq⟩ : MvPolynomial.C ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← Set.image_singleton, ← Ideal.map_span, MvPolynomial.mem_map_C_iff]
    intro s
    exact Ideal.mem_span_singleton.mpr (hc s)
  refine ⟨q, ?_⟩
  rw [hX]
  ext s
  have e := congrArg (MvPolynomial.coeff s)
    (show MvPolynomial.C ϖ * (q * (MvPolynomial.monomial d 1 - MvPolynomial.C ϖ)) = MvPolynomial.C ϖ * g by
      rw [← hp, hq]; ring)
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at e
  exact (mul_cancel_left_mem_nonZeroDivisors hϖ).mp e

theorem model_X_mem {m r : ℕ} (hϖ : ϖ ∈ nonZeroDivisors O) (j : Fin m) (hj : (j : ℕ) < r) :
    Ideal.Quotient.mk _ (MvPolynomial.X j) ∈ nonZeroDivisors (GlobalTheory.Et.ssModel O ϖ m r) := by
  classical
  rw [mem_nonZeroDivisors_iff_left]
  intro g hg
  apply model_mul_eq_zero ϖ hϖ g
  have hmem : j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < r) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
  have hP : algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ =
      Ideal.Quotient.mk _ (MvPolynomial.X j) * Ideal.Quotient.mk _
        (∏ l ∈ (Finset.univ.filter (fun j : Fin m => (j : ℕ) < r)).erase j, MvPolynomial.X l) := by
    rw [← map_mul, Finset.mul_prod_erase _ _ hmem]
    change Ideal.Quotient.mk _ (MvPolynomial.C ϖ) = _
    symm
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.mem_span_singleton_self _
  rw [hP, mul_comm (Ideal.Quotient.mk _ _), mul_assoc, hg, mul_zero]

end Model

section ModelAtlas

variable (ϖ : O) (r : ℕ)

abbrev modelStr : Spec (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (GlobalTheory.Et.ssModel O ϖ r r)))

theorem model_appLE (a : O) :
    ((modelStr ϖ r).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))).inv.hom (algebraMap O _ a) := by
  have h : (modelStr ϖ r).appTop = (modelStr ϖ r).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [← h]
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O (GlobalTheory.Et.ssModel O ϖ r r)))
  exact (congrArg (fun t => t.hom a) e).symm

def modelAtlas (hr : 1 ≤ r) (hϖ : ϖ ∈ nonZeroDivisors O) :
    SSAtlas ϖ (Spec (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))) (modelStr ϖ r) (Fin r) Unit where
  U _ := ⊤
  affine _ := isAffineOpen_top _
  cover := by simp
  F _ i := (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))).inv.hom (Ideal.Quotient.mk _ (MvPolynomial.X i))
  G _ _ _ := 1
  prod_F _ := by
    rw [model_appLE, ← map_prod, ← map_prod]
    congr 1
    change _ = Ideal.Quotient.mk _ (MvPolynomial.C ϖ)
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, Finset.filter_true_of_mem (fun j _ => j.isLt)]
    exact Ideal.mem_span_singleton_self _
  F_eq _ _ _ := by rw [Units.val_one, one_mul]
  nzd _ i := by
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have hx' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))).hom.hom hx
    rw [map_mul, map_zero, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at hx'
    have := (mem_nonZeroDivisors_iff_left.1 (model_X_mem ϖ hϖ i i.isLt)) _ hx'
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))).inv.hom this
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero] at h2
  chart _ x _ := by
    refine ⟨⊤, isAffineOpen_top _, trivial, le_rfl, r, r, hr, le_rfl, Function.Embedding.refl _,
      (Scheme.ΓSpecIso (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))).inv.hom,
      RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _), ?_, fun j => ⟨1, ?_⟩,
      fun i hi => absurd ⟨i, rfl⟩ hi⟩
    · ext a
      rw [RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, model_appLE]
    · rw [Units.val_one, one_mul]
      have e : homOfLE (le_rfl : (⊤ : (Spec (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))).Opens) ≤ ⊤) = 𝟙 _ := rfl
      rw [e, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply]
      rfl
  G_self _ _ := rfl
  G_comp _ _ _ _ := by simp
  prod_G _ _ := by simp

abbrev modelFun (hr : 1 ≤ r) (hϖ : ϖ ∈ nonZeroDivisors O) {k : Type} [CommRing k] (κ : O →+* k) : LogFun k (κ ϖ) :=
  (modelAtlas ϖ r hr hϖ).logFun κ

theorem isSSFun_model (hr : 1 ≤ r) (hϖ : ϖ ∈ nonZeroDivisors O) {k : Type} [CommRing k] (κ : O →+* k) :
    IsSSFun ϖ (Spec (CommRingCat.of (GlobalTheory.Et.ssModel O ϖ r r))) (modelStr ϖ r) κ (modelFun ϖ r hr hϖ κ) :=
  (modelAtlas ϖ r hr hϖ).isSSFun_logFun κ

end ModelAtlas

example : IsSSFun (2 : ℤ) (Spec (CommRingCat.of (GlobalTheory.Et.ssModel ℤ 2 2 2))) (modelStr 2 2) (Int.castRingHom (ZMod 2))
    (modelFun 2 2 (by norm_num) (mem_nonZeroDivisors_of_ne_zero (by norm_num)) (Int.castRingHom (ZMod 2))) :=
  isSSFun_model 2 2 (by norm_num) _ _

example : IsSSFun (2 : ℤ) (Spec (CommRingCat.of (GlobalTheory.Et.ssModel ℤ 2 1 1))) (modelStr 2 1) (RingHom.id ℤ)
    (modelFun 2 1 le_rfl (mem_nonZeroDivisors_of_ne_zero (by norm_num)) (RingHom.id ℤ)) :=
  isSSFun_model 2 1 le_rfl _ _

example : Fintype.card (modelFun (2 : ℤ) 2 (by norm_num) (mem_nonZeroDivisors_of_ne_zero (by norm_num))
    (RingHom.id ℤ)).ι = 2 := by
  simp [modelFun, SSAtlas.logFun]

end GlobalTheory.LogCris
