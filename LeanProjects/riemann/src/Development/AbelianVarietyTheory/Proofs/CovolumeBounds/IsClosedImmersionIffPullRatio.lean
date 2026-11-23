import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjSpace

variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}

theorem appLE_of_eq {φ ψ : Z ⟶ Y} (h : φ = ψ) (U : Y.Opens) (V : Z.Opens) (h₁ : V ≤ φ ⁻¹ᵁ U)
    (h₂ : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V h₁ = ψ.appLE U V h₂ := by
  subst h
  rfl

theorem resG_appLE (g : Z ⟶ Y) {U : Y.Opens} {V W : Z.Opens} (h : V ≤ g ⁻¹ᵁ U) (h' : W ≤ V)
    (a : Γ(Y, U)) :
    resG Z h' ((g.appLE U V h).hom a) = (g.appLE U W (h'.trans h)).hom a :=
  congrArg (fun φ => φ.hom a) (g.appLE_map h (homOfLE h').op)

theorem appLE_resG (g : Z ⟶ Y) {U U' : Y.Opens} {V : Z.Opens} (h' : U' ≤ U) (h : V ≤ g ⁻¹ᵁ U')
    (a : Γ(Y, U)) :
    (g.appLE U' V h).hom (resG Y h' a) = (g.appLE U V (h.trans (g.preimage_mono h'))).hom a :=
  congrArg (fun φ => φ.hom a) (g.map_appLE h (homOfLE h').op)

theorem appLE_appLE {X : Scheme.{0}} (g : Z ⟶ Y) (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)) :
    (g.appLE V W h').hom ((φ.appLE U V h).hom a) =
      ((g ≫ φ).appLE U W (h'.trans (g.preimage_mono h))).hom a :=
  congrArg (fun ψ => ψ.hom a) (Scheme.Hom.appLE_comp_appLE g φ U V W h h')

theorem baseRingHom_appLE {B : CommRingCat.{0}} (p : Y ⟶ Spec B) (g : Z ⟶ Y) (U : Y.Opens) (V : Z.Opens)
    (h : V ≤ g ⁻¹ᵁ U) : baseRingHom p U ≫ g.appLE U V h = baseRingHom (g ≫ p) V :=
  (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Scheme.Hom.appLE_comp_appLE g p ⊤ U V le_top h))

theorem eq_of_baseRingHom_top {B : CommRingCat.{0}} {p q : Y ⟶ Spec B}
    (h : baseRingHom p ⊤ = baseRingHom q ⊤) : p = q := by
  rw [baseRingHom_top, baseRingHom_top, cancel_epi] at h
  exact ext_of_isAffine h

instance isIso_ι_appLE_top (U : Y.Opens) (h : ⊤ ≤ U.ι ⁻¹ᵁ U) : IsIso (U.ι.appLE U ⊤ h) := by
  rw [Scheme.Opens.ι_appLE]
  have e : U.ι ''ᵁ ⊤ = U := by simp
  have : ∀ i : U.ι ''ᵁ ⊤ ⟶ U, IsIso (Y.presheaf.map i.op) := fun i =>
    (Subsingleton.elim i (eqToHom e)) ▸ inferInstance
  exact this _

def pullRatio (φ : Y ⟶ PSpace R N) (W : Y.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (j : Fin (N + 1)) : Γ(Y, W) :=
  (φ.appLE (chart R N i) W hi).hom (ratio R N i j)

section

variable {φ : Y ⟶ PSpace R N} {W V : Y.Opens} {i j k : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {hj : W ≤ φ ⁻¹ᵁ chart R N j}

theorem resG_pullRatio (h : V ≤ W) :
    resG Y h (pullRatio φ W i hi j) = pullRatio φ V i (h.trans hi) j :=
  resG_appLE φ hi h _

@[simp] theorem pullRatio_self : pullRatio φ W i hi i = 1 := by
  rw [pullRatio, ratio, ratioOn_self, map_one]

theorem appLE_ratioOn {U : (PSpace R N).Opens} (hU : U ≤ chart R N i) (hW : W ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U W hW).hom (ratioOn U i hU j) = pullRatio φ W i (hW.trans (φ.preimage_mono hU)) j :=
  appLE_resG φ hU hW (ratio R N i j)

theorem pullRatio_mul_pullRatio :
    pullRatio φ W i hi j * pullRatio φ W j hj k = pullRatio φ W i hi k := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R N i ⊓ chart R N j) := le_inf hi hj
  rw [← appLE_ratioOn inf_le_left hW, ← appLE_ratioOn inf_le_right hW, ← appLE_ratioOn inf_le_left hW,
    ← map_mul, ratioOn_mul_ratioOn]

theorem basicOpen_pullRatio : Y.basicOpen (pullRatio φ W i hi j) = W ⊓ φ ⁻¹ᵁ chart R N j := by
  refine (Scheme.basicOpen_appLE φ W _ hi _).trans ?_
  rw [ratio, basicOpen_ratioOn]
  exact le_antisymm (inf_le_inf_left _ (φ.preimage_mono inf_le_right))
    (le_inf inf_le_left (le_inf (inf_le_left.trans hi) inf_le_right))

theorem appLE_pullRatio (g : Z ⟶ Y) {T : Z.Opens} (h : T ≤ g ⁻¹ᵁ W) :
    (g.appLE W T h).hom (pullRatio φ W i hi j) =
      pullRatio (g ≫ φ) T i (h.trans (g.preimage_mono hi)) j :=
  congrArg (fun ψ => ψ.hom (ratio R N i j)) (Scheme.Hom.appLE_comp_appLE g φ _ _ _ hi h)

theorem pullRatio_of_eq {ψ : Y ⟶ PSpace R N} (h : φ = ψ) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (hi' : W ≤ ψ ⁻¹ᵁ chart R N i) : pullRatio φ W i hi j = pullRatio ψ W i hi' j := by
  subst h
  rfl

theorem appLE_comp_aeval_ratio :
    (φ.appLE (chart R N i) W hi).hom.comp
        (RingHomClass.toRingHom (aeval (R := R) (ratio R N i))) =
      eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) W).hom (pullRatio φ W i hi) := by
  refine ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp only [RingHom.comp_apply, RingHom.coe_coe, algHom_C, eval₂Hom_C]
    exact congrArg (fun ψ => ψ.hom r) (baseRingHom_appLE (PSpace.str R N) φ _ W hi)
  · simp only [RingHom.comp_apply, RingHom.coe_coe, aeval_X, eval₂Hom_X']
    rfl

end

theorem ι_comp_eq (φ : Y ⟶ PSpace R N) (W : Y.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i) :
    W.ι ≫ φ = W.toSpecΓ ≫ Spec.map (φ.appLE (chart R N i) W hi) ≫ (isAffineOpen_chart R N i).fromSpec := by
  rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

theorem hom_ext {φ ψ : Y ⟶ PSpace R N} (h : φ ≫ PSpace.str R N = ψ ≫ PSpace.str R N)
    (H : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (i : Fin (N + 1)) (h₁ : W ≤ φ ⁻¹ᵁ chart R N i)
      (h₂ : W ≤ ψ ⁻¹ᵁ chart R N i), ∀ j, pullRatio φ W i h₁ j = pullRatio ψ W i h₂ j) : φ = ψ := by
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨W, hy, i, h₁, h₂, e⟩ := H y
  refine ⟨W, hy, ?_⟩
  have : φ.appLE (chart R N i) W h₁ = ψ.appLE (chart R N i) W h₂ := by
    ext1
    refine RingHom.ext fun a => ?_
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective R N i a
    have e₁ := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (hi := h₁))
    have e₂ := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := ψ) (hi := h₂))
    rw [h, funext e] at e₁
    exact e₁.trans e₂.symm
  rw [ι_comp_eq φ W i h₁, ι_comp_eq ψ W i h₂, this]

def ofChartHom (i : Fin (N + 1)) (ρ : Γ(PSpace R N, chart R N i) ⟶ Γ(Y, ⊤)) : Y ⟶ PSpace R N :=
  Y.toSpecΓ ≫ Spec.map ρ ≫ (isAffineOpen_chart R N i).fromSpec

theorem ofChartHom_preimage (i : Fin (N + 1)) (ρ : Γ(PSpace R N, chart R N i) ⟶ Γ(Y, ⊤)) :
    ⊤ ≤ ofChartHom i ρ ⁻¹ᵁ chart R N i := by
  rw [ofChartHom, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
  exact le_rfl

theorem ofChartHom_appLE (i : Fin (N + 1)) (ρ : Γ(PSpace R N, chart R N i) ⟶ Γ(Y, ⊤)) :
    (ofChartHom i ρ).appLE (chart R N i) ⊤ (ofChartHom_preimage i ρ) = ρ := by
  have h1 : (isAffineOpen_chart R N i).fromSpec.appLE (chart R N i) ⊤
      (isAffineOpen_chart R N i).fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h2 : (Y.toSpecΓ ≫ Spec.map ρ).appLE ⊤ ⊤ le_rfl = (Scheme.ΓSpecIso _).hom ≫ ρ := by
    refine Eq.trans (Scheme.Hom.app_eq_appLE _).symm ?_
    change (Y.toSpecΓ ≫ Spec.map ρ).appTop = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  have h3 := Scheme.Hom.appLE_comp_appLE (Y.toSpecΓ ≫ Spec.map ρ) (isAffineOpen_chart R N i).fromSpec
    (chart R N i) ⊤ ⊤ (isAffineOpen_chart R N i).fromSpec_preimage_self.ge le_rfl
  rw [h1, h2, Iso.inv_hom_id_assoc] at h3
  exact h3.symm

def chartLift {A : Type} [CommRing A] (i : Fin (N + 1)) (c : R →+* A) (r : Fin (N + 1) → A) :
    Γ(PSpace R N, chart R N i) →+* A :=
  (eval₂Hom c fun j : {j // j ≠ i} => r j.1).comp
    (RingHomClass.toRingHom (chartAlgEquiv R N i).symm)

theorem chartLift_algebraMap {A : Type} [CommRing A] (i : Fin (N + 1)) (c : R →+* A) (r : Fin (N + 1) → A)
    (a : R) : chartLift i c r (algebraMap R _ a) = c a := by
  simp only [chartLift, RingHom.comp_apply, RingHom.coe_coe]
  rw [AlgEquiv.commutes]
  exact eval₂Hom_C _ _ a

theorem chartLift_ratio {A : Type} [CommRing A] (i : Fin (N + 1)) (c : R →+* A) {r : Fin (N + 1) → A}
    (hr : r i = 1) (j : Fin (N + 1)) : chartLift i c r (ratio R N i j) = r j := by
  by_cases h : j = i
  · subst h
    rw [ratio, ratioOn_self, map_one, hr]
  · simp only [chartLift, RingHom.comp_apply, RingHom.coe_coe]
    rw [← chartAlgEquiv_X R N i ⟨j, h⟩, AlgEquiv.symm_apply_apply, eval₂Hom_X']

def ofCoords (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    U.toScheme ⟶ PSpace R N :=
  ofChartHom i (CommRingCat.ofHom (R := Γ(PSpace R N, chart R N i)) (S := Γ(Y, U))
      (chartLift i (baseRingHom f U).hom r) ≫
    U.ι.appLE U ⊤ U.ι_preimage_self.ge)

theorem ofCoords_preimage_top (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    ⊤ ≤ ofCoords f U i r ⁻¹ᵁ chart R N i := by
  unfold ofCoords
  exact ofChartHom_preimage i _

theorem ofCoords_appLE (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    (ofCoords f U i r).appLE (chart R N i) ⊤ (ofCoords_preimage_top f U i r) =
      CommRingCat.ofHom (R := Γ(PSpace R N, chart R N i)) (S := Γ(Y, U))
        (chartLift i (baseRingHom f U).hom r) ≫ U.ι.appLE U ⊤ U.ι_preimage_self.ge :=
  ofChartHom_appLE i _

theorem ofCoords_preimage (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U))
    (g : Z ⟶ U.toScheme) : ⊤ ≤ (g ≫ ofCoords f U i r) ⁻¹ᵁ chart R N i :=
  le_trans le_top (g.preimage_mono (ofCoords_preimage_top f U i r))

theorem ofCoords_str (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    ofCoords f U i r ≫ PSpace.str R N = U.ι ≫ f := by
  refine eq_of_baseRingHom_top ?_
  rw [← baseRingHom_appLE _ (ofCoords f U i r) (chart R N i) ⊤ (ofCoords_preimage_top f U i r),
    ← baseRingHom_appLE f U.ι U ⊤ U.ι_preimage_self.ge, ofCoords_appLE, ← Category.assoc]
  congr 1
  ext1
  exact RingHom.ext fun a => chartLift_algebraMap i _ r a

theorem pullRatio_comp_ofCoords (f : Y ⟶ Sp R) (U : Y.Opens) (i : Fin (N + 1))
    {r : Fin (N + 1) → Γ(Y, U)} (hr : r i = 1) (g : Z ⟶ U.toScheme) (T : Z.Opens)
    (h : T ≤ (g ≫ ofCoords f U i r) ⁻¹ᵁ chart R N i) (h' : T ≤ (g ≫ U.ι) ⁻¹ᵁ U) (j : Fin (N + 1)) :
    pullRatio (g ≫ ofCoords f U i r) T i h j = ((g ≫ U.ι).appLE U T h').hom (r j) := by
  have e : pullRatio (ofCoords f U i r) ⊤ i (ofCoords_preimage_top f U i r) j =
      (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (r j) :=
    (congrArg (fun ψ => ψ.hom (ratio R N i j)) (ofCoords_appLE f U i r)).trans
      (congrArg (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (chartLift_ratio i _ hr j))
  rw [← appLE_pullRatio (hi := ofCoords_preimage_top f U i r) g (le_top : T ≤ g ⁻¹ᵁ ⊤), e]
  exact appLE_appLE g U.ι _ _ _

structure IsCoordFamily (U : Fin (N + 1) → Y.Opens) (r : ∀ i, Fin (N + 1) → Γ(Y, U i)) : Prop where

  cover : ⨆ i, U i = ⊤

  self : ∀ i, r i i = 1

  mul : ∀ i j k, resG Y (inf_le_left : U i ⊓ U j ≤ U i) (r i j) * resG Y inf_le_right (r j k) =
    resG Y inf_le_left (r i k)

  basicOpen_le : ∀ i j, Y.basicOpen (r i j) ≤ U j

theorem isCoordFamily_pullRatio (φ : Y ⟶ PSpace R N) :
    IsCoordFamily (fun i => φ ⁻¹ᵁ chart R N i) (fun i => pullRatio φ _ i le_rfl) where
  cover := by rw [← Scheme.Hom.preimage_iSup, iSup_chart]; rfl
  self _ := pullRatio_self
  mul i j k := by rw [resG_pullRatio, resG_pullRatio, resG_pullRatio, pullRatio_mul_pullRatio]
  basicOpen_le _ _ := basicOpen_pullRatio.le.trans inf_le_right

namespace IsCoordFamily

variable {U : Fin (N + 1) → Y.Opens} {r : ∀ i, Fin (N + 1) → Γ(Y, U i)} (H : IsCoordFamily U r)

include H

theorem appLE_mul (g : Z ⟶ Y) {T : Z.Opens} {i j : Fin (N + 1)} (hi : T ≤ g ⁻¹ᵁ U i) (hj : T ≤ g ⁻¹ᵁ U j)
    (k : Fin (N + 1)) :
    (g.appLE _ T hi).hom (r i j) * (g.appLE _ T hj).hom (r j k) = (g.appLE _ T hi).hom (r i k) := by
  have hT : T ≤ g ⁻¹ᵁ (U i ⊓ U j) := le_inf hi hj
  have := congrArg (g.appLE (U i ⊓ U j) T hT).hom (H.mul i j k)
  rwa [map_mul, appLE_resG, appLE_resG, appLE_resG] at this

theorem isUnit_appLE (g : Z ⟶ Y) {T : Z.Opens} {i j : Fin (N + 1)} (hi : T ≤ g ⁻¹ᵁ U i)
    (hj : T ≤ g ⁻¹ᵁ U j) : IsUnit ((g.appLE _ T hi).hom (r i j)) :=
  .of_mul_eq_one _ ((H.appLE_mul g hi hj i).trans (by rw [H.self, map_one]))

theorem basicOpen_eq (i j : Fin (N + 1)) : Y.basicOpen (r i j) = U i ⊓ U j := by
  refine le_antisymm (le_inf (Y.basicOpen_le _) (H.basicOpen_le i j)) ?_
  have hu : IsUnit (resG Y (inf_le_left : U i ⊓ U j ≤ U i) (r i j)) :=
    .of_mul_eq_one _ ((H.mul i j i).trans (by rw [H.self, map_one]))
  have := Y.basicOpen_of_isUnit hu
  rw [Scheme.basicOpen_res] at this
  exact this.ge.trans inf_le_right

theorem comp_ofCoords_eq (f : Y ⟶ Sp R) (i j : Fin (N + 1)) (a : Z ⟶ (U i).toScheme)
    (b : Z ⟶ (U j).toScheme) (e : a ≫ (U i).ι = b ≫ (U j).ι) :
    a ≫ ofCoords f (U i) i (r i) = b ≫ ofCoords f (U j) j (r j) := by
  have ha : ⊤ ≤ (a ≫ (U i).ι) ⁻¹ᵁ U i := a.preimage_mono (U i).ι_preimage_self.ge
  have hb : ⊤ ≤ (b ≫ (U j).ι) ⁻¹ᵁ U j := b.preimage_mono (U j).ι_preimage_self.ge
  have hb' : ⊤ ≤ (b ≫ (U j).ι) ⁻¹ᵁ U i := e ▸ ha
  have h₁ : ⊤ ≤ (a ≫ ofCoords f (U i) i (r i)) ⁻¹ᵁ chart R N i := ofCoords_preimage f _ i _ a
  have h₂ : ⊤ ≤ (b ≫ ofCoords f (U j) j (r j)) ⁻¹ᵁ chart R N j := ofCoords_preimage f _ j _ b
  have hu := H.isUnit_appLE (b ≫ (U j).ι) hb hb'
  have e₂ := pullRatio_comp_ofCoords f (U j) j (H.self j) b ⊤ h₂ hb
  have h₃ : ⊤ ≤ (b ≫ ofCoords f (U j) j (r j)) ⁻¹ᵁ chart R N i := by
    have := basicOpen_pullRatio (hi := h₂) (j := i)
    rw [e₂, Z.basicOpen_of_isUnit hu] at this
    exact this.le.trans inf_le_right
  refine hom_ext ?_ fun _ => ⟨⊤, trivial, i, h₁, h₃, fun k => ?_⟩
  · rw [Category.assoc, Category.assoc, ofCoords_str, ofCoords_str, reassoc_of% e]
  · refine hu.mul_left_cancel ?_
    rw [pullRatio_comp_ofCoords f (U i) i (H.self i) a ⊤ h₁ ha, appLE_of_eq e _ _ ha hb',
      H.appLE_mul _ hb hb', ← e₂, ← e₂, pullRatio_mul_pullRatio]

def toHom (f : Y ⟶ Sp R) : Y ⟶ PSpace R N :=
  (Y.openCoverOfIsOpenCover U H.cover).glueMorphisms (fun i => ofCoords f (U i) i (r i))
    fun i j => H.comp_ofCoords_eq f i j _ _ pullback.condition

theorem ι_toHom (f : Y ⟶ Sp R) (i : Fin (N + 1)) : (U i).ι ≫ H.toHom f = ofCoords f (U i) i (r i) :=
  (Y.openCoverOfIsOpenCover U H.cover).ι_glueMorphisms _ _ i

theorem exists_mem (y : Y) : ∃ i, y ∈ U i := Opens.mem_iSup.1 (H.cover.ge (Set.mem_univ y))

theorem toHom_str (f : Y ⟶ Sp R) : H.toHom f ≫ PSpace.str R N = f := by
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨i, hi⟩ := H.exists_mem y
  exact ⟨U i, hi, by rw [← Category.assoc, ι_toHom, ofCoords_str]⟩

theorem le_toHom_preimage (f : Y ⟶ Sp R) (i : Fin (N + 1)) : U i ≤ H.toHom f ⁻¹ᵁ chart R N i := by
  intro y hy
  have : ⊤ ≤ ((U i).ι ≫ H.toHom f) ⁻¹ᵁ chart R N i := by
    rw [ι_toHom]
    exact ofCoords_preimage_top _ _ _ _
  exact this (Set.mem_univ (⟨y, hy⟩ : U i))

theorem pullRatio_toHom (f : Y ⟶ Sp R) (i j : Fin (N + 1)) :
    pullRatio (H.toHom f) (U i) i (H.le_toHom_preimage f i) j = r i j := by
  refine (ConcreteCategory.bijective_of_isIso ((U i).ι.appLE (U i) ⊤ (U i).ι_preimage_self.ge)).1 ?_
  refine (appLE_pullRatio _ _).trans ?_
  refine (pullRatio_of_eq ((H.ι_toHom f i).trans (Category.id_comp _).symm) _
    (ofCoords_preimage f _ i _ (𝟙 _))).trans ?_
  exact pullRatio_comp_ofCoords f (U i) i (H.self i) (𝟙 _) ⊤ _ (U i).ι_preimage_self.ge j

theorem toHom_preimage (f : Y ⟶ Sp R) (i : Fin (N + 1)) : H.toHom f ⁻¹ᵁ chart R N i = U i := by
  refine le_antisymm (fun y hy => ?_) (H.le_toHom_preimage f i)
  obtain ⟨k, hk⟩ := H.exists_mem y
  refine H.basicOpen_le k i ?_
  rw [← H.pullRatio_toHom f k i, basicOpen_pullRatio]
  exact ⟨hk, hy⟩

end IsCoordFamily

theorem surjective_appLE_chart_iff {φ : Y ⟶ PSpace R N} {W : Y.Opens} {i : Fin (N + 1)}
    (hi : W ≤ φ ⁻¹ᵁ chart R N i) :
    Function.Surjective (φ.appLE (chart R N i) W hi).hom ↔
      Function.Surjective (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) W).hom (pullRatio φ W i hi)) := by
  rw [← appLE_comp_aeval_ratio]
  exact (Function.Surjective.of_comp_iff _ (aeval_ratio_surjective R N i)).symm

theorem isClosedImmersion_iff_pullRatio (φ : Y ⟶ PSpace R N) {U : Fin (N + 1) → Y.Opens}
    (hU : ∀ i, φ ⁻¹ᵁ chart R N i = U i) :
    IsClosedImmersion φ ↔ ∀ i, IsAffineOpen (U i) ∧ Function.Surjective
      (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) (U i)).hom (pullRatio φ (U i) i (hU i).ge)) := by
  obtain rfl : (fun i => φ ⁻¹ᵁ chart R N i) = U := funext hU
  have key : ∀ i, Function.Surjective (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) (φ ⁻¹ᵁ chart R N i)).hom
      (pullRatio φ (φ ⁻¹ᵁ chart R N i) i (hU i).ge)) ↔ Function.Surjective (φ.app (chart R N i)).hom :=
    fun i => by rw [← surjective_appLE_chart_iff, Scheme.Hom.app_eq_appLE]
  simp only [key]
  refine ⟨fun _ i => ⟨(isAffineOpen_chart R N i).preimage φ,
    φ.app_surjective _ (isAffineOpen_chart R N i)⟩, fun h => ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ (iSup_chart R N)).2 fun i => ?_
  have : IsAffine (chart R N i) := isAffineOpen_chart R N i
  have : IsAffine (φ ⁻¹ᵁ chart R N i) := (h i).1
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk (h i).1.isoSpec (isAffineOpen_chart R N i).isoSpec
      (Scheme.Opens.toSpecΓ_naturality φ _) :
      Arrow.mk (φ ∣_ chart R N i) ≅ Arrow.mk (Spec.map (φ.app (chart R N i))))]
  exact IsClosedImmersion.spec_of_surjective _ (h i).2

end GlobalTheory.ProjSpace
