import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LiftChartIdeal

noncomputable section

namespace GlobalTheory.Points

open AlgebraicGeometry CategoryTheory Limits Topology Filter TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Values

variable {C : Type} [CommRing C] {X Y : Scheme.{0}}

def valMap (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) ⟶ CommRingCat.of C :=
  x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom

theorem valR_eq (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = (valMap x U h).hom f := dif_pos h

theorem valF_eq_valR {F : Type} [Field F] (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valF x U f = valR x U f := rfl

theorem valAt'_eq_valR (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valAt' x U f = valR x U f := rfl

theorem valAt_eq_valR (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt x U h f = valR x U f := (valR_eq x U h f).symm

theorem le_preimage_mono (x : Sp C ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ U :=
  fun _ hz => e (h hz)

theorem le_preimage_comp (x : Sp C ⟶ X) (g : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U :=
  fun _ hz => e (h hz)

theorem appLE_valMap (x : Sp C ⟶ X) (g : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U) : g.appLE U V e ≫ valMap x V h = valMap (x ≫ g) U h' := by
  rw [valMap, valMap, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]

theorem res_valMap (x : Sp C ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x ⁻¹ᵁ U) :
    X.presheaf.map (homOfLE e).op ≫ valMap x V h = valMap x U h' := by
  rw [valMap, valMap, ← Category.assoc, Scheme.Hom.map_appLE]

theorem valR_appLE (x : Sp C ⟶ X) (g : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)) : valR x V ((g.appLE U V e).hom f) = valR (x ≫ g) U f := by
  rw [valR_eq x V h, valR_eq _ U (le_preimage_comp x g e h), ← appLE_valMap x g e h]
  rfl

theorem valR_comp (x : Sp C ⟶ X) (g : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valR (x ≫ g) U f = valR x (g ⁻¹ᵁ U) ((g.app U).hom f) := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ U)
  · rw [← valR_appLE x g le_rfl h, Scheme.Hom.appLE_eq_app]
  · have h' : ¬ ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := h
    rw [valR, valR, dif_neg h, dif_neg h']

theorem valR_res (x : Sp C ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE e).op).hom f) = valR x U f := by
  rw [valR_eq x V h, valR_eq _ U (le_preimage_mono x e h), ← res_valMap x e h]
  rfl

theorem valR_add (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq x U h, map_add]

theorem valR_mul (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_neg (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U (-f) = -valR x U f := by
  simp only [valR_eq x U h, map_neg]

theorem valR_pow (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_eq x U h, map_pow]

theorem valR_one (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : valR x U 1 = 1 := by
  simp only [valR_eq x U h, map_one]

theorem valR_zero (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : valR x U 0 = 0 := by
  simp only [valR_eq x U h, map_zero]

theorem le_preimage_top (x : Sp C ⟶ X) : ⊤ ≤ x ⁻¹ᵁ ⊤ := fun _ _ => trivial

theorem valMap_specMap {A : CommRingCat.{0}} (φ : A ⟶ CommRingCat.of C) (h : ⊤ ≤ Spec.map φ ⁻¹ᵁ ⊤) :
    valMap (Spec.map φ) ⊤ h = (Scheme.ΓSpecIso A).hom ≫ φ := by
  rw [valMap, ← Scheme.ΓSpecIso_naturality]
  congr 1

theorem valR_specMap {A : CommRingCat.{0}} (φ : A ⟶ CommRingCat.of C) (a : A) :
    valR (Spec.map φ) ⊤ ((Scheme.ΓSpecIso A).inv.hom a) = φ.hom a := by
  rw [valR_eq _ ⊤ (le_preimage_top _), valMap_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id_assoc]

theorem preimage_apply {A : CommRingCat.{0}} (x : Sp C ⟶ Spec A) (a : A) :
    (Spec.preimage x).hom a = valR x ⊤ ((Scheme.ΓSpecIso A).inv.hom a) := by
  conv_rhs => rw [← Spec.map_preimage x]
  exact (valR_specMap _ a).symm

theorem specMap_valMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (x : Sp C ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    Spec.map (valMap x U h) ≫ hU.fromSpec = x := by
  have H := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp C)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at H
  rw [valMap, Spec.map_comp, Category.assoc, H, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem le_preimage_specMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) ⟶ CommRingCat.of C) :
    ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U :=
  le_preimage_comp (V := ⊤) _ _ hU.fromSpec_preimage_self.ge le_top

theorem valMap_specMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (φ : Γ(X, U) ⟶ CommRingCat.of C)
    (h : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U) : valMap (Spec.map φ ≫ hU.fromSpec) U h = φ := by
  apply Spec.map_injective
  rw [← cancel_mono hU.fromSpec, specMap_valMap_fromSpec]

theorem ext_of_valR {U : X.Opens} (hU : IsAffineOpen U) {x y : Sp C ⟶ X} (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (H : ∀ f, valR x U f = valR y U f) : x = y := by
  have : valMap x U hx = valMap y U hy := by
    ext f
    rw [← valR_eq, ← valR_eq, H]
  rw [← specMap_valMap_fromSpec hU x hx, this, specMap_valMap_fromSpec]

theorem le_preimage_basicOpen_iff (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ IsUnit (valR x U f) := by
  constructor
  · intro hf
    rw [← valR_res x (X.basicOpen_le f) hf, valR_eq x _ hf]
    exact (RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace f).map _
  · intro hf
    rw [valR_eq x U h] at hf
    have h1 : IsUnit ((x.appLE U ⊤ h).hom f) := by
      have h2 := hf.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
      rwa [← CommRingCat.comp_apply, valMap, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
    have h3 := Scheme.basicOpen_appLE x ⊤ U h f
    rw [Scheme.basicOpen_of_isUnit _ h1] at h3
    exact h3.le.trans inf_le_right

theorem valR_spMap_comp {C' : Type} [CommRing C'] (σ : C →+* C') (x : Sp C ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap σ ≫ x) U f = σ (valR x U f) := by
  rw [← valR_appLE (spMap σ) x h (le_preimage_top _), valR_eq _ ⊤ (le_preimage_top _), valMap_specMap, valR_eq x U h]
  rfl

theorem valR_constFn {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : Sp C ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) : valR x U (constFn p U a) = (Spec.preimage (x ≫ p)).hom a := by
  rw [preimage_apply]
  exact valR_appLE x p _ h _

theorem valR_constFn_of_over {R : Type} [CommRing R] (p : X ⟶ Sp R) (σ : R →+* C) (x : Sp C ⟶ X)
    (hx : x ≫ p = spMap σ) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) : valR x U (constFn p U a) = σ a := by
  rw [valR_constFn p x U h, hx, Spec.preimage_map]
  rfl

theorem valR_constFn_of_section (p : X ⟶ Sp C) (x : Sp C ⟶ X) (hx : x ≫ p = 𝟙 _) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : C) : valR x U (constFn p U a) = a :=
  valR_constFn_of_over p (RingHom.id C) x (hx.trans (Spec.map_id _).symm) U h a

variable [IsLocalRing C]

theorem le_preimage_iff (x : Sp C ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint C) ∈ U :=
  ⟨fun h => h (x := IsLocalRing.closedPoint C) trivial,
    fun h => (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of C) x h).ge⟩

theorem exists_isAffineOpen_le (x : Sp C ⟶ X) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U ∧ U ≤ V := by
  obtain ⟨U, hU, hx, hle⟩ := exists_isAffineOpen_mem_and_subset ((le_preimage_iff x V).1 h)
  exact ⟨U, hU, (le_preimage_iff x U).2 hx, hle⟩

theorem exists_le_preimage_of_iSup_eq_top (x : Sp C ⟶ X) {ι : Sort*} {U : ι → X.Opens} (hU : iSup U = ⊤) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ U i := by
  have h : x (IsLocalRing.closedPoint C) ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h
  exact ⟨i, (le_preimage_iff x _).2 hi⟩

end Values

section Top

variable {C : Type} [CommRing C] {X Y Z : Scheme.{0}}

def basicSet (U : X.Opens) (f : Γ(X, U)) (O : Set C) : Set (Sp C ⟶ X) :=
  {x | ⊤ ≤ x ⁻¹ᵁ U ∧ valR x U f ∈ O}

abbrev PtsOver {S : Scheme.{0}} (p : X ⟶ S) (s : Sp C ⟶ S) : Type := {x : Sp C ⟶ X // x ≫ p = s}

abbrev Pts (p : X ⟶ Sp C) : Type := PtsOver p (𝟙 (Sp C))

def PtsOver.map {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (g : X ⟶ Y) (hg : g ≫ q = p) (s : Sp C ⟶ S) :
    PtsOver p s → PtsOver q s :=
  fun x => ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩

@[simp] theorem PtsOver.map_val {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (g : X ⟶ Y) (hg : g ≫ q = p)
    (s : Sp C ⟶ S) (x : PtsOver p s) : (PtsOver.map g hg s x).1 = x.1 ≫ g := rfl

@[simp] theorem PtsOver.map_id {S : Scheme.{0}} (p : X ⟶ S) (s : Sp C ⟶ S) (x : PtsOver p s) :
    PtsOver.map (𝟙 X) (Category.id_comp p) s x = x := Subtype.ext (Category.comp_id _)

theorem PtsOver.map_map {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} {r : Z ⟶ S} (g : X ⟶ Y) (hg : g ≫ q = p)
    (k : Y ⟶ Z) (hk : k ≫ r = q) (s : Sp C ⟶ S) (x : PtsOver p s) :
    PtsOver.map k hk s (PtsOver.map g hg s x) =
      PtsOver.map (g ≫ k) (by rw [Category.assoc, hk, hg]) s x := Subtype.ext (Category.assoc _ _ _)

variable [TopologicalSpace C]

instance topology (C : Type) [CommRing C] [TopologicalSpace C] (X : Scheme.{0}) :
    TopologicalSpace (Sp C ⟶ X) :=
  generateFrom {S | ∃ (U : X.Opens) (f : Γ(X, U)) (O : Set C), IsOpen O ∧ S = basicSet U f O}

theorem topology_complex (X : Scheme.{0}) : topology ℂ X =
    generateFrom {S | ∃ (U : X.Opens) (f : Γ(X, U)) (O : Set ℂ), IsOpen O ∧
      S = {x : Sp ℂ ⟶ X | ∃ h : ⊤ ≤ x ⁻¹ᵁ U, valAt x U h f ∈ O}} := by
  have : ∀ (U : X.Opens) (f : Γ(X, U)) (O : Set ℂ),
      basicSet U f O = {x : Sp ℂ ⟶ X | ∃ h : ⊤ ≤ x ⁻¹ᵁ U, valAt x U h f ∈ O} := by
    intro U f O
    ext x
    simp only [basicSet, Set.mem_setOf_eq, valAt_eq_valR, exists_prop]
  simp only [topology, this]

theorem isOpen_basicSet (U : X.Opens) (f : Γ(X, U)) {O : Set C} (hO : IsOpen O) :
    IsOpen (basicSet U f O) :=
  isOpen_generateFrom_of_mem ⟨U, f, O, hO, rfl⟩

theorem isOpen_setOf_le_preimage (U : X.Opens) : IsOpen {x : Sp C ⟶ X | ⊤ ≤ x ⁻¹ᵁ U} := by
  convert isOpen_basicSet (C := C) U 0 isOpen_univ using 1
  ext x
  simp [basicSet]

theorem tendsto_iff {B : Type*} {e : B → (Sp C ⟶ X)} {l : Filter B} {x : Sp C ⟶ X} :
    Tendsto e l (𝓝 x) ↔ ∀ U : X.Opens, ⊤ ≤ x ⁻¹ᵁ U → (∀ᶠ b in l, ⊤ ≤ e b ⁻¹ᵁ U) ∧
      ∀ f : Γ(X, U), Tendsto (fun b => valR (e b) U f) l (𝓝 (valR x U f)) := by
  constructor
  · intro H U hU
    refine ⟨H.eventually ((isOpen_setOf_le_preimage U).mem_nhds hU), fun f => ?_⟩
    rw [tendsto_nhds]
    intro O hO hx
    filter_upwards [H.eventually ((isOpen_basicSet U f hO).mem_nhds ⟨hU, hx⟩)] with b hb using hb.2
  · intro H
    refine tendsto_nhds_generateFrom_iff.2 ?_
    rintro _ ⟨U, f, O, hO, rfl⟩ ⟨hU, hx⟩
    filter_upwards [(H U hU).1, ((H U hU).2 f).eventually (hO.mem_nhds hx)] with b h1 h2 using ⟨h1, h2⟩

theorem continuousAt_valR {U : X.Opens} (f : Γ(X, U)) {x : Sp C ⟶ X} (hx : ⊤ ≤ x ⁻¹ᵁ U) :
    ContinuousAt (fun y : Sp C ⟶ X => valR y U f) x :=
  ((tendsto_iff (e := id)).1 tendsto_id U hx).2 f

theorem continuousOn_valR {U : X.Opens} (f : Γ(X, U)) :
    ContinuousOn (fun y : Sp C ⟶ X => valR y U f) {y | ⊤ ≤ y ⁻¹ᵁ U} :=
  fun _ hx => (continuousAt_valR f hx).continuousWithinAt

theorem continuous_valR_top (f : Γ(X, ⊤)) : Continuous fun y : Sp C ⟶ X => valR y ⊤ f :=
  continuous_iff_continuousAt.2 fun _ => continuousAt_valR f le_top

theorem continuous_iff {B : Type*} [TopologicalSpace B] {e : B → (Sp C ⟶ X)} :
    Continuous e ↔ ∀ U : X.Opens, IsOpen {b | ⊤ ≤ e b ⁻¹ᵁ U} ∧
      ∀ f : Γ(X, U), ContinuousOn (fun b => valR (e b) U f) {b | ⊤ ≤ e b ⁻¹ᵁ U} := by
  constructor
  · intro H U
    exact ⟨(isOpen_setOf_le_preimage U).preimage H,
      fun f => (continuousOn_valR f).comp H.continuousOn fun _ hb => hb⟩
  · intro H
    refine continuous_iff_continuousAt.2 fun b => tendsto_iff.2 fun U hU => ?_
    have h := (H U).1.mem_nhds hU
    exact ⟨h, fun f => ((H U).2 f).continuousAt h⟩

@[fun_prop] theorem continuous_comp (g : X ⟶ Y) : Continuous fun x : Sp C ⟶ X => x ≫ g := by
  refine continuous_iff.2 fun U => ⟨isOpen_setOf_le_preimage (g ⁻¹ᵁ U), fun f => ?_⟩
  simp only [valR_comp]
  exact continuousOn_valR _

theorem PtsOver.continuous_map {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (g : X ⟶ Y) (hg : g ≫ q = p)
    (s : Sp C ⟶ S) : Continuous (PtsOver.map g hg s) :=
  ((continuous_comp g).comp continuous_subtype_val).subtype_mk _

def isoHomeomorph (g : X ≅ Y) : (Sp C ⟶ X) ≃ₜ (Sp C ⟶ Y) where
  toFun x := x ≫ g.hom
  invFun y := y ≫ g.inv
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := continuous_comp _
  continuous_invFun := continuous_comp _

@[simp] theorem isoHomeomorph_apply (g : X ≅ Y) (x : Sp C ⟶ X) : isoHomeomorph g x = x ≫ g.hom := rfl

theorem isInducing_of_tendsto {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hf : Continuous f) (H : ∀ (x : α) (l : Filter α), Tendsto f l (𝓝 (f x)) → Tendsto id l (𝓝 x)) :
    IsInducing f :=
  isInducing_iff_nhds.2 fun x =>
    le_antisymm hf.continuousAt.le_comap (tendsto_id'.1 (H x _ tendsto_comap))

theorem PtsOver.isEmbedding_map {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (g : X ⟶ Y) (hg : g ≫ q = p)
    (s : Sp C ⟶ S) (H : IsEmbedding fun x : Sp C ⟶ X => x ≫ g) : IsEmbedding (PtsOver.map g hg s) :=
  IsEmbedding.of_comp (PtsOver.continuous_map g hg s) continuous_subtype_val
    (H.comp IsEmbedding.subtypeVal)

omit [TopologicalSpace C] in

theorem PtsOver.range_map {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (g : X ⟶ Y) (hg : g ≫ q = p)
    (s : Sp C ⟶ S) : Set.range (PtsOver.map g hg s) =
      Subtype.val ⁻¹' Set.range fun x : Sp C ⟶ X => x ≫ g := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  · rintro ⟨x, hx⟩
    have hx' : x ≫ g = y.1 := hx
    exact ⟨⟨x, by rw [← hg, ← Category.assoc, hx', y.2]⟩, Subtype.ext hx'⟩

omit [TopologicalSpace C] in

theorem range_comp_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j] :
    Set.range (fun x : Sp C ⟶ X => x ≫ j) = {y | ⊤ ≤ y ⁻¹ᵁ j.opensRange} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ z _
    exact ⟨x z, rfl⟩
  · intro hy
    exact ⟨IsOpenImmersion.lift j y (by rintro _ ⟨z, rfl⟩; exact hy (x := z) trivial),
      IsOpenImmersion.lift_fac _ _ _⟩

theorem isOpenEmbedding_comp (j : X ⟶ Y) [IsOpenImmersion j] :
    IsOpenEmbedding fun x : Sp C ⟶ X => x ≫ j := by
  refine ⟨⟨isInducing_of_tendsto (continuous_comp j) fun x l H => tendsto_iff.2 fun U hU => ?_,
    fun x y h => (cancel_mono j).1 h⟩, ?_⟩
  · have hle : U ≤ j ⁻¹ᵁ j ''ᵁ U := (j.preimage_image_eq U).ge
    obtain ⟨h1, h2⟩ := tendsto_iff.1 H (j ''ᵁ U) (le_preimage_comp x j hle hU)
    have h3 : ∀ᶠ y in l, ⊤ ≤ y ⁻¹ᵁ U := by
      filter_upwards [h1] with y hy using le_preimage_mono y (j.preimage_image_eq U).le hy
    refine ⟨h3, fun f => ?_⟩
    have key : ∀ y : Sp C ⟶ X, ⊤ ≤ y ⁻¹ᵁ U →
        valR (y ≫ j) (j ''ᵁ U) ((j.appIso U).inv.hom f) = valR y U f := by
      intro y hy
      rw [← valR_appLE y j hle hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
      exact valR_res y le_rfl hy f
    have h4 := h2 ((j.appIso U).inv.hom f)
    rw [key x hU] at h4
    refine h4.congr' ?_
    filter_upwards [h3] with y hy using key y hy
  · rw [range_comp_of_isOpenImmersion]
    exact isOpen_setOf_le_preimage _

theorem PtsOver.isOpenEmbedding_map {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (j : X ⟶ Y)
    [IsOpenImmersion j] (hj : j ≫ q = p) (s : Sp C ⟶ S) : IsOpenEmbedding (PtsOver.map j hj s) :=
  ⟨PtsOver.isEmbedding_map j hj s (isOpenEmbedding_comp j).isEmbedding, by
    rw [PtsOver.range_map]
    exact (isOpenEmbedding_comp j).isOpen_range.preimage continuous_subtype_val⟩

end Top

section Local

open CommRingCat.HomTopology

variable {C : Type} [CommRing C] [TopologicalSpace C] {X Y : Scheme.{0}}

theorem continuousAt_inverse_of_isUnit [IsOpenUnits C] {u : C} (hu : IsUnit u) :
    ContinuousAt Ring.inverse u := by
  obtain ⟨u, rfl⟩ := hu
  rw [← (IsOpenUnits.isOpenEmbedding_unitsVal (M := C)).continuousAt_iff]
  have : Ring.inverse ∘ (Units.val : Cˣ → C) = fun v : Cˣ => ((v⁻¹ : Cˣ) : C) :=
    funext fun v => Ring.inverse_unit v
  rw [this]
  exact Units.continuous_coe_inv.continuousAt

variable [IsTopologicalRing C]

theorem tendsto_valR_of_closure {B : Type*} {e : B → (Sp C ⟶ X)} {l : Filter B} {x : Sp C ⟶ X}
    {U : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ U) (hl : ∀ᶠ b in l, ⊤ ≤ e b ⁻¹ᵁ U) {s : Set Γ(X, U)}
    (H : ∀ f ∈ s, Tendsto (fun b => valR (e b) U f) l (𝓝 (valR x U f))) {f : Γ(X, U)}
    (hf : f ∈ Subring.closure s) : Tendsto (fun b => valR (e b) U f) l (𝓝 (valR x U f)) := by
  induction hf using Subring.closure_induction with
  | mem f hf => exact H f hf
  | zero =>
    rw [valR_zero x U hx]
    exact tendsto_const_nhds.congr' (hl.mono fun b hb => (valR_zero _ U hb).symm)
  | one =>
    rw [valR_one x U hx]
    exact tendsto_const_nhds.congr' (hl.mono fun b hb => (valR_one _ U hb).symm)
  | add f g _ _ hf hg =>
    rw [valR_add x U hx]
    exact (hf.add hg).congr' (hl.mono fun b hb => (valR_add _ U hb f g).symm)
  | neg f _ hf =>
    rw [valR_neg x U hx]
    exact hf.neg.congr' (hl.mono fun b hb => (valR_neg _ U hb f).symm)
  | mul f g _ _ hf hg =>
    rw [valR_mul x U hx]
    exact (hf.mul hg).congr' (hl.mono fun b hb => (valR_mul _ U hb f g).symm)

variable [IsLocalRing C] [IsOpenUnits C]

theorem tendsto_of_isAffineOpen {B : Type*} {e : B → (Sp C ⟶ X)} {l : Filter B} {x : Sp C ⟶ X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hl : ∀ᶠ b in l, ⊤ ≤ e b ⁻¹ᵁ U)
    (H : ∀ f : Γ(X, U), Tendsto (fun b => valR (e b) U f) l (𝓝 (valR x U f))) : Tendsto e l (𝓝 x) := by
  refine tendsto_iff.2 fun V hV => ?_
  obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le (V := V) ⟨_, (le_preimage_iff x V).1 hV⟩
    ((le_preimage_iff x U).1 hx)
  have hxg' : ⊤ ≤ x ⁻¹ᵁ X.basicOpen g := (le_preimage_iff x _).2 hxg
  have hu : IsUnit (valR x U g) := (le_preimage_basicOpen_iff x hx g).1 hxg'
  have hopen : IsOpen {c : C | IsUnit c} := (IsOpenUnits.isOpenEmbedding_unitsVal (M := C)).isOpen_range
  have hl' : ∀ᶠ b in l, ⊤ ≤ e b ⁻¹ᵁ X.basicOpen g := by
    filter_upwards [hl, (H g).eventually (hopen.mem_nhds hu)] with b h1 h2
      using (le_preimage_basicOpen_iff _ h1 g).2 h2
  refine ⟨hl'.mono fun b hb => le_preimage_mono _ hgV hb, fun f => ?_⟩
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g ((X.presheaf.map (homOfLE hgV).op).hom f)
  have key : ∀ y : Sp C ⟶ X, ⊤ ≤ y ⁻¹ᵁ X.basicOpen g →
      valR y V f = valR y U a * Ring.inverse (valR y U g) ^ n := by
    intro y hy
    have hyU := le_preimage_mono y (X.basicOpen_le g) hy
    have hyu : IsUnit (valR y U g) := (le_preimage_basicOpen_iff y hyU g).1 hy
    have h1 := congrArg (valR y (X.basicOpen g)) ha
    rw [valR_mul y _ hy, valR_pow y _ hy, valR_res y hgV hy] at h1
    have h2 : ∀ t : Γ(X, U), valR y (X.basicOpen g) (algebraMap Γ(X, U) Γ(X, X.basicOpen g) t) =
        valR y U t := fun t => valR_res y (X.basicOpen_le g) hy t
    rw [h2, h2] at h1
    rw [← h1, mul_assoc, ← mul_pow, Ring.mul_inverse_cancel _ hyu, one_pow, mul_one]
  rw [key x hxg']
  refine ((H a).mul (((continuousAt_inverse_of_isUnit hu).tendsto.comp (H g)).pow n)).congr' ?_
  filter_upwards [hl'] with b hb using (key _ hb).symm

theorem tendsto_iff_of_generators {B : Type*} {e : B → (Sp C ⟶ X)} {l : Filter B} {x : Sp C ⟶ X}
    {U : X.Opens} (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) {s : Set Γ(X, U)} (hs : Subring.closure s = ⊤) :
    Tendsto e l (𝓝 x) ↔ (∀ᶠ b in l, ⊤ ≤ e b ⁻¹ᵁ U) ∧
      ∀ f ∈ s, Tendsto (fun b => valR (e b) U f) l (𝓝 (valR x U f)) :=
  ⟨fun H => ⟨(tendsto_iff.1 H U hx).1, fun f _ => (tendsto_iff.1 H U hx).2 f⟩,
    fun H => tendsto_of_isAffineOpen hU hx H.1 fun f =>
      tendsto_valR_of_closure hx H.1 H.2 (hs ▸ Subring.mem_top f)⟩

theorem PtsOver.tendsto_iff_of_generators {R : Type} [CommRing R] {p : X ⟶ Sp R} {t : Sp C ⟶ Sp R}
    {B : Type*} {e : B → PtsOver p t} {l : Filter B} {x : PtsOver p t} {U : X.Opens}
    (hU : IsAffineOpen U) (hx : ⊤ ≤ x.1 ⁻¹ᵁ U) {s : Set Γ(X, U)}
    (hs : Subring.closure (Set.range (constFn p U) ∪ s) = ⊤) :
    Tendsto e l (𝓝 x) ↔ (∀ᶠ b in l, ⊤ ≤ (e b).1 ⁻¹ᵁ U) ∧
      ∀ f ∈ s, Tendsto (fun b => valR (e b).1 U f) l (𝓝 (valR x.1 U f)) := by
  rw [tendsto_subtype_rng, Points.tendsto_iff_of_generators hU hx hs]
  refine and_congr_right fun hl => ⟨fun H f hf => H f (Or.inr hf), fun H f hf => ?_⟩
  rcases hf with ⟨a, rfl⟩ | hf
  · rw [valR_constFn p x.1 U hx, x.2]
    refine tendsto_const_nhds.congr' (hl.mono fun b hb => ?_)
    exact ((valR_constFn p (e b).1 U hb a).trans (by rw [(e b).2])).symm
  · exact H f hf

theorem continuous_iff_of_generators {B : Type*} [TopologicalSpace B] {e : B → (Sp C ⟶ X)} {ι : Sort*}
    {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcov : iSup U = ⊤) {s : ∀ i, Set Γ(X, U i)}
    (hs : ∀ i, Subring.closure (s i) = ⊤) :
    Continuous e ↔ ∀ i, IsOpen {b | ⊤ ≤ e b ⁻¹ᵁ U i} ∧
      ∀ f ∈ s i, ContinuousOn (fun b => valR (e b) (U i) f) {b | ⊤ ≤ e b ⁻¹ᵁ U i} := by
  refine ⟨fun H i => ⟨(continuous_iff.1 H _).1, fun f _ => (continuous_iff.1 H _).2 f⟩, fun H => ?_⟩
  refine continuous_iff_continuousAt.2 fun b => ?_
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top (e b) hcov
  have h := (H i).1.mem_nhds hi
  exact (tendsto_iff_of_generators (hU i) hi (hs i)).2 ⟨h, fun f hf => ((H i).2 f hf).continuousAt h⟩

theorem PtsOver.continuous_iff_of_generators {R : Type} [CommRing R] {p : X ⟶ Sp R} {t : Sp C ⟶ Sp R}
    {B : Type*} [TopologicalSpace B] {e : B → PtsOver p t} {ι : Sort*}
    {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcov : iSup U = ⊤) {s : ∀ i, Set Γ(X, U i)}
    (hs : ∀ i, Subring.closure (Set.range (constFn p (U i)) ∪ s i) = ⊤) :
    Continuous e ↔ ∀ i, IsOpen {b | ⊤ ≤ (e b).1 ⁻¹ᵁ U i} ∧
      ∀ f ∈ s i, ContinuousOn (fun b => valR (e b).1 (U i) f) {b | ⊤ ≤ (e b).1 ⁻¹ᵁ U i} := by
  refine ⟨fun H i => ?_, fun H => ?_⟩
  · have H' := continuous_iff.1 (continuous_subtype_val.comp H) (U i)
    exact ⟨H'.1, fun f _ => H'.2 f⟩
  refine continuous_iff_continuousAt.2 fun b => ?_
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top (e b).1 hcov
  have h := (H i).1.mem_nhds hi
  exact (PtsOver.tendsto_iff_of_generators (hU i) hi (hs i)).2
    ⟨h, fun f hf => ((H i).2 f hf).continuousAt h⟩

theorem continuous_specMap (A : CommRingCat.{0}) :
    Continuous fun φ : A ⟶ CommRingCat.of C => (Spec.map φ : Sp C ⟶ Spec A) := by
  refine continuous_iff_continuousAt.2 fun φ => tendsto_of_isAffineOpen (isAffineOpen_top _)
    (le_preimage_top _) (Eventually.of_forall fun _ => le_preimage_top _) fun f => ?_
  obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso A).inv.hom a = f :=
    ⟨(Scheme.ΓSpecIso A).hom.hom f, by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl⟩
  simp only [valR_specMap]
  exact (CommRingCat.HomTopology.continuous_apply a).continuousAt

def specHomeomorph (C : Type) [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C]
    [IsOpenUnits C] (A : CommRingCat.{0}) : (Sp C ⟶ Spec A) ≃ₜ (A ⟶ CommRingCat.of C) where
  toFun := Spec.preimage
  invFun := Spec.map
  left_inv := Spec.map_preimage
  right_inv := Spec.preimage_map
  continuous_toFun := by
    refine continuous_induced_rng.2 (continuous_pi fun a => ?_)
    exact (continuous_valR_top (C := C) _).congr fun x => (preimage_apply x a).symm
  continuous_invFun := continuous_specMap A

@[simp] theorem specHomeomorph_apply (A : CommRingCat.{0}) (x : Sp C ⟶ Spec A) :
    specHomeomorph C A x = Spec.preimage x := rfl

@[simp] theorem specHomeomorph_symm_apply (A : CommRingCat.{0}) (φ : A ⟶ CommRingCat.of C) :
    (specHomeomorph C A).symm φ = Spec.map φ := rfl

def affineHomeomorph {U : X.Opens} (hU : IsAffineOpen U) :
    {x : Sp C ⟶ X // ⊤ ≤ x ⁻¹ᵁ U} ≃ₜ (Γ(X, U) ⟶ CommRingCat.of C) where
  toFun x := valMap x.1 U x.2
  invFun φ := ⟨Spec.map φ ≫ hU.fromSpec, le_preimage_specMap_fromSpec hU φ⟩
  left_inv x := Subtype.ext (specMap_valMap_fromSpec hU x.1 x.2)
  right_inv φ := valMap_specMap_fromSpec hU φ _
  continuous_toFun := by
    refine continuous_induced_rng.2 (continuous_pi fun f => ?_)
    exact (continuousOn_iff_continuous_restrict.1 (continuousOn_valR (C := C) f)).congr
      fun x => valR_eq x.1 U x.2 f
  continuous_invFun := ((continuous_comp _).comp (continuous_specMap _)).subtype_mk _

@[simp] theorem affineHomeomorph_apply {U : X.Opens} (hU : IsAffineOpen U) (x : {x : Sp C ⟶ X // ⊤ ≤ x ⁻¹ᵁ U}) :
    affineHomeomorph hU x = valMap x.1 U x.2 := rfl

@[simp] theorem affineHomeomorph_symm_val {U : X.Opens} (hU : IsAffineOpen U)
    (φ : Γ(X, U) ⟶ CommRingCat.of C) : ((affineHomeomorph hU).symm φ).1 = Spec.map φ ≫ hU.fromSpec := rfl

theorem continuous_spMap_comp {C₀ : Type} [CommRing C₀] [TopologicalSpace C₀] [IsLocalRing C₀]
    (σ : C₀ →+* C) (hσ : Continuous σ) : Continuous fun x : Sp C₀ ⟶ X => spMap σ ≫ x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_le x (le_preimage_top x)
  have hl : ∀ᶠ y : Sp C₀ ⟶ X in 𝓝 x, ⊤ ≤ y ⁻¹ᵁ U := (isOpen_setOf_le_preimage U).mem_nhds hx
  refine tendsto_of_isAffineOpen hU (le_preimage_comp _ x hx (le_preimage_top _))
    (hl.mono fun y hy => le_preimage_comp _ y hy (le_preimage_top _)) fun f => ?_
  rw [valR_spMap_comp σ x U hx]
  exact (hσ.continuousAt.tendsto.comp (continuousAt_valR f hx)).congr'
    (hl.mono fun y hy => (valR_spMap_comp σ y U hy f).symm)

theorem isEmbedding_comp_of_isClosedImmersion (i : X ⟶ Y) [IsClosedImmersion i] :
    IsEmbedding fun x : Sp C ⟶ X => x ≫ i := by
  refine ⟨isInducing_of_tendsto (continuous_comp i) fun x l H => ?_, fun x y h => (cancel_mono i).1 h⟩
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_le (x ≫ i) (le_preimage_top _)
  obtain ⟨h1, h2⟩ := tendsto_iff.1 H V hx
  refine tendsto_of_isAffineOpen (hV.preimage i) hx h1 fun f => ?_
  obtain ⟨g, rfl⟩ := i.app_surjective V hV f
  have h3 := h2 g
  simp only [valR_comp] at h3
  exact h3

omit [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C] in

theorem mem_range_comp_iff_of_isClosedImmersion (i : X ⟶ Y) [IsClosedImmersion i] {V : Y.Opens}
    (hV : IsAffineOpen V) (y : Sp C ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ V) :
    y ∈ Set.range (fun x : Sp C ⟶ X => x ≫ i) ↔ ∀ f, (i.app V).hom f = 0 → valR y V f = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ f hf
    rw [valR_comp, hf]
    exact valR_zero x _ hy
  · intro H
    have hk : RingHom.ker (i.app V).hom ≤ RingHom.ker (valMap y V hy).hom := fun f hf => by
      rw [RingHom.mem_ker, ← valR_eq]
      exact H f hf
    let ψ : Γ(X, i ⁻¹ᵁ V) →+* C := (i.app V).hom.liftOfSurjective (i.app_surjective V hV)
      ⟨(valMap y V hy).hom, hk⟩
    have hψ : i.appLE V (i ⁻¹ᵁ V) le_rfl ≫ CommRingCat.ofHom ψ = valMap y V hy := by
      rw [Scheme.Hom.appLE_eq_app]
      ext f
      exact RingHom.liftOfSurjective_comp_apply (i.app V).hom (i.app_surjective V hV)
        ⟨(valMap y V hy).hom, hk⟩ f
    refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ (hV.preimage i).fromSpec, ?_⟩
    show (Spec.map (CommRingCat.ofHom ψ) ≫ (hV.preimage i).fromSpec) ≫ i = y
    rw [Category.assoc, ← hV.SpecMap_appLE_fromSpec i (hV.preimage i) le_rfl, ← Category.assoc,
      ← Spec.map_comp, hψ, specMap_valMap_fromSpec]

theorem isClosedEmbedding_comp [T1Space C] (i : X ⟶ Y) [IsClosedImmersion i] :
    IsClosedEmbedding fun x : Sp C ⟶ X => x ≫ i := by
  refine ⟨isEmbedding_comp_of_isClosedImmersion i, ?_⟩
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_le y (le_preimage_top _)
  have hy' := mt (mem_range_comp_iff_of_isClosedImmersion i hV y hyV).2 hy
  push Not at hy'
  obtain ⟨f, hf, hne⟩ := hy'
  filter_upwards [(isOpen_basicSet V f (isOpen_compl_singleton (x := (0 : C)))).mem_nhds ⟨hyV, hne⟩]
    with z hz hz' using hz.2 ((mem_range_comp_iff_of_isClosedImmersion i hV z hz.1).1 hz' f hf)

theorem isEmbedding_comp (i : X ⟶ Y) [IsImmersion i] : IsEmbedding fun x : Sp C ⟶ X => x ≫ i := by
  have h := (isOpenEmbedding_comp (C := C) i.coborderRange.ι).isEmbedding.comp
    (isEmbedding_comp_of_isClosedImmersion i.liftCoborder)
  convert h using 1
  ext1 x
  simp only [Function.comp_apply, Category.assoc, Scheme.Hom.liftCoborder_ι]

theorem PtsOver.isClosedEmbedding_map [T1Space C] {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (i : X ⟶ Y)
    [IsClosedImmersion i] (hi : i ≫ q = p) (s : Sp C ⟶ S) : IsClosedEmbedding (PtsOver.map i hi s) :=
  ⟨PtsOver.isEmbedding_map i hi s (isClosedEmbedding_comp i).isEmbedding, by
    rw [PtsOver.range_map]
    exact (isClosedEmbedding_comp i).isClosed_range.preimage continuous_subtype_val⟩

theorem PtsOver.isEmbedding_map_of_isImmersion {S : Scheme.{0}} {p : X ⟶ S} {q : Y ⟶ S} (i : X ⟶ Y)
    [IsImmersion i] (hi : i ≫ q = p) (s : Sp C ⟶ S) : IsEmbedding (PtsOver.map i hi s) :=
  PtsOver.isEmbedding_map i hi s (isEmbedding_comp i)

theorem isEmbedding_of_isPullback {P S : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hP : IsPullback fst snd f g) : IsEmbedding fun z : Sp C ⟶ P => (z ≫ fst, z ≫ snd) := by
  refine ⟨isInducing_of_tendsto ((continuous_comp fst).prodMk (continuous_comp snd)) fun z l H => ?_,
    fun x y h => hP.hom_ext (congrArg Prod.fst h) (congrArg Prod.snd h)⟩
  have H1 : Tendsto (fun y : Sp C ⟶ P => y ≫ fst) l (𝓝 (z ≫ fst)) := H.fst_nhds
  have H2 : Tendsto (fun y : Sp C ⟶ P => y ≫ snd) l (𝓝 (z ≫ snd)) := H.snd_nhds
  have w : ∀ y : Sp C ⟶ P, (y ≫ fst) ≫ f = (y ≫ snd) ≫ g := fun y => by
    rw [Category.assoc, Category.assoc, hP.w]
  obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_le ((z ≫ fst) ≫ f) (le_preimage_top _)
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_le (z ≫ fst) (V := f ⁻¹ᵁ W) hzW
  obtain ⟨V, hV, hzV, hVW⟩ := exists_isAffineOpen_le (z ≫ snd) (V := g ⁻¹ᵁ W) (by
    rw [w] at hzW
    exact hzW)
  let a := f.appLE W U hUW
  let b := g.appLE W V hVW
  let t : Spec (pushout a b) ⟶ P := hP.lift (Spec.map (pushout.inl a b) ≫ hU.fromSpec)
    (Spec.map (pushout.inr a b) ≫ hV.fromSpec) (by
      rw [Category.assoc, Category.assoc, ← hW.SpecMap_appLE_fromSpec f hU hUW,
        ← hW.SpecMap_appLE_fromSpec g hV hVW, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp, pushout.condition])
  have hcond : ∀ (y : Sp C ⟶ P) (h1 : ⊤ ≤ (y ≫ fst) ⁻¹ᵁ U) (h2 : ⊤ ≤ (y ≫ snd) ⁻¹ᵁ V),
      a ≫ valMap _ U h1 = b ≫ valMap _ V h2 := by
    intro y h1 h2
    rw [appLE_valMap _ f hUW h1 (le_preimage_comp _ _ hUW h1),
      appLE_valMap _ g hVW h2 (le_preimage_comp _ _ hVW h2)]
    congr 1
    exact w y
  have hdesc : ∀ (y : Sp C ⟶ P) (h1 : ⊤ ≤ (y ≫ fst) ⁻¹ᵁ U) (h2 : ⊤ ≤ (y ≫ snd) ⁻¹ᵁ V),
      Spec.map (pushout.desc _ _ (hcond y h1 h2)) ≫ t = y := by
    intro y h1 h2
    refine hP.hom_ext ?_ ?_
    · rw [Category.assoc, hP.lift_fst, ← Category.assoc, ← Spec.map_comp, pushout.inl_desc,
        specMap_valMap_fromSpec]
    · rw [Category.assoc, hP.lift_snd, ← Category.assoc, ← Spec.map_comp, pushout.inr_desc,
        specMap_valMap_fromSpec]
  obtain ⟨e1, v1⟩ := tendsto_iff.1 H1 U hzU
  obtain ⟨e2, v2⟩ := tendsto_iff.1 H2 V hzV
  classical
  let ψ : (Sp C ⟶ P) → (pushout a b ⟶ CommRingCat.of C) := fun y =>
    if h : ⊤ ≤ (y ≫ fst) ⁻¹ᵁ U ∧ ⊤ ≤ (y ≫ snd) ⁻¹ᵁ V then pushout.desc _ _ (hcond y h.1 h.2)
    else pushout.desc _ _ (hcond z hzU hzV)
  have hψ : ∀ (y : Sp C ⟶ P) (h1 : ⊤ ≤ (y ≫ fst) ⁻¹ᵁ U) (h2 : ⊤ ≤ (y ≫ snd) ⁻¹ᵁ V),
      ψ y = pushout.desc _ _ (hcond y h1 h2) := fun y h1 h2 => dif_pos ⟨h1, h2⟩
  have hlim : Tendsto ψ l (𝓝 (ψ z)) := by
    rw [(isEmbedding_pushout (R := CommRingCat.of C) a b).tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ ?_
    · rw [(isEmbedding_hom _ _).tendsto_nhds_iff, tendsto_pi_nhds]
      intro u
      rw [hψ z hzU hzV, pushout.inl_desc, ← valR_eq]
      refine (v1 u).congr' ?_
      filter_upwards [e1, e2] with y h1 h2
      simp only [Function.comp_apply]
      rw [hψ y h1 h2, pushout.inl_desc, ← valR_eq]
    · rw [(isEmbedding_hom _ _).tendsto_nhds_iff, tendsto_pi_nhds]
      intro u
      rw [hψ z hzU hzV, pushout.inr_desc, ← valR_eq]
      refine (v2 u).congr' ?_
      filter_upwards [e1, e2] with y h1 h2
      simp only [Function.comp_apply]
      rw [hψ y h1 h2, pushout.inr_desc, ← valR_eq]
  have hfin := (((continuous_comp t).comp (continuous_specMap (C := C) _)).tendsto (ψ z)).comp hlim
  simp only [Function.comp_apply] at hfin
  rw [hψ z hzU hzV, hdesc] at hfin
  refine hfin.congr' ?_
  filter_upwards [e1, e2] with y h1 h2
  simp only [Function.comp_apply, id]
  rw [hψ y h1 h2, hdesc]

def pullbackHomeomorph {P S : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hP : IsPullback fst snd f g) :
    (Sp C ⟶ P) ≃ₜ {q : (Sp C ⟶ X) × (Sp C ⟶ Y) // q.1 ≫ f = q.2 ≫ g} where
  toFun z := ⟨(z ≫ fst, z ≫ snd), (Category.assoc z fst f).trans
    ((congrArg (z ≫ ·) hP.w).trans (Category.assoc z snd g).symm)⟩
  invFun q := hP.lift q.1.1 q.1.2 q.2
  left_inv z := hP.hom_ext (hP.lift_fst _ _ _) (hP.lift_snd _ _ _)
  right_inv q := Subtype.ext (Prod.ext (hP.lift_fst _ _ q.2) (hP.lift_snd _ _ q.2))
  continuous_toFun := (isEmbedding_of_isPullback (C := C) hP).continuous.subtype_mk _
  continuous_invFun := by
    refine (isEmbedding_of_isPullback (C := C) hP).continuous_iff.2 ?_
    exact continuous_subtype_val.congr fun q => (Prod.ext (hP.lift_fst _ _ q.2) (hP.lift_snd _ _ q.2)).symm

@[simp] theorem pullbackHomeomorph_val {P S : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hP : IsPullback fst snd f g) (z : Sp C ⟶ P) : (pullbackHomeomorph hP z).1 = (z ≫ fst, z ≫ snd) := rfl

def PtsOver.prodHomeomorph {P S : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (hP : IsPullback fst snd f g) (s : Sp C ⟶ S) : PtsOver (fst ≫ f) s ≃ₜ PtsOver f s × PtsOver g s where
  toFun z := (PtsOver.map fst rfl s z, PtsOver.map snd hP.w.symm s z)
  invFun q := ⟨hP.lift q.1.1 q.2.1 (q.1.2.trans q.2.2.symm), by
    rw [← Category.assoc, hP.lift_fst, q.1.2]⟩
  left_inv z := Subtype.ext (hP.hom_ext (hP.lift_fst _ _ _) (hP.lift_snd _ _ _))
  right_inv q := Prod.ext (Subtype.ext (hP.lift_fst _ _ _)) (Subtype.ext (hP.lift_snd _ _ _))
  continuous_toFun := (PtsOver.continuous_map _ _ _).prodMk (PtsOver.continuous_map _ _ _)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    rw [(isEmbedding_of_isPullback hP).continuous_iff]
    convert (continuous_subtype_val.prodMap continuous_subtype_val :
      Continuous (Prod.map Subtype.val Subtype.val : PtsOver f s × PtsOver g s → _)) using 1
    ext1 q
    exact Prod.ext (hP.lift_fst _ _ _) (hP.lift_snd _ _ _)

@[simp] theorem PtsOver.prodHomeomorph_apply {P S : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (hP : IsPullback fst snd f g) (s : Sp C ⟶ S) (z : PtsOver (fst ≫ f) s) :
    PtsOver.prodHomeomorph hP s z = (PtsOver.map fst rfl s z, PtsOver.map snd hP.w.symm s z) := rfl

end Local

section Algebra

variable {R C : Type} [CommRing R] [CommRing C] [Algebra R C] (A : Type) [CommRing A] [Algebra R A]

def ptsOverEquivAlgHom {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) :
    PtsOver (spMap (algebraMap R A)) t ≃ (A →ₐ[R] C) where
  toFun x := { (Spec.preimage x.1).hom with
    commutes' := fun r => by
      have h : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage x.1 =
          CommRingCat.ofHom (algebraMap R C) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact x.2.trans ht
      exact congrArg (fun φ => φ.hom r) h }
  invFun φ := ⟨spMap φ.toRingHom, by
    rw [ht, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap⟩
  left_inv x := Subtype.ext (Spec.map_preimage x.1)
  right_inv φ := by
    ext a
    show (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom a = φ a
    rw [Spec.preimage_map]
    rfl

theorem ptsOverEquivAlgHom_apply {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C))
    (x : PtsOver (spMap (algebraMap R A)) t) (a : A) :
    ptsOverEquivAlgHom A ht x a = valR x.1 ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
  preimage_apply (A := CommRingCat.of A) x.1 a

@[simp] theorem ptsOverEquivAlgHom_symm_val {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C))
    (φ : A →ₐ[R] C) : ((ptsOverEquivAlgHom A ht).symm φ).1 = spMap φ.toRingHom := rfl

theorem id_eq_spMap_algebraMap (C : Type) [CommRing C] : 𝟙 (Sp C) = spMap (algebraMap C C) :=
  (Spec.map_id _).symm

abbrev ptsEquivAlgHom {C : Type} [CommRing C] (A : Type) [CommRing A] [Algebra C A] :
    Pts (spMap (algebraMap C A)) ≃ (A →ₐ[C] C) :=
  ptsOverEquivAlgHom A (id_eq_spMap_algebraMap C)

variable {A} in

theorem range_coord {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) {σ : Type*} (a : σ → A)
    (ha : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    Set.range (fun (x : PtsOver (spMap (algebraMap R A)) t) (i : σ) => ptsOverEquivAlgHom A ht x (a i)) =
      {z : σ → C | ∀ q : MvPolynomial σ R, MvPolynomial.aeval a q = 0 → MvPolynomial.aeval z q = 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ q hq
    rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply, hq, map_zero]
  · intro hz
    refine ⟨(ptsOverEquivAlgHom A ht).symm
      (AlgHom.liftOfSurjective _ ha (MvPolynomial.aeval z) fun q hq => hz q hq), funext fun i => ?_⟩
    have h := AlgHom.liftOfSurjective_apply _ ha (MvPolynomial.aeval z) (fun q hq => hz q hq)
      (MvPolynomial.X i)
    simpa using h

variable [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]

open CommRingCat.HomTopology in

theorem isEmbedding_ptsOverEquivAlgHom {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) :
    IsEmbedding fun x : PtsOver (spMap (algebraMap R A)) t => (ptsOverEquivAlgHom A ht x : A → C) :=
  ((CommRingCat.HomTopology.isEmbedding_hom (CommRingCat.of C) (CommRingCat.of A)).comp
    (specHomeomorph C (CommRingCat.of A)).isEmbedding).comp IsEmbedding.subtypeVal

variable {A} in

theorem isEmbedding_coord {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) {σ : Type*} (a : σ → A)
    (ha : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    IsEmbedding fun (x : PtsOver (spMap (algebraMap R A)) t) (i : σ) => ptsOverEquivAlgHom A ht x (a i) := by
  have h := isEmbedding_ptsOverEquivAlgHom A ht
  choose q hq using ha
  refine IsEmbedding.of_comp (g := fun (z : σ → C) (u : A) => MvPolynomial.aeval z (q u))
    (continuous_pi fun i => (continuous_apply (a i)).comp h.continuous) (continuous_pi fun u => ?_) ?_
  · simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    fun_prop
  · convert h using 1
    ext x u
    simp only [Function.comp_apply]
    rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply, hq]

variable {A} in

theorem isClosedEmbedding_coord [T1Space C] {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) {σ : Type*}
    (a : σ → A) (ha : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    IsClosedEmbedding
      fun (x : PtsOver (spMap (algebraMap R A)) t) (i : σ) => ptsOverEquivAlgHom A ht x (a i) := by
  refine ⟨isEmbedding_coord ht a ha, ?_⟩
  rw [range_coord ht a ha, Set.setOf_forall]
  refine isClosed_iInter fun q => ?_
  rw [Set.setOf_forall]
  refine isClosed_iInter fun _ => ?_
  have : Continuous fun z : σ → C => MvPolynomial.aeval z q := by
    simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    fun_prop
  exact isClosed_singleton.preimage this

omit [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C] in

theorem aeval_mk_X {σ : Type} (I : Ideal (MvPolynomial σ R)) (q : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) q = Ideal.Quotient.mk I q := by
  have : MvPolynomial.aeval (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) = Ideal.Quotient.mkₐ R I := by
    ext i
    simp
  rw [this]
  rfl

def zeroSetHomeomorph {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) {σ : Type}
    (I : Ideal (MvPolynomial σ R)) :
    PtsOver (spMap (algebraMap R (MvPolynomial σ R ⧸ I))) t ≃ₜ
      {z : σ → C | ∀ q ∈ I, MvPolynomial.aeval z q = 0} :=
  have ha : Function.Surjective
      (MvPolynomial.aeval (R := R) fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) := fun u => by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨q, aeval_mk_X I q⟩
  (isEmbedding_coord ht _ ha).toHomeomorph.trans (Homeomorph.setCongr (by
    rw [range_coord ht _ ha]
    simp only [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem]))

theorem zeroSetHomeomorph_apply {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) {σ : Type}
    (I : Ideal (MvPolynomial σ R)) (x : PtsOver (spMap (algebraMap R (MvPolynomial σ R ⧸ I))) t) (i : σ) :
    (zeroSetHomeomorph ht I x : σ → C) i =
      ptsOverEquivAlgHom _ ht x (Ideal.Quotient.mk I (MvPolynomial.X i)) := rfl

def zeroLocusHomeomorph {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T1Space F]
    {σ : Type} (I : Ideal (MvPolynomial σ F)) :
    Pts (spMap (algebraMap F (MvPolynomial σ F ⧸ I))) ≃ₜ MvPolynomial.zeroLocus F I :=
  zeroSetHomeomorph (id_eq_spMap_algebraMap F) I

def affineSpaceHomeomorph {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) (σ : Type) :
    PtsOver (spMap (algebraMap R (MvPolynomial σ R))) t ≃ₜ (σ → C) :=
  have ha : Function.Surjective (MvPolynomial.aeval (R := R) (MvPolynomial.X : σ → MvPolynomial σ R)) :=
    fun q => ⟨q, MvPolynomial.aeval_X_left_apply q⟩
  (isEmbedding_coord ht _ ha).toHomeomorphOfSurjective (by
    rw [← Set.range_eq_univ, range_coord ht _ ha, Set.eq_univ_iff_forall]
    intro z q hq
    rw [MvPolynomial.aeval_X_left_apply] at hq
    rw [hq, map_zero])

theorem affineSpaceHomeomorph_apply {t : Sp C ⟶ Sp R} (ht : t = spMap (algebraMap R C)) (σ : Type)
    (x : PtsOver (spMap (algebraMap R (MvPolynomial σ R))) t) (i : σ) :
    affineSpaceHomeomorph ht σ x i = ptsOverEquivAlgHom _ ht x (MvPolynomial.X i) := rfl

end Algebra

section OverCat

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type} [CommRing C] [TopologicalSpace C]

omit [TopologicalSpace C] in

abbrev overPt {A : Over (Sp C)} (x : 𝟙_ (Over (Sp C)) ⟶ A) : Sp C ⟶ A.left := x.left

instance unitLeftTopology (X : Scheme.{0}) : TopologicalSpace ((𝟙_ (Over (Sp C))).left ⟶ X) :=
  topology C X

instance overTopology (A : Over (Sp C)) : TopologicalSpace (𝟙_ (Over (Sp C)) ⟶ A) :=
  induced overPt (topology C A.left)

theorem isEmbedding_left (A : Over (Sp C)) :
    IsEmbedding (overPt (A := A)) :=
  ⟨⟨rfl⟩, fun _ _ h => Over.OverMorphism.ext h⟩

def overHomeomorph (A : Over (Sp C)) : (𝟙_ (Over (Sp C)) ⟶ A) ≃ₜ Pts A.hom where
  toFun x := ⟨x.left, Over.w x⟩
  invFun x := Over.homMk x.1 x.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (isEmbedding_left A).continuous.subtype_mk _
  continuous_invFun := (isEmbedding_left A).continuous_iff.2 continuous_subtype_val

@[simp] theorem overHomeomorph_val (A : Over (Sp C)) (x : 𝟙_ (Over (Sp C)) ⟶ A) :
    (overHomeomorph A x).1 = x.left := rfl

@[fun_prop] theorem continuous_over_comp {A B : Over (Sp C)} (g : A ⟶ B) :
    Continuous fun x : 𝟙_ (Over (Sp C)) ⟶ A => x ≫ g :=
  (isEmbedding_left B).continuous_iff.2 ((continuous_comp g.left).comp (isEmbedding_left A).continuous)

def tensorHomeomorph [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C] (A B : Over (Sp C)) :
    (𝟙_ (Over (Sp C)) ⟶ A ⊗ B) ≃ₜ (𝟙_ (Over (Sp C)) ⟶ A) × (𝟙_ (Over (Sp C)) ⟶ B) where
  toFun z := (z ≫ fst A B, z ≫ snd A B)
  invFun q := lift q.1 q.2
  left_inv z := by ext1 <;> simp
  right_inv q := by simp
  continuous_toFun := (continuous_over_comp _).prodMk (continuous_over_comp _)
  continuous_invFun := by
    refine (isEmbedding_left _).continuous_iff.2 ?_
    refine (isEmbedding_of_isPullback (C := C) (IsPullback.of_hasPullback A.hom B.hom)).continuous_iff.2 ?_
    refine ((isEmbedding_left A).continuous.prodMap (isEmbedding_left B).continuous).congr fun q => ?_
    exact Prod.ext (congrArg (·.left) (lift_fst q.1 q.2)).symm (congrArg (·.left) (lift_snd q.1 q.2)).symm

@[simp] theorem tensorHomeomorph_apply [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]
    (A B : Over (Sp C)) (z : 𝟙_ (Over (Sp C)) ⟶ A ⊗ B) :
    tensorHomeomorph A B z = (z ≫ fst A B, z ≫ snd A B) := rfl

@[simp] theorem tensorHomeomorph_symm_apply [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]
    (A B : Over (Sp C)) (q : (𝟙_ (Over (Sp C)) ⟶ A) × (𝟙_ (Over (Sp C)) ⟶ B)) :
    (tensorHomeomorph A B).symm q = lift q.1 q.2 := rfl

end OverCat

section Complex

open ReciprocityTheory.AnForm.R

variable {X : Scheme.{0}}

theorem continuous_iff_valAt' {B : Type*} [TopologicalSpace B] {e : B → (Sp ℂ ⟶ X)} :
    Continuous e ↔ ∀ U : X.Opens, IsOpen {b | ⊤ ≤ e b ⁻¹ᵁ U} ∧
      ∀ f : Γ(X, U), ContinuousOn (fun b => valAt' (e b) U f) {b | ⊤ ≤ e b ⁻¹ᵁ U} :=
  continuous_iff

theorem continuous_of_differentiableOn {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {e : B → (Sp ℂ ⟶ X)} (H : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {b | ⊤ ≤ e b ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun b => valAt' (e b) U f) {b | ⊤ ≤ e b ⁻¹ᵁ U}) : Continuous e :=
  continuous_iff_valAt'.2 fun U => ⟨(H U 0).1, fun f => (H U f).2.continuousOn⟩

def conjHomeomorph (X : Scheme.{0}) : (Sp ℂ ⟶ X) ≃ₜ (Sp ℂ ⟶ X) :=
  have h : ∀ x : Sp ℂ ⟶ X, spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ x = x := fun x => by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext Complex.conj_conj
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  { toFun := fun x => spMap (starRingEnd ℂ) ≫ x
    invFun := fun x => spMap (starRingEnd ℂ) ≫ x
    left_inv := h
    right_inv := h
    continuous_toFun := continuous_spMap_comp _ Complex.continuous_conj
    continuous_invFun := continuous_spMap_comp _ Complex.continuous_conj }

@[simp] theorem conjHomeomorph_apply (x : Sp ℂ ⟶ X) : conjHomeomorph X x = spMap (starRingEnd ℂ) ≫ x := rfl

theorem valR_conjHomeomorph (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR (conjHomeomorph X x) U f = starRingEnd ℂ (valR x U f) := valR_spMap_comp _ x U h f

def PtsOver.conjHomeomorph {S : Scheme.{0}} (p : X ⟶ S) (s : Sp ℂ ⟶ S) :
    PtsOver p s ≃ₜ PtsOver p (spMap (starRingEnd ℂ) ≫ s) :=
  (Points.conjHomeomorph X).subtype fun x => by
    rw [conjHomeomorph_apply, Category.assoc]
    exact (Points.conjHomeomorph S).injective.eq_iff.symm

def ptsEquivCPt (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] : Pts p ≃ CPt X :=
  pointEquivClosedPoint p

theorem ptsEquivCPt_val (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (x : Pts p) :
    (ptsEquivCPt p x).1 = x.1 (IsLocalRing.closedPoint ℂ) := rfl

theorem ptsEquivCPt_mem_iff (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (x : Pts p) (U : X.Opens) :
    (ptsEquivCPt p x).1 ∈ U ↔ ⊤ ≤ x.1 ⁻¹ᵁ U := (le_preimage_iff x.1 U).symm

theorem germ_stalkClosedPointTo_eq_valMap {C : Type} [CommRing C] [IsLocalRing C] (x : Sp C ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    X.presheaf.germ U (x (IsLocalRing.closedPoint C)) ((le_preimage_iff x U).1 h) ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of C) x = valMap x U h := by
  rw [Scheme.germ_stalkClosedPointTo (R := CommRingCat.of C)]
  rfl

theorem valR_eq_val (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (x : Pts p) (U : X.Opens)
    (h : (ptsEquivCPt p x).1 ∈ U) (f : Γ(X, U)) : valR x.1 U f = val p f (ptsEquivCPt p x).1 h := by
  let ψ : X.residueField (x.1 (IsLocalRing.closedPoint ℂ)) ⟶ CommRingCat.of ℂ :=
    Scheme.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) x.1)
  have hψ : ∀ (V : X.Opens) (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V) (g : Γ(X, V)),
      ψ.hom ((X.evaluation V _ hV).hom g) = valR x.1 V g := by
    intro V hV g
    have hV' := (le_preimage_iff x.1 V).2 hV
    rw [valR_eq x.1 V hV', ← germ_stalkClosedPointTo_eq_valMap, ← CommRingCat.comp_apply,
      ← Scheme.germ_residue, Category.assoc, Scheme.residue_descResidueField]
  have hc : IsClosed ({x.1 (IsLocalRing.closedPoint ℂ)} : Set X) := (ptsEquivCPt p x).2
  have h1 := valHom_unique p _ hc ψ.hom (RingHom.ext fun c =>
    (hψ ⊤ trivial _).trans (valR_constFn_of_section p x.1 x.2 ⊤ (le_preimage_top _) c))
  have h2 := valHom_eq p _ hc
  rw [← h1] at h2
  rw [← hψ U h f]
  exact (congrFun h2 _).symm

theorem valAt_eq_val (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (x : Pts p) (U : X.Opens)
    (h : ⊤ ≤ x.1 ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt x.1 U h f = val p f (ptsEquivCPt p x).1 ((ptsEquivCPt_mem_iff p x U).2 h) :=
  (valAt_eq_valR x.1 U h f).trans (valR_eq_val p x U _ f)

def resolutionHomeomorph {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P} (w : WData P D hP) :
    Pts (w.π ≫ toSpecC hP) ≃ₜ w.M :=
  haveI := w.lft
  let e : Pts (w.π ≫ toSpecC hP) ≃ w.M := ptsEquivCPt (w.π ≫ toSpecC hP)
  have hmem : ∀ (c : w.Idx) (x : Pts (w.π ≫ toSpecC hP)),
      e x ∈ w.src c ↔ ⊤ ≤ x.1 ⁻¹ᵁ (w.pres c.1 c.2).V := fun c x => ptsEquivCPt_mem_iff _ x _
  have hval : ∀ (c : w.Idx) (x : Pts (w.π ≫ toSpecC hP)) (_ : e x ∈ w.src c) (q),
      MvPolynomial.eval (w.coord c (e x)) q = valR x.1 _ ((w.pres c.1 c.2).secHom q) :=
    fun c x hx q => (w.eval_coord_val c (e x) hx q).trans (valR_eq_val _ x _ hx _).symm
  { e with
    continuous_toFun := by
      refine continuous_generateFrom_iff.2 ?_
      rintro _ ⟨c, O, hO, rfl⟩
      have h1 : IsOpen (e ⁻¹' w.src c) := by
        rw [show e ⁻¹' w.src c = _ from Set.ext (hmem c)]
        exact (isOpen_setOf_le_preimage _).preimage continuous_subtype_val
      have h2 : ContinuousOn (fun x => w.coord c (e x)) (e ⁻¹' w.src c) := by
        refine continuousOn_pi.2 fun l => ?_
        refine (((continuousOn_valR ((w.pres c.1 c.2).secHom (MvPolynomial.X l))).comp
          continuous_subtype_val.continuousOn fun x hx => (hmem c x).1 hx)).congr fun x hx => ?_
        exact (MvPolynomial.eval_X l).symm.trans (hval c x hx _)
      exact h2.isOpen_inter_preimage h1 hO
    continuous_invFun := by
      refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun y => ?_)
      obtain ⟨c, hc⟩ := w.cover y
      have hm : ∀ z, z ∈ w.src c → e (e.symm z) ∈ w.src c := fun z hz => by rwa [e.apply_symm_apply]
      have hn := (w.isOpen_alt_bis c).mem_nhds hc
      refine tendsto_of_isAffineOpen (w.pres c.1 c.2).isAffineOpen_V' ((hmem c _).1 (hm y hc))
        (mem_of_superset hn fun z hz => (hmem c _).1 (hm z hz)) fun f => ?_
      obtain ⟨q, rfl⟩ := (w.pres c.1 c.2).secHom_surj f
      have h3 : ContinuousOn (fun z => MvPolynomial.eval (w.coord c z) q) (w.src c) :=
        (MvPolynomial.continuous_eval q).comp_continuousOn
          (continuousOn_iff_continuous_restrict.2 (w.isEmbedding c).continuous)
      have h4 : ContinuousOn (fun z => valR (e.symm z).1 _ ((w.pres c.1 c.2).secHom q)) (w.src c) :=
        h3.congr fun z hz => by rw [← hval c _ (hm z hz), e.apply_symm_apply]
      exact h4.continuousAt hn }

theorem resolutionHomeomorph_val {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P} (w : WData P D hP)
    (x : Pts (w.π ≫ toSpecC hP)) : (resolutionHomeomorph w x).1 = x.1 (IsLocalRing.closedPoint ℂ) := rfl

end Complex

example : Nonempty (Pts (spMap (algebraMap ℂ (MvPolynomial (Fin 2) ℂ))) ≃ₜ (Fin 2 → ℂ)) :=
  ⟨affineSpaceHomeomorph (id_eq_spMap_algebraMap ℂ) (Fin 2)⟩

example : Nonempty (PtsOver (spMap (algebraMap ℤ (MvPolynomial Unit ℤ))) (spMap (algebraMap ℤ ℚ_[2])) ≃ₜ
    (Unit → ℚ_[2])) :=
  ⟨affineSpaceHomeomorph rfl Unit⟩

example : let X := Pts (spMap (algebraMap ℂ (MvPolynomial Unit ℂ)))
    ConnectedSpace X ∧ T2Space X ∧ Nontrivial X := by
  let h := affineSpaceHomeomorph (id_eq_spMap_algebraMap ℂ) Unit
  exact ⟨h.symm.surjective.connectedSpace h.symm.continuous, h.isEmbedding.t2Space,
    h.toEquiv.nontrivial⟩

example : valAt' (spMap (MvPolynomial.eval fun _ : Unit => 2 + Complex.I)) ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial Unit ℂ))).inv.hom (MvPolynomial.X () ^ 2 + 1)) =
      4 + 4 * Complex.I := by
  rw [valAt'_eq_valR, valR_specMap (A := CommRingCat.of (MvPolynomial Unit ℂ))]
  simp only [CommRingCat.hom_ofHom, map_add, map_pow, MvPolynomial.eval_X, map_one]
  linear_combination Complex.I_mul_I

example : CompactSpace (Pts (spMap (algebraMap ℝ (MvPolynomial (Fin 2) ℝ ⧸
    Ideal.span {(MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℝ)})))) := by
  set I := Ideal.span {(MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℝ)}
  have hc : IsCompact {z : Fin 2 → ℝ | ∀ q ∈ I, MvPolynomial.aeval z q = 0} := by
    refine (isCompact_closedBall (0 : Fin 2 → ℝ) 1).of_isClosed_subset ?_ fun z hz => ?_
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun q => isClosed_iInter fun _ =>
        isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · have h := hz _ (Ideal.subset_span rfl)
      simp only [map_sub, map_add, map_pow, MvPolynomial.aeval_X, map_one] at h
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, abs_le]
      fin_cases i <;> constructor <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith
  have := isCompact_iff_compactSpace.1 hc
  exact (zeroSetHomeomorph (id_eq_spMap_algebraMap ℝ) I).symm.compactSpace

end GlobalTheory.Points
