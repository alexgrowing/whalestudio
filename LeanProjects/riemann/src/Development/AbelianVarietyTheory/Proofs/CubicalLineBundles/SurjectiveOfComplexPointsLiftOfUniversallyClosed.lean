import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe u

namespace GlobalTheory.ComplexPoints

section General

variable {K : Type u} [Field K] [IsAlgClosed K]

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

theorem _root_.GlobalTheory.ComplexPoints.exists_point_mem {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ ∧ ∀ a, x a ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨y, hyZ, hy⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed {y} := hy
  exact ⟨pointOfClosedPoint p y hy, pointOfClosedPoint_comp p y hy,
    fun a => by rw [pointOfClosedPoint_apply]; exact hyZ⟩

theorem exists_geomPoint_mem {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = t ∧ ∀ a, x a ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, hw⟩ := (pullback.fst p t).surjective z
  obtain ⟨y, hy, hyZ⟩ := exists_point_mem (pullback.snd p t)
    (hZ.preimage (pullback.fst p t).continuous) ⟨w, show pullback.fst p t w ∈ Z from hw ▸ hz⟩
  refine ⟨y ≫ pullback.fst p t, ?_, fun a => hyZ a⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hy]

theorem surjective_specMap_field {k L : Type u} [Field k] [Field L] (σ : k →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom σ)) :=
  ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

theorem _root_.GlobalTheory.ComplexPoints.top_le_preimage_iff {L : Type u} [Field L] {X : Scheme.{u}}
    (x : Spec (.of L) ⟶ X) (U : X.Opens) (a : ↥(Spec (.of L))) : ⊤ ≤ x ⁻¹ᵁ U ↔ x a ∈ U := by
  constructor
  · intro h
    exact h (show a ∈ (⊤ : (Spec (.of L)).Opens) from trivial)
  · intro h b _
    rw [Subsingleton.elim b a]
    exact h

theorem opens_le_of_geomPoints {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (U V : X.Opens)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro z hzU
  by_contra hzV
  obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem p t (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨z, hzU, hzV⟩
  let a : ↥(Spec (.of K)) := IsLocalRing.closedPoint K
  exact (hxZ a).2 ((top_le_preimage_iff x V a).1 (h x hx ((top_le_preimage_iff x U a).2 (hxZ a).1)))

theorem closed_eq_univ_of_geomPoints {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] {Z : Set X} (hZ : IsClosed Z)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = t → ∃ a, x a ∈ Z) : Z = Set.univ := by
  by_contra hne
  obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem p t hZ.isOpen_compl.isLocallyClosed
    (Set.nonempty_compl.mpr hne)
  obtain ⟨a, ha⟩ := h x hx
  exact hxZ a ha

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

theorem _root_.GlobalTheory.ComplexPoints.surjective_of_geomPoints_lift {A B S : Scheme.{u}} (p : A ⟶ S)
    [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Spec (.of K) ⟶ A, x ≫ p = t → ∃ y : Spec (.of K) ⟶ B, y ≫ ψ = x) :
    Surjective ψ := by
  constructor
  by_contra hns
  have hne : (Set.range ψ)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro hr
    exact hns (Set.range_eq_univ.mp hr)
  have hP : (pullback.fst p t ⁻¹' (Set.range ψ)ᶜ).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨z, hz⟩ := (pullback.fst p t).surjective a
    exact ⟨z, by simpa [hz] using ha⟩
  obtain ⟨y, hy1, hy2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd p t)
    (hψ.isOpen_compl.preimage (pullback.fst p t).continuous).isLocallyClosed hP
  obtain ⟨w, hw⟩ := h (y ≫ pullback.fst p t) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy1, Category.id_comp])
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of K)))
  apply hy2 a
  exact ⟨w a, by rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]⟩

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in

theorem _root_.GlobalTheory.ComplexPoints.hom_ext_of_points {X Y S : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [LocallyOfFiniteType p]
    [IsReduced X] (q : Y ⟶ S) [IsSeparated q] {f g : X ⟶ Y} (hfg : f ≫ q = g ≫ q)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  refine ext_of_fromSpecResidueField_eq f g q (closedPoints X)
    (dense_iff_closure_eq.mpr closure_closedPoints) ?_ hfg
  intro y hy
  have e := h (pointOfClosedPoint p y hy) (pointOfClosedPoint_comp p y hy)
  unfold pointOfClosedPoint at e
  simp only [Category.assoc] at e
  exact (cancel_epi _).mp e

end General

variable {X Y : Scheme.{0}}

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

theorem _root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt x U h f ≠ 0 := by
  have e : x ⁻¹ᵁ X.basicOpen f = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).basicOpen (x.appLE U ⊤ h f) := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  rw [e]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  constructor
  · intro hs h0
    have hz : x.appLE U ⊤ h f = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of ℂ)).inv.hom h0
      simpa using this
    rw [hz, Scheme.basicOpen_zero] at hs
    obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
    exact (hs (show a ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)).elim
  · intro hne
    have hu : IsUnit (x.appLE U ⊤ h f) := by
      have := (isUnit_iff_ne_zero.mpr hne).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
      simpa using this
    rw [Scheme.basicOpen_of_isUnit _ hu]

theorem isUnit_of_valAt_ne_zero (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f ≠ 0) : IsUnit f := by
  have hU : U ≤ X.basicOpen f := opens_le_of_geomPoints p (𝟙 _) U _ fun x hx hxU =>
    (top_le_preimage_basicOpen_iff x U hxU f).2 (h x hxU hx)
  exact X.toRingedSpace.isUnit_of_isUnit_germ U f fun y hy => (X.mem_basicOpen f y hy).1 (hU hy)

theorem eq_zero_of_valAt_eq_zero (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
    (f : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f = 0) : f = 0 := by
  refine eq_zero_of_basicOpen_eq_bot f (le_bot_iff.1 (opens_le_of_geomPoints p (𝟙 _) _ _ ?_))
  intro x hx hxf
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := fun a ha => X.basicOpen_le f (hxf ha)
  exact absurd (h x hxU hx) ((top_le_preimage_basicOpen_iff x U hxU f).1 hxf)

theorem eq_of_valAt_eq (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
    (f g : Γ(X, U))
    (h : ∀ (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U hx f = valAt x U hx g) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_valAt_eq_zero p U _ fun x hx hp => ?_
  have := h x hx hp
  unfold valAt at this ⊢
  rw [map_sub, map_sub, this, sub_self]

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
private theorem opens_le_of_forall_complex_section (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro y hyU
  by_contra hyV
  obtain ⟨x, hx1, hx2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (K := ℂ) p
    (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hyU, hyV⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x U a).mpr (hx2 a).1
  exact (hx2 a).2 ((_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x V a).mp (h x hx1 hU))

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

theorem _root_.GlobalTheory.ComplexPoints.eq_of_valAt'_eq (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    [IsReduced X] (U : X.Opens)
    (f g : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U g) :
    f = g := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  refine eq_bot_iff.mpr (opens_le_of_forall_complex_section p _ ⊥ fun x hx hb => ?_)
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hb.trans fun b hb' => X.basicOpen_le (f - g) hb'
  have hne := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU (f - g)).mp hb
  have he := h x hx hU
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at he
  rw [dif_pos hU, dif_pos hU] at he
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hne he
  rw [map_sub, map_sub, he, sub_self] at hne
  exact (hne rfl).elim

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

theorem _root_.GlobalTheory.ComplexPoints.isUnit_of_valAt'_ne_zero (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f ≠ 0) : IsUnit f := by
  have hle : U ≤ X.basicOpen f := opens_le_of_forall_complex_section p U _ fun x hx hU => by
    have := h x hx hU
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at this
    rw [dif_pos hU] at this
    exact (_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU f).mpr this
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map
    (X.presheaf.map (homOfLE hle).op).hom
  have hid : (homOfLE (X.basicOpen_le f)).op ≫ (homOfLE hle).op = 𝟙 (Opposite.op U) :=
    Subsingleton.elim _ _
  convert hu using 1
  erw [← CommRingCat.comp_apply, ← Functor.map_comp, hid, CategoryTheory.Functor.map_id,
    CommRingCat.id_apply]

theorem hom_ext_of_complexPoints (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (q : Y ⟶ Sp ℂ) [IsSeparated q] {f g : X ⟶ Y} (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g :=
  hom_ext_of_points p q (hf.trans hg.symm) h

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

theorem _root_.GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints {A B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)} [LocallyOfFiniteType A.hom]
    [IsReduced A.left] [IsSeparated B.hom] {f g : A ⟶ B}
    (h : ∀ x : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ A, x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine _root_.GlobalTheory.ComplexPoints.hom_ext_of_points (K := ℂ) A.hom B.hom
    (by rw [Over.w f, Over.w g]) fun x hx => ?_
  have := h (Over.homMk x (by simpa using hx))
  simpa using congrArg (fun k => k.left) this

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

theorem _root_.GlobalTheory.ComplexPoints.opens_le_of_complexPoints (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p] (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V :=
  opens_le_of_forall_complex_section p U V h

theorem opens_eq_top_of_complexPoints (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U) : U = ⊤ :=
  top_le_iff.1 (opens_le_of_complexPoints p ⊤ U fun x hx _ => h x hx)

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in

theorem _root_.GlobalTheory.ComplexPoints.iSup_eq_top_of_complexPoints (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    {I : Type*} (U : I → X.Opens) (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ i, ⊤ ≤ x ⁻¹ᵁ U i) :
    ⨆ i, U i = ⊤ := by
  refine eq_top_iff.mpr (opens_le_of_forall_complex_section p ⊤ _ fun x hx _ => ?_)
  obtain ⟨i, hi⟩ := h x hx
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  rw [_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x _ a] at hi ⊢
  exact (le_iSup U i) hi

theorem surjective_of_complexPoints_lift {k : Type} [Field k] (σ : k →+* ℂ) {A B : Scheme.{0}}
    (a : A ⟶ Sp k) [LocallyOfFiniteType a] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ :=
  haveI : Surjective (spMap σ) := surjective_specMap_field σ
  surjective_of_geomPoints_lift a (spMap σ) ψ hψ h

theorem surjective_of_complexPoints_lift_of_universallyClosed {k : Type} [Field k] (σ : k →+* ℂ)
    {A B : Scheme.{0}} (a : A ⟶ Sp k) [LocallyOfFiniteType a] [IsSeparated a] (b : B ⟶ Sp k)
    [UniversallyClosed b] (ψ : B ⟶ A) (hw : ψ ≫ a = b)
    (h : ∀ x : Sp ℂ ⟶ A, x ≫ a = spMap σ → ∃ y : Sp ℂ ⟶ B, y ≫ ψ = x) : Surjective ψ := by
  subst hw
  have : UniversallyClosed ψ := UniversallyClosed.of_comp_of_isSeparated ψ a
  exact surjective_of_complexPoints_lift σ a ψ ψ.isClosedMap.isClosed_range h

end GlobalTheory.ComplexPoints

namespace GlobalTheory

theorem eq_zero_and_isUnit_of_valAt :
    ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X] (U : X.Opens)
      (f : Γ(X, U)),
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f = 0) → f = 0) ∧
      ((∀ (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ → valAt x U h f ≠ 0) → IsUnit f) :=
  fun _ p _ _ U f =>
    ⟨ComplexPoints.eq_zero_of_valAt_eq_zero p U f, ComplexPoints.isUnit_of_valAt_ne_zero p U f⟩

end GlobalTheory
