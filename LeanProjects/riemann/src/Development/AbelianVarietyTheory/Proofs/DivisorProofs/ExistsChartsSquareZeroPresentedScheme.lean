import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PresCharts

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀} {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem appLE_congr {A Y : Scheme.{0}} {f g : A ⟶ Y} (h : f = g) (U : Y.Opens) (W : A.Opens)
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

theorem specMap_appLE_top {A B : CommRingCat.{0}} (f : A ⟶ B) (e : (⊤ : (Spec B).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ f := by
  rw [← Scheme.ΓSpecIso_naturality]
  rfl

def chartOpen (P : S.Presents s i) (T : AffOp X₀) : X.Opens :=
  haveI := P.isOpen T
  (P.y T).opensRange

theorem preimage_chartOpen (P : S.Presents s i) (T : AffOp X₀) : P.y T ⁻¹ᵁ chartOpen P T = ⊤ := by
  haveI := P.isOpen T
  exact Scheme.Hom.preimage_opensRange _

def chartSec (P : S.Presents s i) (T : AffOp X₀) : Γ(X, chartOpen P T) ⟶ CommRingCat.of (S.F.obj T) :=
  (P.y T).appLE (chartOpen P T) ⊤ (preimage_chartOpen P T).ge ≫ (Scheme.ΓSpecIso _).hom

instance isIso_chartSec (P : S.Presents s i) (T : AffOp X₀) : IsIso (chartSec P T) := by
  haveI := P.isOpen T
  haveI : IsIso ((P.y T).app (chartOpen P T)) := Scheme.Hom.isIso_app _ _ le_rfl
  have h : homOfLE (preimage_chartOpen P T).ge = eqToHom (preimage_chartOpen P T).symm :=
    Subsingleton.elim _ _
  unfold chartSec Scheme.Hom.appLE
  rw [h]
  infer_instance

theorem chartOpen_le (P : S.Presents s i) ⦃T T' : AffOp X₀⦄ (a : T ⟶ T') : chartOpen P T' ≤ chartOpen P T := by
  haveI := P.isOpen T
  haveI := P.isOpen T'
  intro x hx
  change x ∈ ((P.y T').opensRange : Set X) at hx
  change x ∈ ((P.y T).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange] at hx ⊢
  obtain ⟨q, rfl⟩ := hx
  rw [← P.nat a, Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

theorem res_chartSec (P : S.Presents s i) ⦃T T' : AffOp X₀⦄ (a : T ⟶ T') :
    X.presheaf.map (homOfLE (chartOpen_le P a)).op ≫ chartSec P T' =
      chartSec P T ≫ CommRingCat.ofHom (mp S.F a : S.F.obj T →+* S.F.obj T') := by
  have e1 : (⊤ : (Sp (S.F.obj T')).Opens) ≤ P.y T' ⁻¹ᵁ chartOpen P T :=
    (preimage_chartOpen P T').ge.trans (Scheme.Hom.preimage_mono _ (chartOpen_le P a))
  unfold chartSec
  rw [← Category.assoc, Scheme.Hom.map_appLE _ _ (homOfLE (chartOpen_le P a)).op]
  rw [appLE_congr (P.nat a).symm _ _ e1]
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ (preimage_chartOpen P T).ge le_top]
  rw [Category.assoc, Category.assoc]
  congr 1
  exact specMap_appLE_top _ _

theorem injective_of_isPullback {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}
    (h : IsPullback i s₀ s (spMap π)) : Function.Injective i := by
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  exact i.isClosedEmbedding.injective

theorem fromSpec_appLE_ΓSpecIso {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e ≫ (Scheme.ΓSpecIso Γ(Y, U)).hom = 𝟙 _ := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  have : ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE e).op : Opposite.op _ ⟶ Opposite.op _) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem range_affPt (T : AffOp X₀) : Set.range (affPt s₀ T.unop) = T.unop.1 :=
  IsAffineOpen.range_fromSpec T.unop.2

theorem exists_of_mem_chartOpen (hI : I ^ 2 = 0) (P : S.Presents s i) (T : AffOp X₀) (x : X)
    (hx : x ∈ chartOpen P T) : ∃ x₀ ∈ T.unop.1, i x₀ = x := by
  haveI := P.isOpen T
  change x ∈ ((P.y T).opensRange : Set X) at hx
  rw [Scheme.Hom.coe_opensRange] at hx
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨q₀, rfl⟩ := (S.surjective_spMap_p hI T).surj q
  refine ⟨affPt s₀ T.unop q₀, ?_, ?_⟩
  · have : affPt s₀ T.unop q₀ ∈ Set.range (affPt s₀ T.unop) := Set.mem_range_self _
    rw [range_affPt] at this
    exact this
  · rw [← Scheme.Hom.comp_apply, ← P.red T, Scheme.Hom.comp_apply]

theorem le_preimage_chartOpen (P : S.Presents s i) (T : AffOp X₀) :
    T.unop.1 ≤ i ⁻¹ᵁ chartOpen P T := by
  haveI := P.isOpen T
  intro x₀ hx₀
  have hx' : x₀ ∈ Set.range (affPt s₀ T.unop) := by rw [range_affPt]; exact hx₀
  obtain ⟨q, rfl⟩ := hx'
  change i (affPt s₀ T.unop q) ∈ ((P.y T).opensRange : Set X)
  rw [Scheme.Hom.coe_opensRange, ← Scheme.Hom.comp_apply, ← P.red T, Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

theorem preimage_chartOpen_eq (hI : I ^ 2 = 0) (hinj : Function.Injective i) (P : S.Presents s i)
    (T : AffOp X₀) : i ⁻¹ᵁ chartOpen P T = T.unop.1 := by
  refine le_antisymm (fun x₀ hx₀ ↦ ?_) (le_preimage_chartOpen P T)
  obtain ⟨y₀, hy₀, e⟩ := exists_of_mem_chartOpen hI P T (i x₀) hx₀
  rw [← hinj e]
  exact hy₀

theorem appLE_chartSec (P : S.Presents s i) (T : AffOp X₀) (hT : T.unop.1 ≤ i ⁻¹ᵁ chartOpen P T) :
    i.appLE (chartOpen P T) T.unop.1 hT = chartSec P T ≫ CommRingCat.ofHom (S.p T) := by
  have hf : ⊤ ≤ (affPt s₀ T.unop) ⁻¹ᵁ T.unop.1 := (IsAffineOpen.fromSpec_preimage_self T.unop.2).ge
  have k : (affPt s₀ T.unop).appLE T.unop.1 ⊤ hf ≫ (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom = 𝟙 _ :=
    fromSpec_appLE_ΓSpecIso T.unop.2 hf
  have e1 : (⊤ : (Sp (Sec s₀ T.unop.1)).Opens) ≤ (affPt s₀ T.unop ≫ i) ⁻¹ᵁ chartOpen P T :=
    hf.trans (Scheme.Hom.preimage_mono _ hT)
  calc i.appLE (chartOpen P T) T.unop.1 hT
      = i.appLE (chartOpen P T) T.unop.1 hT ≫ ((affPt s₀ T.unop).appLE T.unop.1 ⊤ hf ≫
          (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom) := by rw [k, Category.comp_id]
    _ = (affPt s₀ T.unop ≫ i).appLE (chartOpen P T) ⊤ e1 ≫ (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom := by
        rw [← Scheme.Hom.appLE_comp_appLE (affPt s₀ T.unop) i _ _ _ hT hf]
        exact (Category.assoc _ _ _).symm
    _ = (spMap (S.p T) ≫ P.y T).appLE (chartOpen P T) ⊤ ((P.red T) ▸ e1) ≫
          (Scheme.ΓSpecIso Γ(X₀, T.unop.1)).hom := by
        rw [appLE_congr (P.red T).symm _ _ e1]
    _ = (chartSec P T ≫ CommRingCat.ofHom (S.p T) : Γ(X, chartOpen P T) ⟶ Γ(X₀, T.unop.1)) := by
        rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ (preimage_chartOpen P T).ge le_top]
        refine (Category.assoc _ _ _).trans ?_
        unfold chartSec
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        exact specMap_appLE_top _ _

def chartInv (P : S.Presents s i) (T : AffOp X₀) : S.F.obj T →+* Γ(X, chartOpen P T) :=
  (RingEquiv.ofBijective (chartSec P T).hom (ConcreteCategory.bijective_of_isIso (chartSec P T))).symm.toRingHom

theorem chartSec_chartInv (P : S.Presents s i) (T : AffOp X₀) (b : S.F.obj T) :
    (chartSec P T).hom (chartInv P T b) = b :=
  (RingEquiv.ofBijective (chartSec P T).hom (ConcreteCategory.bijective_of_isIso (chartSec P T))).apply_symm_apply b

theorem chartInv_eq_iff (P : S.Presents s i) (T : AffOp X₀) (b : S.F.obj T) (c : Γ(X, chartOpen P T)) :
    chartInv P T b = c ↔ (chartSec P T).hom c = b := by
  constructor
  · rintro rfl; exact chartSec_chartInv P T b
  · rintro rfl
    exact (ConcreteCategory.bijective_of_isIso (chartSec P T)).1 (chartSec_chartInv P T _)

end GlobalTheory.PresCharts

open GlobalTheory.PresCharts in

theorem GlobalTheory.PresCharts.exists_charts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i), IsPullback i s₀ s (spMap π) → ∃ (V : AffOp X₀ → X.Opens) (hV : ∀ ⦃T T' : AffOp X₀⦄, (T ⟶ T') → V T' ≤ V T) (hi : ∀ T, T.unop.1 ≤ i ⁻¹ᵁ V T) (e : ∀ T, S.F.obj T →+* Γ(X, V T)), (∀ T, i ⁻¹ᵁ V T = T.unop.1) ∧ (∀ (T T' : AffOp X₀) (a : T ⟶ T') (b : S.F.obj T), e T' (mp S.F a b) = resG X (hV a) (e T b)) ∧ ∀ T b, (i.appLE (V T) T.unop.1 (hi T)).hom (e T b) = S.p T b := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S X s i P h
  have hinj := injective_of_isPullback hπ h
  refine ⟨chartOpen P, chartOpen_le P, le_preimage_chartOpen P, chartInv P,
    preimage_chartOpen_eq hI hinj P, fun T T' a b ↦ ?_, fun T b ↦ ?_⟩
  · rw [chartInv_eq_iff]
    have := congrArg (fun f ↦ f.hom (chartInv P T b)) (res_chartSec P a)
    refine this.trans ?_
    change (mp S.F a) ((chartSec P T).hom (chartInv P T b)) = _
    rw [chartSec_chartInv]
  · have := congrArg (fun f ↦ f.hom (chartInv P T b)) (appLE_chartSec P T (le_preimage_chartOpen P T))
    refine this.trans ?_
    change S.p T ((chartSec P T).hom (chartInv P T b)) = _
    rw [chartSec_chartInv]
