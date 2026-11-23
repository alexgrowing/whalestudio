import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GeneratorFunctor

open Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem isRepresentable_of_charts (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) {J : Type} (X : J → Scheme.{0})
    (x : ∀ j, F.obj (op (X j))) (W : ∀ (_ : J) (Z : Scheme.{0}), F.obj (op Z) → Z.Opens)
    (hW : ∀ j (Z : Scheme.{0}) (y : F.obj (op Z)) (Z' : Scheme.{0}) (a : Z' ⟶ Z),
      Set.range a ⊆ (W j Z y : Set Z) ↔ ∃ g : Z' ⟶ X j, F.map g.op (x j) = F.map a.op y)
    (inj : ∀ j (Z : Scheme.{0}) (g g' : Z ⟶ X j), F.map g.op (x j) = F.map g'.op (x j) → g = g')
    (cov : ∀ (Z : Scheme.{0}) (y : F.obj (op Z)) (z : Z), ∃ j, z ∈ W j Z y) :
    F.IsRepresentable := by
  let F' : Sheaf Scheme.zariskiTopology.{0} (Type) := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ j, yoneda.obj (X j) ⟶ F'.1 := fun j => yonedaEquiv.symm (x j)
  have hfa : ∀ j (Z : Scheme.{0}) (g : Z ⟶ X j), (f j).app (op Z) g = F.map g.op (x j) :=
    fun j Z g => rfl
  have hι : ∀ j (Z : Scheme.{0}) (y : F.obj (op Z)),
      ∃ g : (W j Z y).toScheme ⟶ X j, F.map g.op (x j) = F.map (W j Z y).ι.op y :=
    fun j Z y => (hW j Z y _ _).1 (by simp)
  have hf : ∀ j, IsOpenImmersion.presheaf (f j) := by
    intro j
    refine MorphismProperty.relative.of_exists fun Z g => ?_
    obtain ⟨y, rfl⟩ := yonedaEquiv.symm.surjective g
    obtain ⟨c, hc⟩ := hι j Z y
    refine ⟨(W j Z y).toScheme, yoneda.map c, (W j Z y).ι, ?_, inferInstance⟩
    refine IsPullback.of_forall_isPullback_app fun T => ?_
    obtain ⟨T⟩ := T
    rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext (a : T ⟶ _)
      change F.map (a ≫ c).op (x j) = F.map (a ≫ (W j Z y).ι).op y
      simp only [op_comp, Functor.map_comp_apply, hc]
    · rintro (a : T ⟶ _) (a' : T ⟶ _) ⟨-, h⟩
      exact (cancel_mono (W j Z y).ι).1 h
    · rintro (g : T ⟶ _) (a : T ⟶ _) h
      replace h : F.map g.op (x j) = F.map a.op y := h
      have hr := (hW j Z y T a).2 ⟨g, h⟩
      let l := IsOpenImmersion.lift (W j Z y).ι a (by simpa using hr)
      have hl : l ≫ (W j Z y).ι = a := IsOpenImmersion.lift_fac _ _ _
      refine ⟨l, inj j T _ _ ?_, hl⟩
      change F.map (l ≫ c).op (x j) = _
      rw [h, ← hl]
      simp only [op_comp, Functor.map_comp_apply, hc]
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    refine ⟨fun {Z} y => ?_⟩
    rw [Scheme.mem_grothendieckTopology_iff]
    refine ⟨Z.openCoverOfIsOpenCover (fun j => W j Z y) ?_, ?_⟩
    · exact eq_top_iff.2 fun z _ => Opens.mem_iSup.2 (cov Z y z)
    · rintro _ _ ⟨j⟩
      obtain ⟨c, hc⟩ := hι j Z y
      refine ⟨(Sigma.ι (fun j => yoneda.obj (X j)) j).app _ c, ?_⟩
      refine Eq.trans ?_ hc
      exact congrArg (fun φ : yoneda.obj (X j) ⟶ F'.1 => φ.app (op (W j Z y).toScheme) c)
        (Sigma.ι_desc f j)
  exact Scheme.LocalRepresentability.isRepresentable hf

theorem exists_torus (S : Scheme.{0}) (κ : Type) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : κ → Γ(T, ⊤)ˣ),
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : κ → Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        ∀ k, g.appTop.hom (t k).val = (v k).val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        (∀ k, g.appTop.hom (t k).val = g'.appTop.hom (t k).val) → g = g' := by
  refine ⟨(splitTorus S (FreeAbelianGroup κ)).left, (splitTorus S (FreeAbelianGroup κ)).hom,
    fun k => charUnit S _ (FreeAbelianGroup.of k), fun Z c v => ?_, fun Z g g' h hk => ?_⟩
  · let φ : FreeAbelianGroup κ →+ Additive Γ(Z, ⊤)ˣ :=
      FreeAbelianGroup.lift fun k => Additive.ofMul (v k)
    obtain ⟨g, hg⟩ := (splitTorusPointsEquiv S (FreeAbelianGroup κ) (Over.mk c)).surjective
      (AddMonoidHom.toMultiplicativeLeft φ)
    refine ⟨g.left, Over.w g, fun k => ?_⟩
    refine (splitTorusPointsEquiv_val S _ (Over.mk c) g _).symm.trans ?_
    rw [hg]
    simp [φ]
  · let Z' : Over S := Over.mk (g' ≫ (splitTorus S (FreeAbelianGroup κ)).hom)
    let a : Z' ⟶ splitTorus S (FreeAbelianGroup κ) := Over.homMk g h
    let a' : Z' ⟶ splitTorus S (FreeAbelianGroup κ) := Over.homMk g' rfl
    have : a = a' := by
      apply (splitTorusPointsEquiv S (FreeAbelianGroup κ) Z').injective
      apply AddMonoidHom.toMultiplicativeLeft.symm.injective
      refine FreeAbelianGroup.lift_ext _ _ fun k => ?_
      apply Additive.toMul.injective
      apply Units.ext
      exact ((splitTorusPointsEquiv_val S _ Z' a _).trans (hk k)).trans
        (splitTorusPointsEquiv_val S _ Z' a' _).symm
    exact congrArg (·.left) this

noncomputable def pb {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    Γ(Y, U)ˣ →* Γ(Z, W)ˣ :=
  Units.map (f.appLE U W h).hom.toMonoidHom

theorem pb_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (W : Z.Opens) (h : W ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)ˣ) : (pb f U W h x).val = (f.appLE U W h).hom x.val := rfl

theorem pb_pb {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (W : Z.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    pb g V W h' (pb f U V h x) = pb (g ≫ f) U W (h'.trans (g.preimage_mono h)) x := by
  ext
  rw [pb_val, pb_val, pb_val, ← Scheme.Hom.appLE_comp_appLE]
  rfl

theorem pb_congr {Y Z : Scheme.{0}} {f f' : Z ⟶ Y} (e : f = f') (U : Y.Opens) (W : Z.Opens)
    (h : W ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) : pb f U W h x = pb f' U W (e ▸ h) x := by
  subst e; rfl

theorem res_eq_pb {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    res h x = pb (𝟙 X) U V h x := by
  ext
  rw [pb_val, Scheme.Hom.appLE, Scheme.Hom.id_app]
  rfl

theorem pullU_eq_pb {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)ˣ) :
    pullU f U x = pb f U _ le_rfl x := by
  ext
  rw [pb_val, ← Scheme.Hom.app_eq_appLE]
  rfl

theorem pb_id {X : Scheme.{0}} {U : X.Opens} (h : U ≤ 𝟙 X ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    pb (𝟙 X) U U h x = x := by
  rw [← res_eq_pb le_rfl]
  ext
  change (X.presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem pb_top {Y Z : Scheme.{0}} (f : Z ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) (x : Γ(Y, ⊤)ˣ) :
    (pb f ⊤ ⊤ h x).val = f.appTop.hom x.val := by
  rw [pb_val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem pb_id_comp {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (V W : Z.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ 𝟙 Z ⁻¹ᵁ V) (x : Γ(Y, U)ˣ) :
    pb (𝟙 Z) V W h' (pb f U V h x) = pb f U W (le_trans h' h) x := by
  rw [pb_pb]; exact pb_congr (Category.id_comp f) _ _ _ _

theorem pb_comp_id {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U V : Y.Opens) (W : Z.Opens)
    (h : V ≤ 𝟙 Y ⁻¹ᵁ U) (h' : W ≤ f ⁻¹ᵁ V) (x : Γ(Y, U)ˣ) :
    pb f V W h' (pb (𝟙 Y) U V h x) = pb f U W (h'.trans (f.preimage_mono h)) x := by
  rw [pb_pb]; exact pb_congr (Category.comp_id f) _ _ _ _

theorem pb_ι_injective {Y : Scheme.{0}} (W : Y.Opens) (h : ⊤ ≤ W.ι ⁻¹ᵁ W) :
    Function.Injective (pb W.ι W ⊤ h) := by
  intro x y e
  ext
  have : IsIso (W.ι.appLE W ⊤ h) := by
    rw [Scheme.Opens.ι_appLE]
    have : (homOfLE (show W.ι ''ᵁ ⊤ ≤ W by simp)) = eqToHom (by simp) := rfl
    erw [this]
    rw [eqToHom_op, eqToHom_map]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso (W.ι.appLE W ⊤ h)).1 (congrArg Units.val e)

theorem cover_ext {Y : Scheme.{0}} (𝒰 : Y.OpenCover) (V : Y.Opens) (x y : Γ(Y, V)ˣ)
    (h : ∀ i, pb (𝒰.f i) V _ le_rfl x = pb (𝒰.f i) V _ le_rfl y) : x = y := by
  ext
  refine 𝒰.ext_elem _ _ fun i => ?_
  have := congrArg Units.val (h i)
  rwa [pb_val, pb_val, ← Scheme.Hom.app_eq_appLE] at this

theorem cover_glue {Y : Scheme.{0}} (𝒰 : Y.OpenCover) (V : Y.Opens)
    (t : ∀ i, Γ(𝒰.X i, 𝒰.f i ⁻¹ᵁ V)ˣ)
    (ht : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j), a ≫ 𝒰.f i = a' ≫ 𝒰.f j →
      ∀ h h', pb a _ ⊤ h (t i) = pb a' _ ⊤ h' (t j)) :
    ∃ s : Γ(Y, V)ˣ, ∀ i, pb (𝒰.f i) V _ le_rfl s = t i := by
  let W : 𝒰.I₀ → Y.Opens := fun i => 𝒰.f i ''ᵁ (𝒰.f i ⁻¹ᵁ V)
  have hW : ∀ i, W i ≤ V := fun i => (𝒰.f i).image_preimage_le V
  have hW' : ∀ i, 𝒰.f i ⁻¹ᵁ V ≤ 𝒰.f i ⁻¹ᵁ W i := fun i =>
    ((𝒰.f i).preimage_image_eq _).ge
  have hc : V ≤ iSup W := fun y hy => by
    obtain ⟨i, z, rfl⟩ := 𝒰.exists_eq y
    exact Opens.mem_iSup.2 ⟨i, z, hy, rfl⟩
  have hu : ∀ i, ∃ u : Γ(Y, W i)ˣ, pb (𝒰.f i) _ _ (hW' i) u = t i := fun i => by
    refine ⟨Units.map ((𝒰.f i).appIso _).inv.hom.toMonoidHom (t i), ?_⟩
    ext
    rw [pb_val]
    change (((𝒰.f i).appIso _).inv ≫ (𝒰.f i).appLE _ _ _).hom _ = _
    rw [Scheme.Hom.appIso_inv_appLE]
    change ((𝒰.X i).presheaf.map (𝟙 _)).hom _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  choose u hu using hu
  have hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j) := by
    intro i j
    apply pb_ι_injective _ (by simp)
    let a := IsOpenImmersion.lift (𝒰.f i) (W i ⊓ W j).ι (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, -, hz⟩ := y.2.1
      exact ⟨z, hz⟩)
    let a' := IsOpenImmersion.lift (𝒰.f j) (W i ⊓ W j).ι (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, -, hz⟩ := y.2.2
      exact ⟨z, hz⟩)
    have ha : a ≫ 𝒰.f i = (W i ⊓ W j).ι := IsOpenImmersion.lift_fac _ _ _
    have ha' : a' ≫ 𝒰.f j = (W i ⊓ W j).ι := IsOpenImmersion.lift_fac _ _ _
    have h0 : ⊤ ≤ (W i ⊓ W j).ι ⁻¹ᵁ V := fun y _ => hW i y.2.1
    have := ht i j _ a a' (ha.trans ha'.symm) (by rw [← ha] at h0; exact h0)
      (by rw [← ha'] at h0; exact h0)
    rw [← hu i, ← hu j, pb_pb, pb_pb, pb_congr ha, pb_congr ha'] at this
    rw [res_eq_pb, res_eq_pb, pb_comp_id, pb_comp_id, this]
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val)
    (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(Y, V) from s) * (show Γ(Y, V) from s') = 1 := by
    apply Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    change (Y.presheaf.map (homOfLE (hW i)).op).hom _ = (Y.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  refine ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => ?_⟩
  have : res (hW i) (⟨s, s', e, (mul_comm _ _).trans e⟩ : Γ(Y, V)ˣ) = u i := Units.ext (hs i)
  rw [← hu i, ← this, res_eq_pb, pb_comp_id]

variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)

structure Pt (Z : Scheme.{0}) where
  b : Z ⟶ B
  s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ
  compat : ∀ k i i' (W : Z.Opens) (h : W ≤ b ⁻¹ᵁ (N k).U i) (h' : W ≤ b ⁻¹ᵁ (N k).U i'),
    pb (𝟙 Z) (b ⁻¹ᵁ (N k).U i') W h' (s k i') =
      pb b ((N k).U i ⊓ (N k).U i') W (le_inf h h') ((N k).g i i') *
        pb (𝟙 Z) (b ⁻¹ᵁ (N k).U i) W h (s k i)

variable {N}

theorem Pt.compat' {Z : Scheme.{0}} (y : Pt N Z) (k) (i i') {T : Scheme.{0}} (a : T ⟶ Z)
    (W : T.Opens) (h : W ≤ a ⁻¹ᵁ y.b ⁻¹ᵁ (N k).U i) (h' : W ≤ a ⁻¹ᵁ y.b ⁻¹ᵁ (N k).U i') :
    pb a _ W h' (y.s k i') =
      pb (a ≫ y.b) ((N k).U i ⊓ (N k).U i') W (le_inf h h') ((N k).g i i') *
        pb a _ W h (y.s k i) := by
  have := congrArg (pb a (y.b ⁻¹ᵁ (N k).U i ⊓ y.b ⁻¹ᵁ (N k).U i') W (le_inf h h'))
    (y.compat k i i' (y.b ⁻¹ᵁ (N k).U i ⊓ y.b ⁻¹ᵁ (N k).U i') inf_le_left inf_le_right)
  rwa [map_mul, pb_comp_id, pb_comp_id, pb_pb] at this

theorem Pt.ext' {Z : Scheme.{0}} {x y : Pt N Z} (hb : x.b = y.b)
    (hs : ∀ k i, x.s k i = pb (𝟙 Z) _ _ (by rw [hb]; exact le_rfl) (y.s k i)) : x = y := by
  obtain ⟨b, s, _⟩ := x
  obtain ⟨b', s', _⟩ := y
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := by
    funext k i
    exact (hs k i).trans (pb_id _ _)
  rfl

theorem Pt.congr {Z : Scheme.{0}} {x y : Pt N Z} (e : x = y) (k) (i) {T : Scheme.{0}} (a : T ⟶ Z)
    (W : T.Opens) (h h') : pb a _ W h (x.s k i) = pb a _ W h' (y.s k i) := by
  subst e; rfl

noncomputable def Pt.map {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (y : Pt N Z) : Pt N Z' where
  b := a ≫ y.b
  s k i := pb a _ ((a ≫ y.b) ⁻¹ᵁ (N k).U i) le_rfl (y.s k i)
  compat k i i' W h h' := by
    rw [pb_id_comp, pb_id_comp]
    exact y.compat' k i i' a W h h'

variable (N) in

noncomputable def genFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj Z := Pt N Z.unop
  map a := TypeCat.ofHom (Pt.map a.unop)
  map_id Z := by
    ext y
    exact Pt.ext' (Category.id_comp _) fun k i => rfl
  map_comp a a' := by
    ext y
    refine Pt.ext' (Category.assoc _ _ _) fun k i => ?_
    change pb _ _ _ _ _ = pb _ _ _ _ (pb _ _ _ _ (pb _ _ _ _ _))
    rw [pb_id_comp, pb_pb]
    rfl

theorem genFunctor_map {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (y : Pt N Z) :
    (genFunctor N).map a.op y = Pt.map a y := rfl

theorem isSheaf_genFunctor : Presieve.IsSheaf Scheme.zariskiTopology (genFunctor N) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro (x : ∀ j, Pt N (𝒰.X j)) hx
  replace hx : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = a' ≫ 𝒰.f j → Pt.map a (x i) = Pt.map a' (x j) := hx
  let b : Y ⟶ B := 𝒰.glueMorphisms (fun j => (x j).b) fun i j =>
    congrArg Pt.b (hx i j _ _ _ pullback.condition)
  have hb : ∀ j, 𝒰.f j ≫ b = (x j).b := fun j => 𝒰.ι_glueMorphisms _ _ j
  have hle : ∀ j (U : B.Opens), 𝒰.f j ⁻¹ᵁ b ⁻¹ᵁ U ≤ 𝟙 (𝒰.X j) ⁻¹ᵁ (x j).b ⁻¹ᵁ U := fun j U => by
    rw [← hb]; exact le_rfl
  have hs : ∀ k i, ∃ s : Γ(Y, b ⁻¹ᵁ (N k).U i)ˣ, ∀ j, pb (𝒰.f j) _ _ le_rfl s =
      pb (𝟙 _) _ _ (hle j _) ((x j).s k i) := fun k i => by
    refine cover_glue 𝒰 _ _ fun j j' Z a a' e h h' => ?_
    have := Pt.congr (hx j j' Z a a' e) k i (𝟙 Z) ⊤ (h.trans (a.preimage_mono (hle j _)))
      (h'.trans (a'.preimage_mono (hle j' _)))
    rw [pb_comp_id, pb_comp_id]
    exact (pb_id_comp _ _ _ _ _ _ _).symm.trans (this.trans (pb_id_comp _ _ _ _ _ _ _))
  choose s hs using hs
  have hs' : ∀ k i j (W : (𝒰.X j).Opens) (h : W ≤ 𝒰.f j ⁻¹ᵁ b ⁻¹ᵁ (N k).U i),
      pb (𝒰.f j) _ W h (s k i) = pb (𝟙 _) _ W (h.trans (hle j _)) ((x j).s k i) := by
    intro k i j W h
    have := congrArg (pb (𝟙 _) (𝒰.f j ⁻¹ᵁ b ⁻¹ᵁ (N k).U i) W h) (hs k i j)
    rwa [pb_id_comp, pb_id_comp] at this
  let y : Pt N Y := ⟨b, s, fun k i i' W h h' => cover_ext 𝒰 _ _ _ fun j => by
    rw [map_mul, pb_comp_id, pb_comp_id, pb_pb, hs', hs', pb_congr (hb j)]
    exact (x j).compat k i i' _ _ _⟩
  refine ⟨y, fun j => ?_, fun (y' : Pt N Y) hy' => ?_⟩
  · exact Pt.ext' (hb j) fun k i => hs k i j
  · replace hy' : ∀ j, Pt.map (𝒰.f j) y' = x j := hy'
    have e : y'.b = b := 𝒰.hom_ext _ _ fun j => (congrArg Pt.b (hy' j)).trans (hb j).symm
    refine Pt.ext' e fun k i => cover_ext 𝒰 _ _ _ fun j => ?_
    rw [pb_comp_id]
    refine Eq.trans ?_ (hs' k i j _ _).symm
    exact (pb_id_comp _ _ _ _ _ _ _).symm.trans (Pt.congr (hy' j) k i (𝟙 _) _ le_rfl _)

noncomputable def Pt.ofChart (hN : ∀ k, (N k).IsLB) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hb : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (v : κ → Γ(Z, ⊤)ˣ) : Pt N Z where
  b := b
  s k i := pb b _ _ (le_inf (le_top.trans (hb k)) le_rfl) ((N k).g (j k) i) *
    pb (𝟙 Z) ⊤ _ le_top (v k)
  compat k i i' W h h' := by
    have := LB.pull_cocycle (hN k) b (j k) i i' (W := W) (le_inf (le_top.trans (hb k)) h)
      (le_inf h h') (le_inf (le_top.trans (hb k)) h')
    simp only [res_eq_pb, pullU_eq_pb] at this
    rw [pb_id_comp, pb_id_comp, pb_id_comp] at this
    rw [map_mul, map_mul, pb_id_comp, pb_id_comp, pb_id_comp, pb_id_comp, ← this, ← _root_.mul_assoc,
      _root_.mul_comm (pb b ((N k).U i ⊓ (N k).U i') W (le_inf h h') _)]

theorem Pt.inverseBundleGeneratorPoint_ofChartUnits_sections (hN : ∀ k, (N k).IsLB) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hb : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (v : κ → Γ(Z, ⊤)ˣ) (k)
    {T : Scheme.{0}} (a : T ⟶ Z) (h) :
    (pb a _ ⊤ h ((Pt.ofChart hN b j hb v).s k (j k))).val = a.appTop.hom (v k).val := by
  have := LB.pull_g_self (hN k) b (j k) (W := b ⁻¹ᵁ (N k).U (j k)) (le_inf le_rfl le_rfl)
  rw [res_eq_pb, pullU_eq_pb, pb_id_comp] at this
  change (pb a (b ⁻¹ᵁ (N k).U (j k)) ⊤ h (pb _ _ _ _ _ * pb _ _ _ _ _)).val = _
  rw [this, _root_.one_mul, pb_comp_id, pb_top]

theorem Pt.ext_chart {Z : Scheme.{0}} {x y : Pt N Z} (hb : x.b = y.b) (j : ∀ k, (N k).ι)
    (hx : ∀ k, ⊤ ≤ 𝟙 Z ⁻¹ᵁ x.b ⁻¹ᵁ (N k).U (j k)) (hy : ∀ k, ⊤ ≤ 𝟙 Z ⁻¹ᵁ y.b ⁻¹ᵁ (N k).U (j k))
    (hs : ∀ k, pb (𝟙 Z) _ ⊤ (hx k) (x.s k (j k)) = pb (𝟙 Z) _ ⊤ (hy k) (y.s k (j k))) :
    x = y := by
  refine Pt.ext' hb fun k i => ?_
  have := congrArg (pb (𝟙 Z) ⊤ (x.b ⁻¹ᵁ (N k).U i) le_top) (hs k)
  rw [pb_id_comp, pb_id_comp] at this
  rw [← pb_id le_rfl (x.s k i), x.compat k (j k) i _ (le_top.trans (hx k)) le_rfl,
    y.compat k (j k) i _ (le_top.trans (hy k)) (by rw [hb]), this, pb_congr hb]

theorem isRepresentable_genFunctor [Fintype κ] (hN : ∀ k, (N k).IsLB) :
    (genFunctor N).IsRepresentable := by
  let U : (∀ k, (N k).ι) → B.Opens := fun j =>
    ⟨⋂ k, ((N k).U (j k) : Set B), isOpen_iInter_of_finite fun k => ((N k).U (j k)).isOpen⟩
  have hU : ∀ j k, U j ≤ (N k).U (j k) := fun j k _ hy => Set.mem_iInter.1 hy k
  choose T p t hex hun using fun j => exists_torus (U j).toScheme κ
  have hb : ∀ j k, ⊤ ≤ (p j ≫ (U j).ι) ⁻¹ᵁ (N k).U (j k) := fun j k z _ =>
    hU j k (p j z).2
  let x : ∀ j, Pt N (T j) := fun j => Pt.ofChart hN (p j ≫ (U j).ι) j (hb j) (t j)
  have hx : ∀ j (Z : Scheme.{0}) (g : Z ⟶ T j) k,
      ⊤ ≤ 𝟙 Z ⁻¹ᵁ (Pt.map g (x j)).b ⁻¹ᵁ (N k).U (j k) := fun j Z g k z _ =>
    hU j k (p j (g z)).2
  have hxs : ∀ j (Z : Scheme.{0}) (g : Z ⟶ T j) k,
      (pb (𝟙 Z) _ ⊤ (hx j Z g k) ((Pt.map g (x j)).s k (j k))).val =
        g.appTop.hom (t j k).val := fun j Z g k =>
    (congrArg Units.val (pb_id_comp _ _ _ _ _ _ _)).trans (Pt.inverseBundleGeneratorPoint_ofChartUnits_sections hN _ j (hb j) (t j) k g _)
  refine isRepresentable_of_charts (genFunctor N) isSheaf_genFunctor T x
    (fun j Z (y : Pt N Z) => y.b ⁻¹ᵁ U j) ?_ ?_ ?_
  · intro j Z (y : Pt N Z) Z' a
    simp only [genFunctor_map]
    constructor
    · intro h
      let c := IsOpenImmersion.lift (U j).ι (a ≫ y.b) (by
        rintro _ ⟨z, rfl⟩
        exact ⟨⟨_, h ⟨z, rfl⟩⟩, rfl⟩)
      have hc : c ≫ (U j).ι = a ≫ y.b := IsOpenImmersion.lift_fac _ _ _
      have hy : ∀ k, ⊤ ≤ 𝟙 Z' ⁻¹ᵁ (Pt.map a y).b ⁻¹ᵁ (N k).U (j k) := fun k z _ =>
        hU j k (h ⟨z, rfl⟩)
      obtain ⟨g, hg, hg'⟩ := hex j Z' c fun k => pb (𝟙 Z') _ ⊤ (hy k) ((Pt.map a y).s k (j k))
      refine ⟨g, Pt.ext_chart ?_ j (hx j Z' g) hy fun k => Units.ext ((hxs j Z' g k).trans (hg' k))⟩
      change g ≫ p j ≫ (U j).ι = a ≫ y.b
      rw [← hc, ← hg, Category.assoc]
    · rintro ⟨g, hg⟩ _ ⟨z, rfl⟩
      have e : g ≫ p j ≫ (U j).ι = a ≫ y.b := congrArg Pt.b hg
      change (a ≫ y.b) z ∈ U j
      rw [← e]
      exact (p j (g z)).2
  · intro j Z g g' h
    replace h : Pt.map g (x j) = Pt.map g' (x j) := h
    refine hun j Z g g' ?_ fun k => ?_
    · have e : g ≫ p j ≫ (U j).ι = g' ≫ p j ≫ (U j).ι := congrArg Pt.b h
      rw [← cancel_mono (U j).ι, Category.assoc, Category.assoc, e]
    · rw [← hxs, ← hxs]
      exact congrArg Units.val (Pt.congr h k (j k) _ _ _ _)
  · intro Z (y : Pt N Z) z
    choose j hj using fun k => LB.mem_of_cover (hN k) (y.b z)
    exact ⟨j, Set.mem_iInter.2 hj⟩

end GeneratorFunctor

set_option backward.isDefEq.respectTransparency false in
open GeneratorFunctor Opposite in

theorem exists_generatorScheme : ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val := by
  intro B κ _ N hN
  obtain ⟨G, ⟨e⟩⟩ := (isRepresentable_genFunctor hN).has_representation
  let x : Pt N G := e.homEquiv (𝟙 G)
  have he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x := fun g => by
    rw [e.homEquiv_eq]; rfl
  refine ⟨G, x.b, x.s, fun k i i' => ?_, fun Z b s hs => ?_⟩
  · rw [res_eq_pb, res_eq_pb, pullU_eq_pb]
    exact x.compat k i i' _ inf_le_left inf_le_right
  · let y : Pt N Z := ⟨b, s, fun k i i' W h h' => by
      have := congrArg (pb (𝟙 Z) (b ⁻¹ᵁ ((N k).U i ⊓ (N k).U i')) W (le_inf h h')) (hs k i i')
      rwa [map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp] at this⟩
    have key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ k i, (g.appLE (x.b ⁻¹ᵁ (N k).U i)
        (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (x.s k i).val = (s k i).val) ↔
        e.homEquiv g = y := fun g => by
      rw [he]
      constructor
      · rintro ⟨hg, h⟩
        refine (Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm
        exact (Units.ext (h k i).symm).trans (pb_id_comp _ _ _ _ _ _ _).symm
      · intro h
        have hg : g ≫ x.b = b := congrArg Pt.b h
        refine ⟨hg, fun k i => ?_⟩
        have := Pt.congr h k i (𝟙 Z) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl) le_rfl
        exact congrArg Units.val
          ((pb_id_comp _ _ _ _ _ _ _).symm.trans (this.trans (pb_id _ _)))
    refine ⟨e.homEquiv.symm y, (key _).2 (e.homEquiv.apply_symm_apply y), fun g hg => ?_⟩
    rw [← (key g).1 hg, Equiv.symm_apply_apply]

end GlobalTheory
