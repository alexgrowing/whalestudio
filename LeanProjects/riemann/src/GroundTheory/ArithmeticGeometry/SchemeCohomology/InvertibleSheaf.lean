import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ModulesTensor
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace

universe u

namespace GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}

noncomputable instance : MonoidalCategory X.Modules :=
  sheafModulesMonoidal (Opens.grothendieckTopology X) X.sheaf

noncomputable instance : SymmetricCategory X.Modules :=
  sheafModulesSymmetric (Opens.grothendieckTopology X) X.sheaf

instance isIso_ringSheafId_scheme : IsIso (ringSheafId (Opens.grothendieckTopology X) X.sheaf) :=
  inferInstanceAs (IsIso (𝟙 (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

variable (X) in

abbrev PMod := PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)

variable (X) in

noncomputable abbrev sheafifyMod : PMod X ⥤ X.Modules :=
  modulesSheafification (Opens.grothendieckTopology X) X.sheaf

variable (X) in

noncomputable abbrev preMod : X.Modules ⥤ PMod X :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (ringSheafId _ X.sheaf)

variable (X) in

noncomputable abbrev sheafifyModAdj : sheafifyMod X ⊣ preMod X :=
  PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (R₀ := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) (R := X.ringCatSheaf) (ringSheafId _ X.sheaf)

instance isIso_sheafifyModAdj_counit : IsIso (sheafifyModAdj X).counit :=
  inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit)

noncomputable instance : (sheafifyMod X).Monoidal :=
  modulesSheafificationMonoidal (Opens.grothendieckTopology X) X.sheaf

noncomputable def tensorIso (M N : X.Modules) :
    (sheafifyMod X).obj ((preMod X).obj M ⊗ (preMod X).obj N) ≅ M ⊗ N :=
  (Functor.Monoidal.μIso (sheafifyMod X) _ _).symm ≪≫
    (asIso ((sheafifyModAdj X).counit.app M) ⊗ᵢ asIso ((sheafifyModAdj X).counit.app N))

noncomputable def tensorToSheaf (M N : X.Modules) :
    (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj (M ⊗ N) :=
  (sheafifyModAdj X).unit.app _ ≫ (preMod X).map (tensorIso M N).hom

noncomputable def tensorLift {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) : M ⊗ N ⟶ G :=
  (tensorIso M N).inv ≫ ((sheafifyModAdj X).homEquiv _ _).symm e

@[reassoc]
lemma tensorToSheaf_tensorLift {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) :
    tensorToSheaf M N ≫ (preMod X).map (tensorLift e) = e := by
  rw [tensorToSheaf, tensorLift, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

lemma tensorLift_unique {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) (f : M ⊗ N ⟶ G)
    (hf : tensorToSheaf M N ≫ (preMod X).map f = e) : f = tensorLift e := by
  rw [← hf, tensorLift, tensorToSheaf, Category.assoc, ← Functor.map_comp,
    ← Adjunction.homEquiv_unit, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]

lemma W_tensorToSheaf (M N : X.Modules) :
    ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj (tensorToSheaf M N) := by
  refine MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  change (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map _)
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact GrothendieckTopology.W_toSheafify _ _

lemma sheaf_eq_of_locally {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]
    [Limits.HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
    [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} (s t : ToType (F.1.obj (op V)))
    (h : ∀ x ∈ V, ∃ (W : Opens T) (i : W ≤ V), x ∈ W ∧
      F.1.map (homOfLE i).op s = F.1.map (homOfLE i).op t) : s = t := by
  choose W i hx h using h
  refine F.eq_of_locally_eq' (U := fun x : V => W x.1 x.2) V (fun x => homOfLE (i _ _)) ?_ s t
    (fun x => h _ _)
  intro x hxV
  exact Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _ _⟩

lemma sheaf_exists_glue {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]
    [Limits.HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
    [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} {ι : Type u} (W : ι → Opens T)
    (i : ∀ a, W a ≤ V) (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, ToType (F.1.obj (op (W a))))
    (hsf : ∀ a b, F.1.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op (sf a) =
      F.1.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op (sf b)) :
    ∃ s : ToType (F.1.obj (op V)), ∀ a, F.1.map (homOfLE (i a)).op s = sf a := by
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W V (fun a => homOfLE (i a))
    (fun x hxV => Opens.mem_iSup.2 (hcov x hxV)) sf hsf
  exact ⟨s, hs⟩

noncomputable def resM (P : PMod X) {U V : X.Opens} (h : V ≤ U) (x : P.obj (op U)) : P.obj (op V) :=
  P.map (homOfLE h).op x

abbrev ringOn (X : Scheme.{u}) (V : X.Opens) := (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)

noncomputable def resR {U V : X.Opens} (h : V ≤ U) : ringOn X U →+* ringOn X V :=
  ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE h).op).hom

lemma resM_resM (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (x : P.obj (op U)) :
    resM P i (resM P h x) = resM P (i.trans h) x := by
  rw [resM, resM, resM, ← PresheafOfModules.map_comp_apply]
  rfl

lemma resM_smul (P : PMod X) {U V : X.Opens} (h : V ≤ U) (r : ringOn X U) (x : P.obj (op U)) :
    resM P h (r • x) = resR h r • resM P h x :=
  PresheafOfModules.map_smul _ _ _ _

lemma resM_add (P : PMod X) {U V : X.Opens} (h : V ≤ U) (x y : P.obj (op U)) :
    resM P h (x + y) = resM P h x + resM P h y :=
  map_add _ _ _

lemma resM_zero (P : PMod X) {U V : X.Opens} (h : V ≤ U) : resM P h (0 : P.obj (op U)) = 0 :=
  map_zero _

lemma resM_smul_res (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X V)
    (x : P.obj (op U)) : resM P i (r • resM P h x) = resR i r • resM P (i.trans h) x := by
  rw [resM_smul, resM_resM]

lemma app_resM {P Q : PMod X} (φ : P ⟶ Q) {U V : X.Opens} (h : V ≤ U) (x : P.obj (op U)) :
    φ.app (op V) (resM P h x) = resM Q h (φ.app (op U) x) :=
  PresheafOfModules.naturality_apply φ _ x

lemma app_smul {P Q : PMod X} (φ : P ⟶ Q) {U : X.Opens} (r : ringOn X U) (x : P.obj (op U)) :
    φ.app (op U) (r • x) = r • φ.app (op U) x :=
  (φ.app (op U)).hom.map_smul r x

lemma resR_resR {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X U) :
    resR i (resR h r) = resR (i.trans h) r := by
  rw [resR, resR, resR, ← RingHom.comp_apply, ← RingCat.hom_comp, ← Functor.map_comp]
  rfl

def IsBasisOn (P : PMod X) (U : X.Opens) (s : P.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op V) => r • resM P h s)

theorem IsBasisOn.map_of_alt {P : PMod X} {F : X.Modules} (φ : P ⟶ (preMod X).obj F)
    (hφ : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj φ)
    {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s) :
    IsBasisOn ((preMod X).obj F) U (φ.app _ s) := by
  obtain ⟨hinj, hsurj⟩ := (ModulesTensor.W_toPresheaf_iff φ).1 hφ
  have hres : ∀ (V : X.Opens) (h : V ≤ U), resM ((preMod X).obj F) h (φ.app _ s) =
      φ.app _ (resM P h s) :=
    fun V h => (PresheafOfModules.naturality_apply φ _ s).symm
  have hsm : ∀ (V : X.Opens) (r : ringOn X V) (x : P.obj (op V)),
      φ.app (op V) (r • x) = r • φ.app (op V) x := fun V r x => (φ.app (op V)).hom.map_smul r x
  have hPsm : ∀ (V W : X.Opens) (i : W ≤ V) (h : V ≤ U) (r : ringOn X V),
      resM P i (r • resM P h s) =
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE i).op r • resM P (i.trans h) s := by
    intro V W i h r
    rw [resM, PresheafOfModules.map_smul, resM, ← PresheafOfModules.map_comp_apply]
    rfl
  have inj : ∀ (V : X.Opens) (h : V ≤ U) (r : ringOn X V),
      r • resM ((preMod X).obj F) h (φ.app _ s) = 0 → r = 0 := by
    intro V h r hr
    rw [hres, ← hsm] at hr
    have hz := hinj (op V) _ hr
    apply sheaf_eq_of_locally X.sheaf (V := V) r 0
    intro x hx
    obtain ⟨W, f, hf, hxW⟩ := hz x hx
    refine ⟨W, f.le, hxW, ?_⟩
    have hf' : resM P f.le (r • resM P h s) = 0 := hf
    rw [hPsm] at hf'
    have := (hs W (f.le.trans h)).1 (a₁ := (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map
      (homOfLE f.le).op r) (a₂ := 0) (by simp only [zero_smul]; exact hf')
    change ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE f.le).op) r = _
    rw [this]
    exact (map_zero _).symm
  intro V h
  constructor
  · intro r₁ r₂ e
    have := inj V h (r₁ - r₂) (by rw [sub_smul]; exact sub_eq_zero.mpr e)
    exact sub_eq_zero.mp this
  · intro σ
    have hσ := hsurj (op V) σ
    choose W f hf hxW using hσ
    choose p hp using hf
    have hWU : ∀ x hx, W x hx ≤ U := fun x hx => (f x hx).le.trans h
    choose rr hrr using fun x hx => (hs (W x hx) (hWU x hx)).2 (p x hx)
    have key : ∀ x hx, rr x hx • resM ((preMod X).obj F) (hWU x hx) (φ.app _ s) =
        resM ((preMod X).obj F) (f x hx).le σ := by
      intro x hx
      have e := hrr x hx
      simp only at e
      rw [← app_resM, ← app_smul, e]
      exact hp x hx
    obtain ⟨r, hr⟩ := sheaf_exists_glue X.sheaf (V := V) (ι := V) (fun a => W a.1 a.2)
      (fun a => (f a.1 a.2).le) (fun x hx => ⟨⟨x, hx⟩, hxW x hx⟩) (fun a => rr a.1 a.2) (by
        intro a b
        have hab : W a.1 a.2 ⊓ W b.1 b.2 ≤ U := inf_le_left.trans (hWU _ _)
        have := inj _ hab (resR inf_le_left (rr a.1 a.2) - resR inf_le_right (rr b.1 b.2)) (by
          rw [sub_smul, sub_eq_zero, ← resM_smul_res _ (hWU a.1 a.2) inf_le_left,
            ← resM_smul_res _ (hWU b.1 b.2) inf_le_right, key, key, resM_resM, resM_resM])
        exact sub_eq_zero.mp this)
    refine ⟨r, ?_⟩
    apply sheaf_eq_of_locally ⟨F.presheaf, F.isSheaf⟩ (V := V)
    intro x hx
    refine ⟨W x hx, (f x hx).le, hxW x hx, ?_⟩
    change resM ((preMod X).obj F) (f x hx).le (r • resM ((preMod X).obj F) h (φ.app _ s)) =
      resM ((preMod X).obj F) (f x hx).le σ
    rw [resM_smul, resM_resM, ← key x hx]
    congr 1
    exact hr ⟨x, hx⟩

lemma IsBasisOn.restrict {P : PMod X} {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    {V : X.Opens} (h : V ≤ U) : IsBasisOn P V (resM P h s) := by
  intro W i
  have := hs W (i.trans h)
  simp only [resM_resM]
  exact this

lemma isBasisOn_one (U : X.Opens) :
    IsBasisOn ((preMod X).obj (𝟙_ X.Modules)) U (1 : ringOn X U) := by
  intro V h
  have e : resM ((preMod X).obj (𝟙_ X.Modules)) h (1 : ringOn X U) = (1 : ringOn X V) :=
    map_one (resR h)
  simp only [e]
  change Function.Bijective (fun r : ringOn X V => r * 1)
  simp only [mul_one]
  exact Function.bijective_id

lemma IsBasisOn.tmul {P Q : PMod X} {U : X.Opens} {s : P.obj (op U)} {t : Q.obj (op U)}
    (hs : IsBasisOn P U s) (ht : IsBasisOn Q U t) :
    IsBasisOn (P ⊗ Q) U (s ⊗ₜ t : (P ⊗ Q).obj (op U)) := by
  intro V h
  have e : resM (P ⊗ Q) h (s ⊗ₜ t : (P ⊗ Q).obj (op U)) =
      (resM P h s ⊗ₜ resM Q h t : (P ⊗ Q).obj (op V)) := rfl
  rw [e]
  let eP := LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM P h s)) (hs V h)
  let eQ := LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM Q h t)) (ht V h)
  let E := (TensorProduct.lid (ringOn X V) (ringOn X V)).symm ≪≫ₗ TensorProduct.congr eP eQ
  have hE : ∀ r : ringOn X V, E r = r • (resM P h s ⊗ₜ resM Q h t) := by
    intro r
    change eP 1 ⊗ₜ eQ r = _
    change ((1 : ringOn X V) • resM P h s) ⊗ₜ (r • resM Q h t) = _
    rw [one_smul, TensorProduct.tmul_smul]
  have : (fun r : ringOn X V => r • (resM P h s ⊗ₜ resM Q h t : (P ⊗ Q).obj (op V))) = E := by
    funext r
    exact (hE r).symm
  have hb := E.bijective
  rw [← this] at hb
  exact hb

lemma IsBasisOn.map_iso {M N : X.Modules} (e : M ≅ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s) :
    IsBasisOn ((preMod X).obj N) U (((preMod X).map e.hom).app _ s) :=
  hs.map_of_alt _ (MorphismProperty.of_isIso _ _)

def IsInvertibleSheaf (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : ((preMod X).obj M).obj (op U)),
    IsBasisOn ((preMod X).obj M) U s

lemma isInvertibleSheaf_unit : IsInvertibleSheaf (𝟙_ X.Modules) :=
  fun _ => ⟨⊤, trivial, (1 : ringOn X ⊤), isBasisOn_one ⊤⟩

lemma IsInvertibleSheaf.of_iso {M N : X.Modules} (e : M ≅ N) (hM : IsInvertibleSheaf M) :
    IsInvertibleSheaf N := by
  intro x
  obtain ⟨U, hx, s, hs⟩ := hM x
  exact ⟨U, hx, _, hs.map_iso e⟩

lemma IsInvertibleSheaf.tensor {M N : X.Modules} (hM : IsInvertibleSheaf M)
    (hN : IsInvertibleSheaf N) : IsInvertibleSheaf (M ⊗ N) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hM x
  obtain ⟨V, hxV, t, ht⟩ := hN x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, _, ((hs.restrict inf_le_left).tmul (ht.restrict inf_le_right)).map_of_alt
    (tensorToSheaf M N) (W_tensorToSheaf M N)⟩

lemma isIso_of_locally_bijective {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U, Function.Bijective (f.app V)) : IsIso f := by
  choose U hxU hU using hf
  have nat : ∀ {V W : X.Opens} (i : W ≤ V) (σ : Γ(M, V)),
      f.app W (M.presheaf.map (homOfLE i).op σ) = N.presheaf.map (homOfLE i).op (f.app V σ) :=
    fun i σ => NatTrans.naturality_apply f.mapPresheaf (homOfLE i).op σ
  have inj : ∀ V : X.Opens, Function.Injective (f.app V) := by
    intro V σ τ hστ
    apply sheaf_eq_of_locally ⟨M.presheaf, M.isSheaf⟩ (V := V)
    intro x hx
    refine ⟨V ⊓ U x, inf_le_left, ⟨hx, hxU x⟩, ?_⟩
    apply (hU x (V ⊓ U x) inf_le_right).1
    change f.app _ (M.presheaf.map _ σ) = f.app _ (M.presheaf.map _ τ)
    rw [nat, nat, hστ]
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨inj V, fun τ => ?_⟩
  have loc : ∀ x : {x : X // x ∈ V}, ∃ σ : Γ(M, V ⊓ U x.1),
      f.app _ σ = N.presheaf.map (homOfLE (inf_le_left : V ⊓ U x.1 ≤ V)).op τ :=
    fun x => (hU x.1 _ inf_le_right).2 _
  choose σ hσ using loc
  obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨M.presheaf, M.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
    (fun a => V ⊓ U a.1) (fun _ => inf_le_left) (fun x hx => ⟨⟨x, hx⟩, hx, hxU x⟩) σ (by
      intro a b
      apply inj
      change f.app _ (M.presheaf.map _ (σ a)) = f.app _ (M.presheaf.map _ (σ b))
      rw [nat, nat, hσ, hσ]
      change ((N.presheaf.map _ ≫ N.presheaf.map _) τ) = ((N.presheaf.map _ ≫ N.presheaf.map _) τ)
      rw [← N.presheaf.map_comp, ← N.presheaf.map_comp]
      rfl)
  refine ⟨g, ?_⟩
  apply sheaf_eq_of_locally ⟨N.presheaf, N.isSheaf⟩ (V := V)
  intro x hx
  refine ⟨V ⊓ U x, inf_le_left, ⟨hx, hxU x⟩, ?_⟩
  change N.presheaf.map _ (f.app V g) = _
  rw [← nat]
  have := hg ⟨x, hx⟩
  simp only at this
  rw [this]
  exact hσ ⟨x, hx⟩

lemma bijective_app_of_isBasisOn {M N : X.Modules} (f : M ⟶ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s)
    (hfs : IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) (V : X.Opens) (h : V ≤ U) :
    Function.Bijective (f.app V) := by
  have e : (fun r : ringOn X V => r • resM ((preMod X).obj N) h (((preMod X).map f).app _ s)) =
      f.app V ∘ (fun r : ringOn X V => r • resM ((preMod X).obj M) h s) := by
    funext r
    change _ = ((preMod X).map f).app (op V) (r • resM ((preMod X).obj M) h s)
    rw [app_smul, app_resM]
  have h1 := hfs V h
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff _ (hs V h)).1 h1

lemma isIso_of_isBasisOn {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (s : ((preMod X).obj M).obj (op U)),
      IsBasisOn ((preMod X).obj M) U s ∧ IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) :
    IsIso f := by
  apply isIso_of_locally_bijective
  intro x
  obtain ⟨U, hx, s, hs, hfs⟩ := hf x
  exact ⟨U, hx, fun V h => bijective_app_of_isBasisOn f hs hfs V h⟩

end GroundTheory.Arith.SchemeCoh
