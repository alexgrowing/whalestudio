import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGrpObjSplitExtensionOfGenerators
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.BiextTriv
open GlobalTheory.GeneratorLaw GlobalTheory.TorusUnit

theorem exists_gen_of_pull {B E : Scheme.{0}} [IsAffine B] [IsAffine E] (e : B ⟶ E)
    (hinj : Function.Injective (CommRing.Pic.mapRingHom (e.appLE ⊤ ⊤ le_top).hom)) {N : LB E} (hN : N.IsLB)
    (h : ∃ t : LB.Gen (N.pull e), t.IsGen) : ∃ t : LB.Gen N, t.IsGen := by
  have hq := GlobalTheory.LB.isQuasicoherent_toMod hN
  have i1 := GlobalTheory.LB.invertible_sections hN (isAffineOpen_top E)
  have f1 := (GlobalTheory.LB.exists_isFrame_iff_free (pull_isLB hN e) (isAffineOpen_top B)).1
    ((GlobalTheory.LB.exists_isGen_iff_isFrame (pull_isLB hN e)).1 h)
  have f2 : Module.Free Γ(B, ⊤) Γ((Scheme.Modules.pullback e).obj (GlobalTheory.LB.toMod N), ⊤) :=
    Module.Free.of_equiv (GlobalTheory.LB.appLinearEquiv (GlobalTheory.LB.pullbackIso hN e) ⊤).symm
  have bc := QCoh.isBaseChange_pullbackSections e (GlobalTheory.LB.toMod N) (isAffineOpen_top B) (isAffineOpen_top E) le_top
  have hle : (⊤ : B.Opens) ≤ e ⁻¹ᵁ ⊤ := le_top
  letI := QCoh.appLEAlgebra e hle
  letI := QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (GlobalTheory.LB.toMod N)) hle
  haveI := QCoh.appLE_isScalarTower e ((Scheme.Modules.pullback e).obj (GlobalTheory.LB.toMod N)) hle
  have f3 := Module.Free.of_equiv bc.equiv.symm
  refine (GlobalTheory.LB.exists_isGen_iff_isFrame hN).2 ((GlobalTheory.LB.exists_isFrame_iff_free hN (isAffineOpen_top E)).2 ?_)
  rw [← CommRing.Pic.mk_eq_one_iff_free]
  apply hinj
  rw [map_one]
  have : CommRing.Pic.mapRingHom (e.appLE ⊤ ⊤ le_top).hom = CommRing.Pic.mapAlgebra Γ(E, ⊤) Γ(B, ⊤) :=
    CommRing.Pic.mapRingHom_algebraMap
  rw [this, CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]
  exact Module.Free.of_equiv (((CommRing.Pic.mk.linearEquiv _ _).baseChange _ Γ(B, ⊤) _ _).symm)

theorem exists_gen_pull {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (e : Z ⟶ Y) (t : LB.Gen (LB.LinComb L (fun k => e ≫ φ k) ε)) (ht : t.IsGen) :
    ∃ t : LB.Gen ((LB.LinComb L φ ε).pull e), t.IsGen := by
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull e).U J ≤ LB.wchart L (fun k => e ≫ φ k) (J PUnit.unit) :=
    fun J z hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hz) k
  refine ⟨⟨fun J => res (le J) (t.s (J PUnit.unit))⟩, fun J J' => unit_ext fun z hz => ?_⟩
  refine ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_pull_g _ e (𝟙 Z) z J J' hz.1 hz.2)
      ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.2 _)))).symm)
  refine (gen_trans ht (𝟙 Z) z (le J hz.1) (le J' hz.2)).trans (congrArg (· * _) (Eq.symm ?_))
  refine (gm_linComb L φ ε (𝟙 Z ≫ e) z _ _ (mem_pull.1 hz.1) (mem_pull.1 hz.2)).trans ?_
  simp only [trF, Category.assoc]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

variable (X) in

def aug (R : CommRingCat.{0}) : grpAlg X R ⟶ R :=
  CommRingCat.ofHom (AddMonoidAlgebra.lift R R X 1).toRingHom

theorem aug_single (R : CommRingCat.{0}) (x : X) (c : R) : (aug X R).hom (AddMonoidAlgebra.single x c) = c := by
  simp [aug]

theorem const_aug (R : CommRingCat.{0}) : const X R ≫ aug X R = 𝟙 R := by
  apply CommRingCat.hom_ext
  refine RingHom.ext fun r => ?_
  simp [const, aug]

variable (X Y) in

def unitSec : Y.left ⟶ (splitTorus S X ⊗ Y).left := (lift (1 : Y ⟶ splitTorus S X) (𝟙 Y)).left

theorem comp_unitSec {Z : Over S} (y : Z ⟶ Y) :
    y.left ≫ unitSec X Y = (lift (1 : Z ⟶ splitTorus S X) y).left := by
  rw [unitSec, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id]

theorem expand_aug {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    expand y ≫ aug X R = (unitSec X Y).appTop ≫ y.appTop ≫ (Scheme.ΓSpecIso R).hom := by
  have h1 : torusPoint (fromInt X R ≫ aug X R) (y ≫ Y.hom) = 1 := by
    have := torusPoint_mul (fromInt X R ≫ aug X R) (fromInt X R ≫ aug X R) (fromInt X R ≫ aug X R) (y ≫ Y.hom)
      fun x => by
        rw [CommRingCat.hom_comp, RingHom.comp_apply, fromInt_single, aug_single, _root_.mul_one]
    exact mul_eq_left.1 this
  have h2 : prodPoint (fromInt X R ≫ aug X R) y = y ≫ unitSec X Y := by
    rw [prodPoint, h1]
    exact (comp_unitSec (Over.homMk y rfl : Over.mk (y ≫ Y.hom) ⟶ Y)).symm
  rw [expand, value_comp, ← Spec.map_comp_assoc, const_aug, Spec.map_id, Category.id_comp, value, h2,
    Scheme.Hom.comp_appTop, Category.assoc]

theorem exists_char [Module.Free ℤ X] [IsIntegral Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : (unitSec X Y).appTop.hom ρ.val = 1) :
    ∃ χ : X, ρ.val = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val := by
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  have loc : ∀ p : Y.left, ∃ χ, IsCharNear ρ.val χ p := fun p => by
    obtain ⟨R, y, hy, q, hq⟩ : ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
        p ∈ Set.range y :=
      ⟨_, Y.left.affineOpenCover.f (Y.left.affineOpenCover.idx p), inferInstance,
        Y.left.affineOpenCover.covers p⟩
    have : Nonempty (Spec R) := ⟨q⟩
    have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion y
    have : IsDomain R := (affine_isIntegral_iff R).1 ‹_›
    obtain ⟨χ, c, -, hc⟩ := Rosenlicht.isUnit_eq_single (ρ.isUnit.map (expand y).hom)
    have e := congrArg (fun f => f.hom ρ.val) (expand_aug (X := X) y)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [hρ, map_one, map_one, hc, aug_single] at e
    exact ⟨χ, R, y, hy, ⟨q, hq⟩, e ▸ hc⟩
  choose c hc using loc
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    obtain ⟨R, y, hy, hp, he⟩ := hc p
    exact ⟨Set.range y, y.isOpenEmbedding.isOpen_range, hp,
      fun p' hp' => (hc p').unique ⟨R, y, hy, hp', he⟩⟩
  obtain ⟨p₀⟩ : Nonempty Y.left := inferInstance
  refine ⟨c p₀, ext_of_expand fun p => ?_⟩
  obtain ⟨R, y, hy, hp, he⟩ := hc p
  refine ⟨R, y, hy, hp, ?_⟩
  rw [he, expand_char, hlc.apply_eq_of_preconnectedSpace p p₀]

theorem pic_injective [Module.Free ℤ X] [IsAffine Y.left] [IsDomain Γ(Y.left, ⊤)] [IsIntegrallyClosed Γ(Y.left, ⊤)] :
    Function.Injective (CommRing.Pic.mapRingHom ((unitSec X Y).appLE ⊤ ⊤ le_top).hom) := by
  let R := Γ(Y.left, ⊤)
  let y : Spec R ⟶ Y.left := Y.left.isoSpec.inv
  have i1 : IsIso (prodPoint (fromInt X R) (Spec.map (const X R) ≫ y)) := (isPullback_expand (X := X) y).isIso_fst_of_isIso
  have i2 : IsIso (expand (X := X) y) := by
    have : IsIso (prodPoint (fromInt X R) (Spec.map (const X R) ≫ y)).appTop :=
      inferInstanceAs (IsIso ((prodPoint (fromInt X R) (Spec.map (const X R) ≫ y)).app ⊤))
    rw [expand, value]; infer_instance
  have cp : ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (M), CommRing.Pic.mapRingHom g.hom
      (CommRing.Pic.mapRingHom f.hom M) = CommRing.Pic.mapRingHom (f ≫ g).hom M :=
    fun f g M => CommRing.Pic.mapRingHom_mapRingHom
  have a : Function.Injective (CommRing.Pic.mapRingHom (expand (X := X) y).hom) := by
    apply Function.LeftInverse.injective (g := CommRing.Pic.mapRingHom (inv (expand (X := X) y)).hom)
    intro M
    rw [CommRing.Pic.mapRingHom_mapRingHom, ← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id,
      CommRing.Pic.mapRingHom_id_apply]
  have b : Function.Injective (CommRing.Pic.mapRingHom (aug X R).hom) := by
    have s : Function.Surjective (CommRing.Pic.mapRingHom (const X R).hom) := by
      have : CommRing.Pic.mapRingHom (const X R).hom = CommRing.Pic.mapAlgebra R (AddMonoidAlgebra R X) :=
        CommRing.Pic.mapRingHom_algebraMap
      rw [this]
      exact (pic_mapAlgebra_groupAlgebra_bijective R X).2
    intro M M' h
    obtain ⟨M, rfl⟩ := s M
    obtain ⟨M', rfl⟩ := s M'
    rw [cp, cp, const_aug, CommRingCat.hom_id, CommRing.Pic.mapRingHom_id_apply,
      CommRing.Pic.mapRingHom_id_apply] at h
    rw [h]
  have e : (unitSec X Y).appLE ⊤ ⊤ le_top = (unitSec X Y).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  intro M M' h
  apply a
  apply b
  rw [e] at h
  rw [cp, cp, expand_aug, ← cp, ← cp _ _ M', h]

section Values

variable {X₀ : Scheme.{0}} {L : LB X₀}

theorem exists_gen_of_rep (hL : L.IsLB) {W : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (W ⟶ X₀)) (ε : K → ℤ)
    {σ : Form W X₀} {F : Vals L W} (h : Rep L σ F)
    (e : ∀ (V : Type) [CommGroup V] k, σ V k = ∏ a, k (φ a) ^ ε a) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ ∀ Z r z J, Good L z J → val t r z J = F Z r z J := by
  obtain ⟨K', _, φ', ε', t, ht, hs, hv⟩ := h
  obtain ⟨t', ht', h'⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun V _ k => (hs V k).trans (e V k)) t ht
  exact ⟨t', ht', fun Z r z J hJ => (h' Z r z J hJ).trans (hv Z r z J hJ)⟩

theorem rep_val {W : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (W ⟶ X₀)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    Rep L (fun _ _ k => ∏ a, k (φ a) ^ ε a) (fun _ r z J => val t r z J) :=
  ⟨K, inferInstance, φ, ε, t, ht, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

def Normalised (F : Vals L (splitTorus S X ⊗ Y).left) : Prop :=
  ∀ (Z : Over S) (y : Z ⟶ Y) (z : Z.left) (J), Good L z J → F _ (lift (1 : Z ⟶ splitTorus S X) y).left z J = 1

theorem exists_char_of_rep [Module.Free ℤ X] [IsIntegral Y.left] (hL : L.IsLB)
    {F : Vals L (splitTorus S X ⊗ Y).left} (h : Rep L (fun _ _ _ => 1) F) (hn : Normalised F) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (z : Z.left) (J), Good L z J →
      F _ (lift t y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  obtain ⟨ρ, hρ⟩ := h.exists_unit hL
  have h1 : Units.map (unitSec X Y).appTop.hom.toMonoidHom ρ = 1 := unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := exists_good_pt hL z
    rw [← gm_top, map_one, hρ _ _ z J hJ]
    exact hn Y (𝟙 Y) z J hJ
  obtain ⟨χ, hχ⟩ := exists_char ρ (congrArg Units.val h1)
  refine ⟨χ, fun Z t y z J hJ => ?_⟩
  rw [← hρ _ _ z J hJ, gm_top]
  refine congrArg _ (Units.ext ?_)
  refine (congrArg (lift t y).left.appTop.hom hχ).trans ?_
  rw [chV_val, Rosenlicht.over_appTop_comp, lift_fst]

theorem char_eq_zero [Nonempty Y.left] {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (_ : Z ⟶ Y) (z : Z.left), gm (𝟙 Z.left) z ⊤ (chV t χ) = 1) :
    χ = 0 := by
  obtain ⟨p⟩ : Nonempty Y.left := inferInstance
  have h1 : chV (fst (splitTorus S X) Y) χ = 1 := unit_ext fun z _ =>
    (h _ _ (snd _ _) z).trans (map_one _).symm
  have h2 := expand_char (Y.left.fromSpecResidueField p) χ
  rw [← chV_val, h1, Units.val_one, map_one] at h2
  exact (eq_of_single_one_eq h2).symm

variable {K : Type} [Fintype K] (φ : K → ((splitTorus S X ⊗ Y).left ⟶ X₀)) (ε : K → ℤ)

def IsNormGen {A : Over S} (a : A ⟶ Y) (F : Vals L (splitTorus S X ⊗ A).left) : Prop :=
  Rep L (fun _ _ k => ∏ i, k ((splitTorus S X ◁ a).left ≫ φ i) ^ ε i) F ∧ Normalised F

variable {φ ε}

theorem exists_isNormGen [Module.Free ℤ X] (hL : L.IsLB)
    (h : ∀ (V : Type) [CommGroup V] (k : (Y.left ⟶ X₀) → V), ∏ i, k (unitSec X Y ≫ φ i) ^ ε i = 1)
    {A : Over S} (a : A ⟶ Y) [IsAffine A.left] [IsDomain Γ(A.left, ⊤)] [IsIntegrallyClosed Γ(A.left, ⊤)] :
    ∃ F : Vals L _, IsNormGen φ ε a F := by
  have e : unitSec X A ≫ (splitTorus S X ◁ a).left = a.left ≫ unitSec X Y := by
    rw [comp_unitSec, unitSec, ← Over.comp_left, lift_whiskerLeft, Category.id_comp]
  have h' : ∀ {W : Scheme.{0}} (r : W ⟶ A.left) (V : Type) [CommGroup V] (k : (W ⟶ X₀) → V),
      ∏ i, k (r ≫ unitSec X A ≫ (splitTorus S X ◁ a).left ≫ φ i) ^ ε i = 1 := fun r V _ k => by
    simp only [← Category.assoc (unitSec X A), e, Category.assoc]
    exact h V fun q => k (r ≫ a.left ≫ q)
  have : IsAffine (splitTorus S X ⊗ A).left := by
    have : IsAffineHom (snd (splitTorus S X) A).left := isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (splitTorus S X).hom A.hom) (Diag.isAffineHom_hom S X)
    exact isAffine_of_isAffineHom (snd (splitTorus S X) A).left
  obtain ⟨t₀, ht₀, -⟩ := exists_gen_of_rep hL (fun i => unitSec X A ≫ (splitTorus S X ◁ a).left ≫ φ i) ε
    (Rep.unit 1) fun V _ k => by simpa only [Category.id_comp] using (h' (𝟙 _) V k).symm
  obtain ⟨t, ht⟩ := exists_gen_of_pull (unitSec X A) pic_injective (LB.isLB_linComb hL _ ε)
    (exists_gen_pull (unitSec X A) t₀ ht₀)
  refine ⟨_, ((rep_val ht).mul ((rep_val ht).pull ((snd (splitTorus S X) A).left ≫ unitSec X A)).inv).congr
    fun V _ k => ?_, fun Z y z J hJ => ?_⟩
  · simp only [Category.assoc, h', inv_one, _root_.mul_one]
  · show _ * _ = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd, comp_unitSec, mul_inv_cancel]

theorem exists_inter [IsIntegral Y.left] {A B : Over S} (a : A ⟶ Y) (b : B ⟶ Y) [IsOpenImmersion a.left]
    [IsOpenImmersion b.left] [Nonempty A.left] [Nonempty B.left] :
    ∃ (C : Over S) (c : C ⟶ A) (d : C ⟶ B), IsOpenImmersion c.left ∧ Nonempty C.left ∧ c ≫ a = d ≫ b ∧
      ∀ (Z : Over S) (y : Z ⟶ A) (y' : Z ⟶ B), y ≫ a = y' ≫ b → ∃ w : Z ⟶ C, w ≫ c = y ∧ w ≫ d = y' := by
  refine ⟨Over.mk (pullback.fst a.left b.left ≫ A.hom), Over.homMk (pullback.fst _ _) rfl,
    Over.homMk (pullback.snd _ _) ?_, inferInstanceAs (IsOpenImmersion (pullback.fst a.left b.left)), ?_,
    Over.OverMorphism.ext pullback.condition, fun Z y y' h => ?_⟩
  · show _ = pullback.fst a.left b.left ≫ A.hom
    rw [← Over.w a, ← Over.w b, pullback.condition_assoc]
  · obtain ⟨_, ⟨p, rfl⟩, ⟨q, hq⟩⟩ := nonempty_preirreducible_inter a.left.isOpenEmbedding.isOpen_range
      b.left.isOpenEmbedding.isOpen_range (Set.range_nonempty _) (Set.range_nonempty _)
    obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback p q hq.symm
    exact ⟨z⟩
  · refine ⟨Over.homMk (pullback.lift y.left y'.left (congrArg (·.left) h)) ?_, Over.OverMorphism.ext
      (pullback.lift_fst _ _ _), Over.OverMorphism.ext (pullback.lift_snd _ _ _)⟩
    exact (pullback.lift_fst_assoc _ _ _ _).trans (Over.w y)

theorem exists_compare [Module.Free ℤ X] [IsIntegral Y.left] (hL : L.IsLB) {A B : Over S} {a : A ⟶ Y} {b : B ⟶ Y}
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] [Nonempty A.left] [Nonempty B.left] {F : Vals L _}
    {F' : Vals L _} (h : IsNormGen φ ε a F) (h' : IsNormGen φ ε b F') :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ A) (y' : Z ⟶ B), y ≫ a = y' ≫ b →
      ∀ (z : Z.left) (J), Good L z J →
        F _ (lift t y).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) * F' _ (lift t y').left z J := by
  obtain ⟨C, c, d, _, _, hcd, hl⟩ := exists_inter a b
  have : IsIntegral C.left := isIntegral_of_isOpenImmersion (c.left ≫ a.left)
  have e : ∀ {Z A : Over S} (t : Z ⟶ splitTorus S X) (w : Z ⟶ C) (c : C ⟶ A),
      (lift t w).left ≫ (splitTorus S X ◁ c).left = (lift t (w ≫ c)).left := fun t w c => by
    rw [← Over.comp_left, lift_whiskerLeft]
  obtain ⟨χ, hχ⟩ := exists_char_of_rep hL (((h.1.pull (splitTorus S X ◁ c).left).mul
    (h'.1.pull (splitTorus S X ◁ d).left).inv).congr fun V _ k => by
      simp only [← Category.assoc, ← Over.comp_left, ← whiskerLeft_comp, hcd, mul_inv_cancel])
    fun Z y z J hJ => by
      show _ * _ = _
      rw [e, e, h.2 Z _ z J hJ, h'.2 Z _ z J hJ, mul_inv_cancel]
  refine ⟨χ, fun Z t y y' hy z J hJ => ?_⟩
  obtain ⟨w, rfl, rfl⟩ := hl Z y y' hy
  rw [← hχ Z t w z J hJ, ← e, ← e, inv_mul_cancel_right]

theorem IsNormGen.twist {A : Over S} {a : A ⟶ Y} {F : Vals L _} (h : IsNormGen φ ε a F) (χ : X) :
    ∃ F' : Vals L _, IsNormGen φ ε a F' ∧ ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ A) (z : Z.left) (J),
      F' _ (lift t y).left z J = (gm (𝟙 Z.left) z ⊤ (chV t χ))⁻¹ * F _ (lift t y).left z J := by
  have e : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ A) (z : Z.left),
      gm ((lift t y).left ≫ (fst (splitTorus S X) A).left) z ⊤ (charUnit S X χ) = gm (𝟙 Z.left) z ⊤ (chV t χ) := fun Z t y z => by
    rw [← Over.comp_left, lift_fst, gm_charUnit]
  refine ⟨_, ⟨(((Rep.unit (charUnit S X χ)).pull (fst (splitTorus S X) A).left).inv.mul h.1).congr
    fun V _ k => by rw [inv_one, _root_.one_mul], fun Z y z J hJ => ?_⟩, fun Z t y z J => by rw [← e]⟩
  have o : chV (1 : Z ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl
  show _ * _ = _
  rw [e, o, map_one, inv_one, _root_.one_mul, h.2 Z y z J hJ]

theorem exists_normalised_gen [Module.Free ℤ X] [IsIntegral Y.left]
    (hY : ∀ U : Y.left.affineOpens, Nonempty U.1 → IsIntegrallyClosed Γ(U.1.toScheme, ⊤)) (hL : L.IsLB)
    (h : ∀ (V : Type) [CommGroup V] (k : (Y.left ⟶ X₀) → V), ∏ i, k (unitSec X Y ≫ φ i) ^ ε i = 1) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧ Normalised (L := L) fun _ r z J => val s r z J := by
  let I := {U : Y.left.affineOpens // Nonempty U.1}
  let A : I → Over S := fun U => Over.mk (U.1.1.ι ≫ Y.hom)
  let a : ∀ U, A U ⟶ Y := fun U => Over.homMk U.1.1.ι rfl
  have oa : ∀ U, IsOpenImmersion (a U).left := fun U => inferInstanceAs (IsOpenImmersion U.1.1.ι)
  have na : ∀ U, Nonempty (A U).left := fun U => U.2
  have cov : ∀ p : Y.left, ∃ U : I, p ∈ U.1.1 := fun p => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hp, -⟩ :=
      Y.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
    exact ⟨⟨⟨U, hU⟩, ⟨p, hp⟩⟩, hp⟩
  have loc : ∀ U, ∃ F : Vals L _, IsNormGen φ ε (a U) F := fun U => by
    have : IsAffine (A U).left := U.1.2
    have : IsIntegral (A U).left := isIntegral_of_isOpenImmersion (a U).left
    have : IsIntegrallyClosed Γ((A U).left, ⊤) := hY U.1 U.2
    exact exists_isNormGen hL h (a U)
  choose F₀ hF₀ using loc
  obtain ⟨U₀, -⟩ := cov (Classical.arbitrary _)
  have adj : ∀ U, ∃ F : Vals L _, IsNormGen φ ε (a U) F ∧ ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ A U)
      (y' : Z ⟶ A U₀), y ≫ a U = y' ≫ a U₀ → ∀ (z : Z.left) (J), Good L z J →
        F _ (lift t y).left z J = F₀ U₀ _ (lift t y').left z J := fun U => by
    obtain ⟨χ, hχ⟩ := exists_compare hL (hF₀ U) (hF₀ U₀)
    obtain ⟨F, hF, hv⟩ := (hF₀ U).twist χ
    exact ⟨F, hF, fun Z t y y' hy z J hJ => by rw [hv, hχ Z t y y' hy z J hJ, inv_mul_cancel_left]⟩
  choose F hF hv using adj
  have agr : ∀ U U' (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ A U) (y' : Z ⟶ A U'), y ≫ a U = y' ≫ a U' →
      ∀ (z : Z.left) (J), Good L z J → F U _ (lift t y).left z J = F U' _ (lift t y').left z J := fun U U' => by
    obtain ⟨χ, hχ⟩ := exists_compare hL (hF U) (hF U')
    obtain ⟨C, c, d, _, _, hcd, -⟩ := exists_inter (a U) (a U')
    have : IsOpenImmersion (c ≫ a U).left := inferInstanceAs (IsOpenImmersion (c.left ≫ (a U).left))
    obtain ⟨C', c', d', _, _, hcd', -⟩ := exists_inter (c ≫ a U) (a U₀)
    obtain rfl : χ = 0 := char_eq_zero (Y := C') fun Z t w z => by
      obtain ⟨J, hJ⟩ := exists_good_pt hL z
      have e := hχ Z t (w ≫ c' ≫ c) (w ≫ c' ≫ d) (by simp only [Category.assoc, hcd]) z J hJ
      rw [hv U Z t _ (w ≫ d') (by simp only [Category.assoc, ← hcd']) z J hJ,
        hv U' Z t _ (w ≫ d') (by simp only [Category.assoc, ← hcd', hcd]) z J hJ] at e
      exact (right_eq_mul.1 e)
    intro Z t y y' hy z J hJ
    rw [hχ Z t y y' hy z J hJ, chV_zero, map_one, _root_.one_mul]
  let W : I → (splitTorus S X ⊗ Y).left.Opens := fun U => (snd (splitTorus S X) Y).left ⁻¹ᵁ U.1.1
  let B : I → Over S := fun U => Over.mk ((W U).ι ≫ (splitTorus S X ⊗ Y).hom)
  let w : ∀ U, B U ⟶ splitTorus S X ⊗ Y := fun U => Over.homMk (W U).ι rfl
  have ey : ∀ U, ∃ y : B U ⟶ A U, y ≫ a U = w U ≫ snd _ _ := fun U =>
    ⟨Over.homMk ((snd (splitTorus S X) Y).left ∣_ U.1.1) (by
      show _ ≫ U.1.1.ι ≫ Y.hom = (W U).ι ≫ _
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w]),
      Over.OverMorphism.ext (morphismRestrict_ι _ _)⟩
  choose y hy using ey
  have em : ∀ U, (lift (w U ≫ fst _ _) (y U)).left ≫ (splitTorus S X ◁ a U).left = (W U).ι := fun U => by
    rw [← Over.comp_left, lift_whiskerLeft, hy, ← comp_lift, lift_fst_snd, Category.comp_id]; rfl
  have gl : ∀ U, ∃ t : LB.Gen (LB.LinComb L (fun i => (W U).ι ≫ φ i) ε), t.IsGen ∧ ∀ (Z : Over S) (r : Z ⟶ B U) z J,
      Good L z J → val t r.left z J = F U _ (lift (r ≫ w U ≫ fst _ _) (r ≫ y U)).left z J := fun U => by
    obtain ⟨t, ht, hv⟩ := exists_gen_of_rep hL (fun i => (W U).ι ≫ φ i) ε
      ((hF U).1.pull (lift (w U ≫ fst _ _) (y U)).left) fun V _ k => by simp only [← Category.assoc, em]
    refine ⟨t, ht, fun Z r z J hJ => (hv _ _ z J hJ).trans ?_⟩
    rw [← comp_lift]; rfl
  choose t ht htv using gl
  obtain ⟨s, hs, hsv⟩ := glue_gen hL φ ε W (fun p => cov _) t ht fun U U' Z r r' z J hJ hr => by
    let Z' : Over S := Over.mk (r ≫ (B U).hom)
    let ρ : Z' ⟶ B U := Over.homMk r rfl
    let ρ' : Z' ⟶ B U' := Over.homMk r' (by
      show r' ≫ (W U').ι ≫ _ = r ≫ (W U).ι ≫ _
      rw [← Category.assoc, ← hr, Category.assoc])
    have e : ρ ≫ w U = ρ' ≫ w U' := Over.OverMorphism.ext hr
    refine (htv U Z' ρ z J hJ).trans (Eq.trans ?_ (htv U' Z' ρ' z J hJ).symm)
    rw [← Category.assoc ρ', ← e, Category.assoc]
    exact agr U U' Z' _ _ _ (by rw [Category.assoc, Category.assoc, hy, hy, reassoc_of% e]) z J hJ
  refine ⟨s, hs, ?_⟩
  obtain ⟨ρ, hρ⟩ := (((rep_val hs).pull (unitSec X Y)).congr (σ' := fun _ _ _ => 1) fun V _ k => h V k).exists_unit hL
  have h1 : ρ = 1 := unit_ext fun p _ => by
    obtain ⟨U, hU⟩ := cov p
    let z : (A U).left := ⟨p, hU⟩
    obtain ⟨J, hJ⟩ := exists_good_pt hL z
    refine (gm_inj (a U).left z (U := ⊤) (U' := ⊤) trivial trivial (a := ρ) (b := 1) ?_)
    let r : A U ⟶ B U := Over.homMk (IsOpenImmersion.lift (W U).ι ((a U).left ≫ unitSec X Y) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      have : ((a U).left ≫ unitSec X Y) ≫ (snd (splitTorus S X) Y).left = (a U).left := by
        rw [comp_unitSec, ← Over.comp_left, lift_snd]
      exact (congrArg (fun m => m q ∈ U.1.1) this).mpr q.2)) (by
      refine (IsOpenImmersion.lift_fac_assoc _ _ _ _).trans ?_
      rw [comp_unitSec, Over.w])
    have hr : r ≫ w U = lift 1 (a U) :=
      Over.OverMorphism.ext ((IsOpenImmersion.lift_fac _ _ _).trans (comp_unitSec _))
    rw [hρ _ _ z J hJ, map_one, comp_unitSec, ← hr]
    refine (hsv U _ r.left z J hJ).trans ((htv U _ r z J hJ).trans ?_)
    rw [reassoc_of% hr, lift_fst]
    exact (hF U).2 _ _ z J hJ
  intro Z q z J hJ
  rw [← comp_unitSec]
  exact (hρ _ _ z J hJ).symm.trans (by rw [h1, map_one])

end Values

section Group

variable {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (i : splitTorus S X ⟶ G)

def lamForm {Z : Over S} (t : Z ⟶ splitTorus S X) (x : Z ⟶ G) : Form Z.left G.left := fun _ _ k =>
  k ((t ≫ i) * x).left * (k (t ≫ i).left)⁻¹ * (k x.left)⁻¹ * k (1 : Z ⟶ G).left

theorem prod_lam {Z : Over S} (t : Z ⟶ splitTorus S X) (x : Z ⟶ G) (V : Type) [CommGroup V]
    (k : (Z.left ⟶ G.left) → V) : ∏ a, k ((lift t x).left ≫ lamφ i a) ^ Oε a = lamForm i t x V k := by
  rw [Fin.prod_univ_four]
  show k (lift t x ≫ ((fst _ G ≫ i) * snd _ G)).left ^ (1 : ℤ) * k (lift t x ≫ fst _ G ≫ i).left ^ (-1 : ℤ) *
    k (lift t x ≫ snd _ G).left ^ (-1 : ℤ) * k (lift t x ≫ (1 : _ ⟶ G)).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_one]
  simp only [zpow_neg, zpow_one, lamForm]

theorem rep_lam {s : LB.Gen (LB.LinComb L.L (lamφ i) Oε)} (hs : s.IsGen) {Z : Over S} (t : Z ⟶ splitTorus S X)
    (x : Z ⟶ G) : Rep L.L (lamForm i t x) fun _ r z J => val s (r ≫ (lift t x).left) z J :=
  ((rep_val hs).pull (lift t x).left).congr fun V _ k => prod_lam i t x V k

theorem rep_cub {Z : Over S} (x y u : Z ⟶ G) : Rep L.L (fun _ _ h =>
      h (x * y * u).left * (h (x * y).left)⁻¹ * (h (x * u).left)⁻¹ * (h (y * u).left)⁻¹ * h x.left * h y.left *
        h u.left * (h (1 : Z ⟶ G).left)⁻¹)
    fun _ r z J => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t (r ≫ (lift x (lift y u)).left) z J :=
  ((rep_val (φ := thφ G (x3 G)) (ε := thε) c.isGen).pull (lift x (lift y u)).left).congr fun _ _ k => prod_cub x y u k

theorem nonempty_biTriv [Module.Free ℤ X] [IsMonHom i] [IsIntegral (splitTorus S X ⊗ G).left] [IsIntegral (G ⊗ G).left]
    {s : LB.Gen (LB.LinComb L.L (lamφ i) Oε)} (hs : s.IsGen)
    (h₁ : Normalised (L := L.L) fun _ r z J => val s r z J)
    (h₂ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left) (J), Good L.L z J →
      val s (lift t (1 : Z ⟶ G)).left z J = 1) : Nonempty (BiTriv c i) := by
  have key : ∀ (Y : Over S) [IsIntegral Y.left] (t t₁ t₂ : splitTorus S X ⊗ Y ⟶ splitTorus S X)
      (x x₁ x₂ a b d : splitTorus S X ⊗ Y ⟶ G),
      (∀ (V : Type) [CommGroup V] (h : (_ ⟶ G.left) → V), lamForm i t x V h * (h (a * b * d).left * (h (a * b).left)⁻¹ *
        (h (a * d).left)⁻¹ * (h (b * d).left)⁻¹ * h a.left * h b.left * h d.left *
        (h (1 : splitTorus S X ⊗ Y ⟶ G).left)⁻¹ * lamForm i t₁ x₁ V h * lamForm i t₂ x₂ V h)⁻¹ = 1) →
      ∀ P : ∀ Z : Over S, (Z ⟶ splitTorus S X ⊗ Y) → ∀ z : Z.left, ((Z.left ⟶ G.left) → L.L.ι) → Prop,
      (∀ Z r z J, P Z r z J ↔ val s (lift (r ≫ t) (r ≫ x)).left z J = cubV c z J (r ≫ a) (r ≫ b) (r ≫ d) *
        val s (lift (r ≫ t₁) (r ≫ x₁)).left z J * val s (lift (r ≫ t₂) (r ≫ x₂)).left z J) →
      (∀ Z y z J, Good L.L z J → P Z (lift 1 y) z J) →
      (∀ Z τ, ∃ y, ∀ z J, Good L.L z J → P Z (lift τ y) z J) →
      ∀ Z τ y z J, Good L.L z J → P Z (lift τ y) z J := by
    intro Y _ t t₁ t₂ x x₁ x₂ a b d hF P hP p₁ p₂
    have R := ((rep_lam i hs t x).mul (((rep_cub c a b d).mul (rep_lam i hs t₁ x₁)).mul
      (rep_lam i hs t₂ x₂)).inv).congr (σ' := fun _ _ _ => 1) hF
    have hP' : ∀ (Z : Over S) (r : Z ⟶ splitTorus S X ⊗ Y) z J, P Z r z J ↔ val s (r.left ≫ (lift t x).left) z J *
        (val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t (r.left ≫ (lift a (lift b d)).left) z J *
          val s (r.left ≫ (lift t₁ x₁).left) z J * val s (r.left ≫ (lift t₂ x₂).left) z J)⁻¹ = 1 := fun Z r z J => by
      rw [hP, mul_inv_eq_one]
      simp only [← Over.comp_left, comp_lift, cubV]
    obtain ⟨χ, hχ⟩ := exists_char_of_rep L.isLB R fun Z y z J hJ => (hP' _ _ _ _).1 (p₁ Z y z J hJ)
    intro Z τ y z J hJ
    obtain ⟨y', hy'⟩ := p₂ Z τ
    exact (hP' _ _ _ _).2 ((hχ Z τ y z J hJ).trans ((hχ Z τ y' z J hJ).symm.trans ((hP' _ _ _ _).1 (hy' z J hJ))))
  refine ⟨⟨s, hs, fun Z t t' x z J hJ => ?_, fun Z t x x' z J hJ => ?_⟩⟩
  · have := key (splitTorus S X ⊗ G) (fst _ _ * (snd _ _ ≫ fst _ _)) (fst _ _) (snd _ _ ≫ fst _ _)
      (snd _ _ ≫ snd _ _) (snd _ _ ≫ snd _ _) (snd _ _ ≫ snd _ _) (fst _ _ ≫ i) ((snd _ _ ≫ fst _ _) ≫ i)
      (snd _ _ ≫ snd _ _) (fun V _ h => by
        simp only [lamForm, MonObj.mul_comp]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel) _ (fun _ _ _ _ => Iff.rfl)
      (fun Z y z J hJ => by
        have e := h₁ Z (y ≫ snd _ _) z J hJ
        simp only [MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, MonObj.one_comp,
          (isCub_cubV c hJ).face, _root_.one_mul] at e ⊢
        rw [e, _root_.one_mul])
      (fun Z τ => ⟨lift 1 1, fun z J hJ => by
        simp only [MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, MonObj.one_comp,
          (isCub_cubV c hJ).face₃, _root_.one_mul, _root_.mul_one, h₂ Z _ z J hJ]⟩) Z t (lift t' x) z J hJ
    simpa only [MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using this
  · have := key (G ⊗ G) (fst _ _) (fst _ _) (fst _ _) ((snd _ _ ≫ fst _ _) * (snd _ _ ≫ snd _ _))
      (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) (fst _ _ ≫ i) (snd _ _ ≫ fst _ _)
      (snd _ _ ≫ snd _ _) (fun V _ h => by
        simp only [lamForm, _root_.mul_assoc (fst (splitTorus S X) (G ⊗ G) ≫ i)]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel) _ (fun _ _ _ _ => Iff.rfl)
      (fun Z y z J hJ => by
        have e : ∀ x, val s (lift (1 : Z ⟶ splitTorus S X) x).left z J = 1 := fun x => h₁ Z x z J hJ
        simp only [lift_fst_assoc, lift_fst, MonObj.one_comp, (isCub_cubV c hJ).face, _root_.one_mul, e])
      (fun Z τ => ⟨lift 1 1, fun z J hJ => by
        simp only [MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, MonObj.one_comp,
          (isCub_cubV c hJ).face₃, _root_.one_mul, _root_.mul_one, h₂ Z _ z J hJ]⟩) Z t (lift x x') z J hJ
    simpa only [MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using this

end Group

theorem main : (∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus _ X ⟶ G), IsMonHom i → Nonempty (BiTriv c i)) := by
  intro k _ X _ _ _ G _ _ _ _ L c i _
  obtain ⟨c₁, c₂⟩ := GroupConn.connectedSpace_group _ G
  obtain ⟨c₃, c₄⟩ := c₂ X G c₁
  have : IsIntegral G.left := isIntegral_of_smooth_field_of_connectedSpace G.hom
  have : Smooth (splitTorus (Spec (CommRingCat.of k)) X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Spec (CommRingCat.of k)) X).hom G.hom ≫ _))
  have : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ _))
  have : IsIntegral (splitTorus (Spec (CommRingCat.of k)) X ⊗ G).left :=
    isIntegral_of_smooth_field_of_connectedSpace (splitTorus (Spec (CommRingCat.of k)) X ⊗ G).hom
  have : IsIntegral (G ⊗ G).left := isIntegral_of_smooth_field_of_connectedSpace (G ⊗ G).hom
  obtain ⟨s, hs, hn⟩ := exists_normalised_gen (φ := lamφ i) (ε := Oε) (fun U hU => by
      have : IsAffine U.1.toScheme := U.2
      have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
      have h := (HasRingHomProperty.appTop (P := @Smooth) (U.1.ι ≫ G.hom) inferInstance)
      algebraize [(U.1.ι ≫ G.hom).appTop.hom]
      have : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
        IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
      exact isIntegrallyClosed_of_smooth Γ(Spec (CommRingCat.of k), ⊤) _) L.isLB fun V _ h => by
    refine (prod_lam i 1 (𝟙 G) V h).trans ?_
    simp [lamForm]
  have R := (rep_val hs).mul (rep_lam i hs (fst (splitTorus _ X) G) 1).inv
  obtain ⟨s', hs', hv⟩ := exists_gen_of_rep L.isLB (lamφ i) Oε R fun V _ h => by simp [lamForm]
  have hv' : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ splitTorus _ X) (x : Z ⟶ G) z J, Good L.L z J →
      val s' (lift t x).left z J = val s (lift t x).left z J * (val s (lift t (1 : Z ⟶ G)).left z J)⁻¹ :=
    fun Z t x z J hJ => by rw [hv _ _ z J hJ, ← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one]
  refine nonempty_biTriv c i hs' (fun Z y z J hJ => (hv' Z 1 y z J hJ).trans ?_) fun Z t z J hJ => ?_
  · exact mul_inv_eq_one.2 ((hn Z y z J hJ).trans (hn Z 1 z J hJ).symm)
  · rw [hv' Z t 1 z J hJ, mul_inv_cancel]

end GlobalTheory.BiextTriv
end
