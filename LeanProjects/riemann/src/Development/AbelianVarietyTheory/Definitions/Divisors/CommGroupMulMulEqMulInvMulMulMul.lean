import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open GlobalTheory.TopForm (le_preimage_inf)

variable {k k' : Type} [CommRing k] [CommRing k'] {Y T : Scheme.{0}}

abbrev ger {U : Y.Opens} (y : Y) (hy : y ∈ U) : Γ(Y, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ U y hy).hom

theorem memInf {U V : Y.Opens} {y : Y} (h : y ∈ U) (h' : y ∈ V) : y ∈ U ⊓ V := ⟨h, h'⟩

@[simp] theorem ger_resG {U V : Y.Opens} (h : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)) :
    ger y hy (resG Y h a) = ger y (h hy) a :=
  TopCat.Presheaf.germ_res_apply Y.presheaf _ y hy a

theorem fun_ext_ger {U : Y.Opens} {a b : Γ(Y, U)} (h : ∀ y hy, ger y hy a = ger y hy b) : a = b :=
  TopCat.Presheaf.section_ext Y.sheaf U a b h

theorem ger_appLE (r : T ⟶ Y) {U : Y.Opens} {W : T.Opens} (h : W ≤ r ⁻¹ᵁ U) (z : T) (hz : z ∈ W)
    (a : Γ(Y, U)) : ger z hz ((r.appLE U W h).hom a) = (r.stalkMap z).hom (ger (r z) (h hz) a) := by
  rw [← resG_app, ger_resG]
  exact (Scheme.Hom.germ_stalkMap_apply r U z (h hz) a).symm

abbrev tr (B : LB Y) (y : Y) (i j : B.ι) : (Y.presheaf.stalk y)ˣ :=
  gm (𝟙 Y) y (B.U i ⊓ B.U j) (B.g i j)

theorem val_tr (B : LB Y) (y : Y) {i j : B.ι} (h : y ∈ B.U i ⊓ B.U j) :
    (tr B y i j).val = ger y h (B.g i j).val := gm_val (𝟙 Y) y _ h _

theorem tr_tens (A B : LB Y) (y : Y) {a b : (tens A B).ι} (ha : y ∈ (tens A B).U a)
    (hb : y ∈ (tens A B).U b) : tr (tens A B) y a b = tr A y a.1 b.1 * tr B y a.2 b.2 :=
  gm_tens A B (𝟙 Y) y a b ha hb

theorem tr_div (A B : LB Y) (y : Y) {a b : (LB.div A B).ι} (ha : y ∈ (LB.div A B).U a)
    (hb : y ∈ (LB.div A B).U b) : tr (LB.div A B) y a b = tr A y a.1 b.1 * (tr B y a.2 b.2)⁻¹ :=
  gm_div' A B (𝟙 Y) y a b ha hb

theorem tr_zpow (L : LB Y) (n : ℤ) (y : Y) {a b : (lbZPow L n).ι} (ha : y ∈ (lbZPow L n).U a)
    (hb : y ∈ (lbZPow L n).U b) :
    tr (lbZPow L n) y a b = tr L y (a PUnit.unit) (b PUnit.unit) ^ n :=
  (gm_linComb L _ _ (𝟙 Y) y a b ha hb).trans (by rw [Fintype.prod_unique, Category.id_comp])

theorem tr_pull (B : LB Y) (r : T ⟶ Y) (z : T) {a b : (B.pull r).ι} (ha : z ∈ (B.pull r).U a)
    (hb : z ∈ (B.pull r).U b) : tr (B.pull r) z a b =
      Units.map (r.stalkMap z).hom.toMonoidHom (tr B (r z) (a PUnit.unit) (b PUnit.unit)) := by
  have h : r z ∈ B.U (a PUnit.unit) ⊓ B.U (b PUnit.unit) := ⟨mem_pull.1 ha, mem_pull.1 hb⟩
  refine Units.ext ((val_tr _ z (memInf ha hb)).trans ?_)
  have e := congrArg (ger z (memInf ha hb)) (resG_pull_g r a b le_rfl)
  rw [resG_self, ger_appLE] at e
  exact e.trans (congrArg (r.stalkMap z).hom (val_tr B _ h).symm)

def H0 (_p : Y ⟶ Sp k) (B : LB Y) (O : Y.Opens) : Type := Γ(toMod B, O)

namespace H0

variable {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens}

instance : AddCommGroup (H0 p B O) := inferInstanceAs (AddCommGroup Γ(toMod B, O))

instance moduleFun : Module Γ(Y, O) (H0 p B O) := inferInstanceAs (Module Γ(Y, O) Γ(toMod B, O))

instance moduleBase : Module k (H0 p B O) := Module.compHom _ (algX p O)

theorem base_smul (c : k) (f : H0 p B O) : c • f = algX p O c • f := rfl

def loc (f : H0 p B O) (i : B.ι) : Γ(Y, O ⊓ B.U i) := coord (L := B) f i

def germ (i : B.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ B.U i) : H0 p B O →+ Y.presheaf.stalk y where
  toFun f := ger y (memInf hy hi) (f.loc i)
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _

theorem germ_apply (i : B.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ B.U i) (f : H0 p B O) :
    germ i y hy hi f = ger y (memInf hy hi) (f.loc i) := rfl

theorem germ_fun_smul (i : B.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ B.U i) (a : Γ(Y, O))
    (f : H0 p B O) : germ i y hy hi (a • f) = ger y hy a * germ i y hy hi f :=
  (map_mul (ger y (memInf hy hi)) (resG Y inf_le_left a) (f.loc i)).trans
    (congrArg (· * _) (ger_resG _ _ _ _))

variable (p) in

def const (y : Y) : k →+* Y.presheaf.stalk y := (ger (U := ⊤) y trivial).comp (algX p ⊤)

theorem ger_algX (y : Y) (hy : y ∈ O) (c : k) : ger y hy (algX p O c) = const p y c := by
  rw [← TopForm.resG_comp_algX p (le_top : O ≤ ⊤), RingHom.comp_apply, ger_resG]
  rfl

theorem germ_smul (i : B.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ B.U i) (c : k) (f : H0 p B O) :
    germ i y hy hi (c • f) = const p y c * germ i y hy hi f := by
  rw [base_smul, germ_fun_smul, ger_algX]

theorem germ_change (i j : B.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ B.U i) (hj : y ∈ B.U j)
    (f : H0 p B O) : germ i y hy hi f = tr B y i j * germ j y hy hj f := by
  have e := congrArg (ger y (memInf (memInf hy hi) hj)) (coord_rel (L := B) f i j
    inf_le_left (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right))
  rw [map_mul, ger_resG, ger_resG, ger_resG] at e
  rw [val_tr B y (memInf hi hj)]
  exact e

theorem ext_germ {f f' : H0 p B O}
    (h : ∀ y (hy : y ∈ O), ∃ i hi, germ i y hy hi f = germ i y hy hi f') : f = f' :=
  sec_ext fun j => fun_ext_ger fun y hy => by
    obtain ⟨i, hi, e⟩ := h y hy.1
    change germ j y hy.1 hy.2 f = germ j y hy.1 hy.2 f'
    rw [germ_change j i y _ _ hi, germ_change j i y _ _ hi f', e]

def restr (h : O' ≤ O) : H0 p B O →ₗ[k] H0 p B O' where
  toFun f := (toMod B).presheaf.map (homOfLE h).op f
  map_add' _ _ := map_add _ _ _
  map_smul' c f := (map_smul_resG h _ _).trans
    (congrArg (· • _) (DFunLike.congr_fun (TopForm.resG_comp_algX p h) c))

@[simp] theorem germ_restr (h : O' ≤ O) (i : B.ι) (y : Y) (hy : y ∈ O') (hi : y ∈ B.U i)
    (f : H0 p B O) : germ i y hy hi (restr h f) = germ i y (h hy) hi f :=
  ger_resG (inf_le_inf_right _ h) y _ _

variable (p) in

def ofSec (O : Y.Opens) : LB.Sec B →+ H0 p B O where
  toFun σ := LB.ofSec σ O
  map_zero' := sec_ext fun _ => map_zero _
  map_add' _ _ := sec_ext fun _ => map_add _ _ _

@[simp] theorem germ_ofSec (i : B.ι) (y : Y) (hy : y ∈ O) (hi : y ∈ B.U i) (σ : LB.Sec B) :
    germ i y hy hi (ofSec p O σ) = ger y hi (σ.f i) :=
  ger_resG inf_le_right y _ _

@[simp] theorem restr_ofSec (h : O' ≤ O) (σ : LB.Sec B) : restr h (ofSec p O σ) = ofSec p O' σ :=
  map_ofSec σ h

theorem ofSec_smul (c : k) (σ : LB.Sec B) : ofSec p O (algX p ⊤ c • σ) = c • ofSec p O σ :=
  sec_ext fun i => fun_ext_ger fun y hy => by
    change germ i y hy.1 hy.2 _ = germ i y hy.1 hy.2 _
    rw [germ_smul, germ_ofSec, germ_ofSec, smul_f, map_mul, ger_resG, ger_algX]

theorem bijective_ofSec_top : Function.Bijective (ofSec p (B := B) ⊤) :=
  (globalEquiv B).symm.bijective

theorem finrank_top {E : Type} [Field E] (p : Y ⟶ Sp E) (B : LB Y) :
    letI := algebraΓOfHom p
    Module.finrank E (H0 p B ⊤) = lbH0 E B := by
  letI := algebraΓOfHom p
  letI : Module E B.Sec := Module.compHom _ (algebraMap E Γ(Y, ⊤))
  haveI : IsScalarTower E Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _
  have e (c : E) : algebraMap E Γ(Y, ⊤) c = algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [lineBundleGlobalSectionsDim_eq_finrank]
  exact (LinearEquiv.ofBijective
    { ofSec p ⊤ with map_smul' := fun c σ => (e c ▸ ofSec_smul c σ :) } bijective_ofSec_top).finrank_eq.symm

theorem exists_of_germs (hB : B.IsLB) {τ : Type*} (V : τ → Y.Opens) (c : τ → B.ι)
    (hO : ∀ t, V t ≤ O) (hc : ∀ t, V t ≤ B.U (c t)) (cover : ∀ y ∈ O, ∃ t, y ∈ V t)
    (u : ∀ t, Γ(Y, V t))
    (rule : ∀ y t t' (h : y ∈ V t) (h' : y ∈ V t'),
      ger y h (u t) = tr B y (c t) (c t') * ger y h' (u t')) :
    ∃ f : H0 p B O, ∀ t y (h : y ∈ V t), germ (c t) y (hO t h) (hc t h) f = ger y h (u t) := by
  let s (t : τ) : H0 p B (V t) := (chartEquiv hB (c t) (hc t)).symm (u t)
  have hs (t y) (h : y ∈ V t) : germ (c t) y h (hc t h) (s t) = ger y h (u t) := by
    conv_rhs => rw [← (chartEquiv hB (c t) (hc t)).apply_symm_apply (u t), chartEquiv_apply, ger_resG]
    rfl
  obtain ⟨f, hf⟩ := exists_mod_of_cover (F := toMod B) V hO
    (fun y hy => Opens.mem_iSup.2 (cover y hy)) s fun t t' => ext_germ (p := p) fun y hy =>
      ⟨c t, hc t hy.1, (germ_restr inf_le_left _ _ _ _ (s t)).trans <| Eq.symm <|
        (germ_restr inf_le_right _ _ _ _ (s t')).trans <| by
          rw [germ_change _ (c t') y _ _ (hc t' hy.2), hs, hs, rule y t t' hy.1 hy.2]⟩
  exact ⟨f, fun t y h => by rw [← hs t y h, ← hf t]; exact (germ_restr (hO t) _ _ _ _ f).symm⟩

def pullSL (r : T ⟶ Y) {q : T ⟶ Sp k'} {φ : k →+* k'} (hq : r ≫ p = q ≫ spMap φ) {W : T.Opens}
    (h : W ≤ r ⁻¹ᵁ O) : H0 p B O →ₛₗ[φ] H0 q (B.pull r) W where
  toFun f := restr (p := q) h (pullSec B r O f)
  map_add' f g := (congrArg (restr (p := q) h) ((pullSec B r O).map_add f g)).trans (map_add _ _ _)
  map_smul' c f := by
    have e : (r.appLE O W h).hom (algX p O c) = algX q W (φ c) := by
      have e₁ := Scheme.Hom.appLE_comp_appLE r p ⊤ O W le_top h
      have e₂ := Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ W le_top le_top
      have e₃ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at e₃
      simp only [hq] at e₁
      have e₄ := congrArg (· ≫ q.appLE ⊤ W le_top) e₃
      have e₅ := (e₄.trans (Category.assoc _ _ _)).trans (congrArg (_ ≫ ·) (e₂.trans e₁.symm))
      exact (congrArg (fun g => g.hom c) e₅).symm
    refine (congrArg (restr (p := q) h) ((pullSec B r O).map_smulₛₗ (algX p O c) f)).trans ?_
    exact (map_smul_resG (F := toMod (B.pull r)) h _ _).trans
      (congrArg (· • _) ((resG_app r h _).trans e))

theorem germ_pullSL (r : T ⟶ Y) {q : T ⟶ Sp k'} {φ : k →+* k'} (hq : r ≫ p = q ≫ spMap φ)
    {W : T.Opens} (h : W ≤ r ⁻¹ᵁ O) (j : (B.pull r).ι) (z : T) (hz : z ∈ W)
    (hj : z ∈ (B.pull r).U j) (f : H0 p B O) : germ j z hz hj (pullSL r hq h f) =
      (r.stalkMap z).hom (germ (j PUnit.unit) (r z) (h hz) (mem_pull.1 hj) f) :=
  (germ_restr h _ _ _ _ _).trans (ger_appLE r (pull_inf_le r O j) z _ _)

def pull (r : T ⟶ Y) {W : T.Opens} (h : W ≤ r ⁻¹ᵁ O) :
    H0 p B O →ₗ[k] H0 (r ≫ p) (B.pull r) W :=
  pullSL r (φ := RingHom.id k) (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) h

theorem germ_pull (r : T ⟶ Y) {W : T.Opens} (h : W ≤ r ⁻¹ᵁ O) (j : (B.pull r).ι) (z : T)
    (hz : z ∈ W) (hj : z ∈ (B.pull r).U j) (f : H0 p B O) : germ j z hz hj (pull r h f) =
      (r.stalkMap z).hom (germ (j PUnit.unit) (r z) (h hz) (mem_pull.1 hj) f) :=
  germ_pullSL r _ h j z hz hj f

@[simp] theorem pull_restr (r : T ⟶ Y) {W : T.Opens} (h' : O' ≤ O) (h : W ≤ r ⁻¹ᵁ O')
    (f : H0 p B O) : pull r h (restr h' f) = pull r (h.trans (r.preimage_mono h')) f :=
  sec_ext fun i => fun_ext_ger fun y hy => by
    change germ i y hy.1 hy.2 _ = germ i y hy.1 hy.2 _
    rw [germ_pull, germ_pull]
    exact congrArg _ (germ_restr _ _ _ _ _ _)

theorem stalkMap_const (r : T ⟶ Y) (z : T) (c : k) :
    (r.stalkMap z).hom (const p (r z) c) = const (r ≫ p) z c := by
  refine (ger_appLE r (U := ⊤) (W := ⊤) le_top z trivial _).symm.trans (congrArg (ger z _) ?_)
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE r p ⊤ ⊤ ⊤ le_top le_top)

section Val

variable {R : Type} [CommRing R]

def val (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) : H0 p B O →+ R where
  toFun f := evalPt x (O ⊓ B.U i) (le_preimage_inf hO hi) (f.loc i)
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _

theorem val_apply (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (f : H0 p B O) : val x i hO hi f = evalPt x (O ⊓ B.U i) (le_preimage_inf hO hi) (f.loc i) := rfl

theorem val_change (x : Sp R ⟶ Y) (i j : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ B.U j) (f : H0 p B O) : val x i hO hi f =
      evalPt x (B.U i ⊓ B.U j) (le_preimage_inf hi hj) (B.g i j).val * val x j hO hj f := by
  have e := congrArg (evalPt x (O ⊓ B.U i ⊓ B.U j) (le_preimage_inf (le_preimage_inf hO hi) hj)) (coord_rel (L := B)
    f i j inf_le_left (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_right))
  rwa [map_mul, evalPt_res x _ (le_preimage_inf hO hi), evalPt_res x _ (le_preimage_inf hi hj),
    evalPt_res x _ (le_preimage_inf hO hj)] at e

theorem val_fun_smul (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (a : Γ(Y, O)) (f : H0 p B O) : val x i hO hi (a • f) = evalPt x O hO a * val x i hO hi f :=
  (map_mul (evalPt x _ (le_preimage_inf hO hi)) (resG Y inf_le_left a) (f.loc i)).trans
    (congrArg (· * _) (evalPt_res x _ hO _ a))

theorem val_ofSec (x : Sp R ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (σ : LB.Sec B) : val x i hO hi (ofSec p O σ) = evalPt x _ hi (σ.f i) :=
  evalPt_res x inf_le_right hi _ _

theorem val_pull (r : T ⟶ Y) {W : T.Opens} (h : W ≤ r ⁻¹ᵁ O) (x : Sp R ⟶ T) (j : (B.pull r).ι)
    (hW : ⊤ ≤ x ⁻¹ᵁ W) (hj : ⊤ ≤ x ⁻¹ᵁ (B.pull r).U j) (hO : ⊤ ≤ (x ≫ r) ⁻¹ᵁ O)
    (hi : ⊤ ≤ (x ≫ r) ⁻¹ᵁ B.U (j PUnit.unit)) (f : H0 p B O) :
    val x j hW hj (pull r h f) = val (x ≫ r) (j PUnit.unit) hO hi f := by
  have e := Scheme.Hom.appLE_comp_appLE x r (O ⊓ B.U (j PUnit.unit)) (W ⊓ (B.pull r).U j) ⊤
    ((inf_le_inf_right _ h).trans (pull_inf_le r O j)) (le_preimage_inf hW hj)
  refine (congrArg (evalPt x _ (le_preimage_inf hW hj)) (resG_appLE r (pull_inf_le r O j)
    (inf_le_inf_right _ h) (f.loc _))).trans ?_
  exact congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom (f.loc _)) e

end Val

end H0

open H0

def NowhereZero {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (f : H0 p B O) : Prop :=
  ∀ y hy i hi, IsUnit (germ i y hy hi f)

theorem nowhereZero_of_exists {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} {f : H0 p B O}
    (h : ∀ y (hy : y ∈ O), ∃ i hi, IsUnit (germ i y hy hi f)) : NowhereZero f := fun y hy j hj => by
  obtain ⟨i, hi, e⟩ := h y hy
  rw [germ_change j i y hy hj hi]
  exact (Units.isUnit _).mul e

theorem isUnit_ger_iff {B : LB Y} (σ : LB.Sec B) {y : Y} {i : B.ι} (hi : y ∈ B.U i) :
    IsUnit (ger y hi (σ.f i)) ↔ y ∈ nonzeroLocus σ :=
  (Y.mem_basicOpen _ y hi).symm.trans (mem_nonzeroLocus_iff_basicOpen σ hi).symm

theorem nowhereZero_pull_ofSec {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (σ : LB.Sec B) (r : T ⟶ Y)
    {W : T.Opens} (h : W ≤ r ⁻¹ᵁ O) (hσ : W ≤ r ⁻¹ᵁ nonzeroLocus σ) :
    NowhereZero (H0.pull r h (H0.ofSec p O σ)) := fun z hz i hi => by
  rw [germ_pull]
  exact IsUnit.map _ ((germ_ofSec (p := p) _ _ (h hz) _ σ).symm ▸ (isUnit_ger_iff σ _).2 (hσ hz))

structure ProdChart (P B N : LB Y) where

  isLB₁ : P.IsLB

  isLB₂ : B.IsLB

  isLB₃ : N.IsLB

  τ : Type

  a : τ → P.ι

  b : τ → B.ι

  c : τ → N.ι

  cover : ∀ y, ∃ t, y ∈ P.U (a t) ∧ y ∈ B.U (b t) ∧ y ∈ N.U (c t)

  rule : ∀ y t t', y ∈ P.U (a t) ∧ y ∈ B.U (b t) ∧ y ∈ N.U (c t) →
    y ∈ P.U (a t') ∧ y ∈ B.U (b t') ∧ y ∈ N.U (c t') →
      tr N y (c t) (c t') = tr P y (a t) (a t') * tr B y (b t) (b t')

namespace ProdChart

variable {p : Y ⟶ Sp k} {P B N : LB Y} {O O' : Y.Opens} (C : ProdChart P B N)

theorem exists_mul (σ : H0 p P O) (f : H0 p B O) : ∃ g : H0 p N O, ∀ t y hy ha hb hc,
    germ (C.c t) y hy hc g = germ (C.a t) y hy ha σ * germ (C.b t) y hy hb f := by
  obtain ⟨g, hg⟩ := exists_of_germs (p := p) (O := O) C.isLB₃
    (fun t => ((O ⊓ P.U (C.a t)) ⊓ (O ⊓ B.U (C.b t))) ⊓ N.U (C.c t)) C.c
    (fun _ => inf_le_left.trans (inf_le_left.trans inf_le_left)) (fun _ => inf_le_right)
    (fun y hy => (C.cover y).imp fun _ h => ⟨⟨⟨hy, h.1⟩, hy, h.2.1⟩, h.2.2⟩)
    (fun t => resG Y (inf_le_left.trans inf_le_left) (σ.loc _) *
      resG Y (inf_le_left.trans inf_le_right) (f.loc _))
    fun y t t' h h' => by
      simp only [map_mul, ger_resG]
      rw [C.rule y t t' ⟨h.1.1.2, h.1.2.2, h.2⟩ ⟨h'.1.1.2, h'.1.2.2, h'.2⟩, Units.val_mul,
        mul_mul_mul_comm]
      exact congrArg₂ (· * ·) (germ_change _ _ y h.1.1.1 h.1.1.2 h'.1.1.2 σ)
        (germ_change _ _ y h.1.1.1 h.1.2.2 h'.1.2.2 f)
  refine ⟨g, fun t y hy ha hb hc => (hg t y (memInf (memInf (memInf hy ha) (memInf hy hb)) hc)).trans ?_⟩
  rw [map_mul, ger_resG, ger_resG]
  rfl

theorem sec_ext {g g' : H0 p N O} (h : ∀ t y hy, y ∈ P.U (C.a t) → y ∈ B.U (C.b t) → ∀ hc,
    germ (C.c t) y hy hc g = germ (C.c t) y hy hc g') : g = g' :=
  ext_germ fun y hy => let ⟨t, ht⟩ := C.cover y; ⟨C.c t, ht.2.2, h t y hy ht.1 ht.2.1 ht.2.2⟩

def mulFun (σ : H0 p P O) (f : H0 p B O) : H0 p N O := (C.exists_mul σ f).choose

theorem germ_mulFun (σ : H0 p P O) (f : H0 p B O) (t : C.τ) (y : Y) (hy : y ∈ O)
    (ha : y ∈ P.U (C.a t)) (hb : y ∈ B.U (C.b t)) (hc : y ∈ N.U (C.c t)) :
    germ (C.c t) y hy hc (C.mulFun σ f) = germ (C.a t) y hy ha σ * germ (C.b t) y hy hb f :=
  (C.exists_mul σ f).choose_spec t y hy ha hb hc

def mul : H0 p P O →ₗ[k] H0 p B O →ₗ[k] H0 p N O :=
  LinearMap.mk₂ k C.mulFun
    (fun σ σ' f => C.sec_ext fun t y hy ha hb hc => by
      simp only [map_add, C.germ_mulFun _ _ t y hy ha hb hc, add_mul])
    (fun c σ f => C.sec_ext fun t y hy ha hb hc => by
      simp only [germ_smul, C.germ_mulFun _ _ t y hy ha hb hc, mul_assoc])
    (fun σ f f' => C.sec_ext fun t y hy ha hb hc => by
      simp only [map_add, C.germ_mulFun _ _ t y hy ha hb hc, mul_add])
    (fun c σ f => C.sec_ext fun t y hy ha hb hc => by
      simp only [germ_smul, C.germ_mulFun _ _ t y hy ha hb hc, mul_left_comm])

theorem germ_mul (σ : H0 p P O) (f : H0 p B O) (t : C.τ) (y : Y) (hy : y ∈ O)
    (ha : y ∈ P.U (C.a t)) (hb : y ∈ B.U (C.b t)) (hc : y ∈ N.U (C.c t)) :
    germ (C.c t) y hy hc (C.mul σ f) = germ (C.a t) y hy ha σ * germ (C.b t) y hy hb f :=
  C.germ_mulFun σ f t y hy ha hb hc

theorem resG_loc_mul (σ : H0 p P O) (f : H0 p B O) (t : C.τ) {W : Y.Opens}
    (ha : W ≤ O ⊓ P.U (C.a t)) (hb : W ≤ O ⊓ B.U (C.b t)) (hc : W ≤ O ⊓ N.U (C.c t)) :
    resG Y hc ((C.mul σ f).loc _) = resG Y ha (σ.loc _) * resG Y hb (f.loc _) :=
  fun_ext_ger fun y hy => by
    rw [map_mul, ger_resG, ger_resG, ger_resG]
    exact C.germ_mul σ f t y (ha hy).1 (ha hy).2 (hb hy).2 (hc hy).2

theorem val_mul {R : Type} [CommRing R] (σ : H0 p P O) (f : H0 p B O) (t : C.τ) (x : Sp R ⟶ Y)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (ha : ⊤ ≤ x ⁻¹ᵁ P.U (C.a t)) (hb : ⊤ ≤ x ⁻¹ᵁ B.U (C.b t))
    (hc : ⊤ ≤ x ⁻¹ᵁ N.U (C.c t)) :
    val x (C.c t) hO hc (C.mul σ f) = val x (C.a t) hO ha σ * val x (C.b t) hO hb f := by
  have e := congrArg (evalPt x _ (le_preimage_inf (le_preimage_inf (le_preimage_inf hO ha)
    (le_preimage_inf hO hb)) (le_preimage_inf hO hc))) (C.resG_loc_mul σ f t
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)
  rwa [map_mul, evalPt_res x _ (le_preimage_inf hO hc), evalPt_res x _ (le_preimage_inf hO ha),
    evalPt_res x _ (le_preimage_inf hO hb)] at e

theorem restr_mul (h : O' ≤ O) (σ : H0 p P O) (f : H0 p B O) :
    restr h (C.mul σ f) = C.mul (restr h σ) (restr h f) :=
  C.sec_ext fun t y hy ha hb hc => by
    rw [germ_restr, C.germ_mul _ _ t y _ ha hb, C.germ_mul _ _ t y _ ha hb, germ_restr, germ_restr]

theorem bijective_mul {σ : H0 p P O} (hσ : NowhereZero σ) : Function.Bijective (C.mul σ) := by
  refine ⟨fun f f' e => ext_germ fun y hy => ?_, fun g => ?_⟩
  · obtain ⟨t, ha, hb, hc⟩ := C.cover y
    refine ⟨C.b t, hb, (hσ y hy _ ha).mul_left_cancel ?_⟩
    rw [← C.germ_mul _ _ t y hy ha hb hc, ← C.germ_mul _ _ t y hy ha hb hc, e]
  · have hu (t : C.τ) : IsUnit (σ.loc (C.a t)) :=
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => hσ y hy.1 _ hy.2
    have hv (t y) (h : y ∈ O ⊓ P.U (C.a t)) :
        germ (C.a t) y h.1 h.2 σ * ger y h (hu t).unit⁻¹.val = 1 :=
      (map_mul (ger y h) _ _).symm.trans (by rw [IsUnit.mul_val_inv, map_one])
    obtain ⟨f, hf⟩ := exists_of_germs (p := p) (O := O) C.isLB₂
      (fun t => ((O ⊓ P.U (C.a t)) ⊓ (O ⊓ N.U (C.c t))) ⊓ B.U (C.b t)) C.b
      (fun _ => inf_le_left.trans (inf_le_left.trans inf_le_left)) (fun _ => inf_le_right)
      (fun y hy => (C.cover y).imp fun _ h => ⟨⟨⟨hy, h.1⟩, hy, h.2.2⟩, h.2.1⟩)
      (fun t => resG Y (inf_le_left.trans inf_le_left) (hu t).unit⁻¹.val *
        resG Y (inf_le_left.trans inf_le_right) (g.loc _))
      fun y t t' h h' => by
        simp only [map_mul, ger_resG]
        have e₁ := germ_change _ _ y h.1.1.1 h.1.2.2 h'.1.2.2 g
        rw [C.rule y t t' ⟨h.1.1.2, h.2, h.1.2.2⟩ ⟨h'.1.1.2, h'.2, h'.1.2.2⟩, Units.val_mul] at e₁
        have e₂ := germ_change _ _ y h.1.1.1 h.1.1.2 h'.1.1.2 σ
        have e₃ := hv t y h.1.1
        have e₄ := hv t' y h'.1.1
        change _ * germ (C.c t) y h.1.1.1 h.1.2.2 g = _ * (_ * germ (C.c t') y h.1.1.1 h'.1.2.2 g)
        rw [e₁]
        rw [e₂] at e₃
        linear_combination (exp := 1) (tr B y (C.b t) (C.b t')).val *
          germ (C.c t') y h.1.1.1 h'.1.2.2 g * (ger y h'.1.1 (hu t').unit⁻¹.val * e₃ -
            (tr P y (C.a t) (C.a t')).val * ger y h.1.1 (hu t).unit⁻¹.val * e₄)
    refine ⟨f, C.sec_ext fun t y hy ha hb hc => ?_⟩
    rw [C.germ_mul _ _ t y hy ha hb hc,
      hf t y (memInf (memInf (memInf hy ha) (memInf hy hc)) hb), map_mul, ger_resG, ger_resG,
      ← mul_assoc, hv t y (memInf hy ha), one_mul]
    rfl

def mulEquiv {σ : H0 p P O} (hσ : NowhereZero σ) : H0 p B O ≃ₗ[k] H0 p N O :=
  LinearEquiv.ofBijective (C.mul σ) (C.bijective_mul hσ)

@[simp] theorem mulEquiv_apply {σ : H0 p P O} (hσ : NowhereZero σ) (f : H0 p B O) :
    C.mulEquiv hσ f = C.mul σ f := rfl

abbrev pull (r : T ⟶ Y) : ProdChart (P.pull r) (B.pull r) (N.pull r) where
  isLB₁ := LB.isLB_pull C.isLB₁ r
  isLB₂ := LB.isLB_pull C.isLB₂ r
  isLB₃ := LB.isLB_pull C.isLB₃ r
  τ := C.τ
  a t _ := C.a t
  b t _ := C.b t
  c t _ := C.c t
  cover z := (C.cover (r z)).imp fun _ h => ⟨mem_pull.2 h.1, mem_pull.2 h.2.1, mem_pull.2 h.2.2⟩
  rule z t t' h h' := by
    rw [tr_pull N r z h.2.2 h'.2.2, tr_pull P r z h.1 h'.1, tr_pull B r z h.2.1 h'.2.1, ← map_mul]
    exact congrArg _ (C.rule (r z) t t' ⟨mem_pull.1 h.1, mem_pull.1 h.2.1, mem_pull.1 h.2.2⟩
      ⟨mem_pull.1 h'.1, mem_pull.1 h'.2.1, mem_pull.1 h'.2.2⟩)

theorem pullSL_mul (r : T ⟶ Y) {q : T ⟶ Sp k'} {φ : k →+* k'} (hq : r ≫ p = q ≫ spMap φ)
    {W : T.Opens} (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullSL r hq h (C.mul σ f) = (C.pull r).mul (pullSL r hq h σ) (pullSL r hq h f) :=
  (C.pull r).sec_ext fun t z hz ha hb hc => by
    rw [(C.pull r).germ_mul _ _ t z hz ha hb hc, germ_pullSL, germ_pullSL, germ_pullSL, ← map_mul]
    exact congrArg _ (C.germ_mul σ f t _ _ _ _ _)

theorem pull_mul (r : T ⟶ Y) {W : T.Opens} (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    H0.pull r h (C.mul σ f) = (C.pull r).mul (H0.pull r h σ) (H0.pull r h f) :=
  C.pullSL_mul r _ h σ f

end ProdChart

section Charts

variable {L M A B : LB Y} {n m d l : ℤ}

abbrev tensChart (hA : A.IsLB) (hB : B.IsLB) : ProdChart A B (tens A B) where
  isLB₁ := hA
  isLB₂ := hB
  isLB₃ := isLB_tens hA hB
  τ := A.ι × B.ι
  a t := t.1
  b t := t.2
  c t := t
  cover y := let ⟨i, hi⟩ := exists_chart hA y; let ⟨j, hj⟩ := exists_chart hB y
    ⟨(i, j), hi, hj, hi, hj⟩
  rule y _ _ h h' := tr_tens A B y h.2.2 h'.2.2

abbrev tw (M L : LB Y) (n : ℤ) : LB Y := tens M (lbZPow L n)

theorem isLB_tw (hM : M.IsLB) (hL : L.IsLB) (n : ℤ) : (tw M L n).IsLB :=
  isLB_tens hM (Twist.isLB_lbZPow hL n)

abbrev twIdx (n : ℤ) (i : M.ι) (j : L.ι) : (tw M L n).ι := (i, fun _ => j)

theorem mem_zpow_U {y : Y} {j : L.ι} : y ∈ (lbZPow L n).U (fun _ => j) ↔ y ∈ L.U j := mem_powChart

theorem mem_tw_U {y : Y} {i : M.ι} {j : L.ι} :
    y ∈ (tw M L n).U (twIdx n i j) ↔ y ∈ M.U i ∧ y ∈ L.U j :=
  and_congr_right' mem_powChart

theorem tr_tw (y : Y) {i i' : M.ι} {j j' : L.ι} (h : y ∈ (tw M L n).U (twIdx n i j))
    (h' : y ∈ (tw M L n).U (twIdx n i' j')) :
    tr (tw M L n) y (twIdx n i j) (twIdx n i' j') = tr M y i i' * tr L y j j' ^ n :=
  (tr_tens M _ y h h').trans (congrArg (_ * ·) (tr_zpow L n y h.2 h'.2))

abbrev oneChart (hM : M.IsLB) (hL : L.IsLB) (h : n + 1 = l) : ProdChart L (tw M L n) (tw M L l) where
  isLB₁ := hL
  isLB₂ := isLB_tw hM hL n
  isLB₃ := isLB_tw hM hL l
  τ := M.ι × L.ι
  a t := t.2
  b t := twIdx n t.1 t.2
  c t := twIdx l t.1 t.2
  cover y := let ⟨i, hi⟩ := exists_chart hM y; let ⟨j, hj⟩ := exists_chart hL y
    ⟨(i, j), hj, mem_tw_U.2 ⟨hi, hj⟩, mem_tw_U.2 ⟨hi, hj⟩⟩
  rule y _ _ e e' := by
    rw [tr_tw y e.2.2 e'.2.2, tr_tw y e.2.1 e'.2.1, ← h, zpow_add_one, ← mul_assoc, mul_comm]

abbrev powChart (hM : M.IsLB) (hL : L.IsLB) (h : n + m = l) :
    ProdChart (lbZPow L m) (tw M L n) (tw M L l) where
  isLB₁ := Twist.isLB_lbZPow hL m
  isLB₂ := isLB_tw hM hL n
  isLB₃ := isLB_tw hM hL l
  τ := M.ι × L.ι
  a t _ := t.2
  b t := twIdx n t.1 t.2
  c t := twIdx l t.1 t.2
  cover y := let ⟨i, hi⟩ := exists_chart hM y; let ⟨j, hj⟩ := exists_chart hL y
    ⟨(i, j), mem_zpow_U.2 hj, mem_tw_U.2 ⟨hi, hj⟩, mem_tw_U.2 ⟨hi, hj⟩⟩
  rule y _ _ e e' := by
    rw [tr_tw y e.2.2 e'.2.2, tr_tw y e.2.1 e'.2.1, tr_zpow L m y e.1 e'.1, ← h, zpow_add,
      ← mul_assoc, mul_comm]

abbrev baseChart (hM : M.IsLB) (hL : L.IsLB) (m : ℤ) : ProdChart (lbZPow L m) M (tw M L m) where
  isLB₁ := Twist.isLB_lbZPow hL m
  isLB₂ := hM
  isLB₃ := isLB_tw hM hL m
  τ := M.ι × L.ι
  a t _ := t.2
  b t := t.1
  c t := twIdx m t.1 t.2
  cover y := let ⟨i, hi⟩ := exists_chart hM y; let ⟨j, hj⟩ := exists_chart hL y
    ⟨(i, j), mem_zpow_U.2 hj, hi, mem_tw_U.2 ⟨hi, hj⟩⟩
  rule y _ _ e e' := by rw [tr_tw y e.2.2 e'.2.2, tr_zpow L m y e.1 e'.1, mul_comm]

abbrev adjChart (hM : M.IsLB) (hB : B.IsLB) (hL : L.IsLB) (h : n + d = l) :
    ProdChart (tw M L d) (tw B L n) (tw (tens M B) L l) where
  isLB₁ := isLB_tw hM hL d
  isLB₂ := isLB_tw hB hL n
  isLB₃ := isLB_tw (isLB_tens hM hB) hL l
  τ := M.ι × B.ι × L.ι
  a t := twIdx d t.1 t.2.2
  b t := twIdx n t.2.1 t.2.2
  c t := twIdx (M := tens M B) l (t.1, t.2.1) t.2.2
  cover y := let ⟨i, hi⟩ := exists_chart hM y; let ⟨b, hb⟩ := exists_chart hB y
    let ⟨j, hj⟩ := exists_chart hL y
    ⟨(i, b, j), mem_tw_U.2 ⟨hi, hj⟩, mem_tw_U.2 ⟨hb, hj⟩, mem_tw_U.2 ⟨⟨hi, hb⟩, hj⟩⟩
  rule y _ _ e e' := by
    rw [tr_tw y e.2.2 e'.2.2, tr_tw y e.2.1 e'.2.1, tr_tw y e.1 e'.1,
      tr_tens M B y e.2.2.1 e'.2.2.1, ← h, add_comm, zpow_add, mul_mul_mul_comm]

theorem commGroup_mul_mul_eq_mul_inv_mul_mul_mul {G : Type*} [CommGroup G] (m a b x y : G) :
    m * a * x = a * (b * y)⁻¹ * (m * b * (x * y)) := by
  rw [show m * b * (x * y) = b * y * (m * x) by ac_rfl, mul_assoc a, inv_mul_cancel_left]
  ac_rfl

abbrev quotChart (hM : M.IsLB) (hA : A.IsLB) (hB : B.IsLB) (hL : L.IsLB) (h : n + d = l) :
    ProdChart (LB.div A (tw B L d)) (tw (tens M B) L l) (tw (tens M A) L n) where
  isLB₁ := LB.isLB_div hA (isLB_tw hB hL d)
  isLB₂ := isLB_tw (isLB_tens hM hB) hL l
  isLB₃ := isLB_tw (isLB_tens hM hA) hL n
  τ := M.ι × A.ι × B.ι × L.ι
  a t := (t.2.1, twIdx d t.2.2.1 t.2.2.2)
  b t := twIdx (M := tens M B) l (t.1, t.2.2.1) t.2.2.2
  c t := twIdx (M := tens M A) n (t.1, t.2.1) t.2.2.2
  cover y := let ⟨i, hi⟩ := exists_chart hM y; let ⟨a, ha⟩ := exists_chart hA y
    let ⟨b, hb⟩ := exists_chart hB y; let ⟨j, hj⟩ := exists_chart hL y
    ⟨(i, a, b, j), ⟨ha, mem_tw_U.2 ⟨hb, hj⟩⟩, mem_tw_U.2 ⟨⟨hi, hb⟩, hj⟩, mem_tw_U.2 ⟨⟨hi, ha⟩, hj⟩⟩
  rule y _ _ e e' := by
    rw [tr_tw y e.2.2 e'.2.2, tr_tw y e.2.1 e'.2.1, tr_div A _ y e.1 e'.1, tr_tw y e.1.2 e'.1.2,
      tr_tens M B y e.2.1.1 e'.2.1.1, tr_tens M A y e.2.2.1 e'.2.2.1, ← h, zpow_add]
    exact commGroup_mul_mul_eq_mul_inv_mul_mul_mul _ _ _ _ _

end Charts

end GlobalTheory.Vanishing
