import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod
  resG_g_self resG_cocycle)

namespace GlobalTheory

namespace Twist

variable {X Y : Scheme.{0}}

variable (F G H : X.Modules) (L M N : LB X)

def secGroup (V : X.Opens) : AddSubgroup (∀ i, Γ(F, V ⊓ L.U i)) where
  carrier := {s | ∀ i j, resM F (inf_le_left : V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i) (s i) =
    resG X (inf_le_inf_right _ inf_le_right : V ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j)
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
        resM F (inf_le_inf_right _ inf_le_left : V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U j) (s j)}
  add_mem' := fun {s t} hs ht i j => by
    simp only [Pi.add_apply, map_add, hs i j, ht i j, smul_add]
  zero_mem' := fun i j => by simp only [Pi.zero_apply, map_zero, smul_zero]
  neg_mem' := fun {s} hs i j => by simp only [Pi.neg_apply, map_neg, hs i j, smul_neg]

variable {F L} in

theorem secGroup_rel {V : X.Opens} (s : secGroup F L V) (i j : L.ι)
    {W : X.Opens} (hi : W ≤ V ⊓ L.U i) (hj : W ≤ V ⊓ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resM F hi (s.1 i) = resG X hij (L.g i j : Γ(X, L.U i ⊓ L.U j)) • resM F hj (s.1 j) := by
  have := congrArg (resM F (le_inf hi (hj.trans inf_le_right) : W ≤ V ⊓ L.U i ⊓ L.U j)) (s.2 i j)
  simpa only [resM_smul, resM_resM, resG_resG] using this

instance secGroupModule (V : X.Opens) : Module Γ(X, V) (secGroup F L V) where
  smul a s := ⟨fun i => resG X (inf_le_left : V ⊓ L.U i ≤ V) a • s.1 i, fun i j => by
    rw [resM_smul, resM_smul, s.2 i j, resG_resG, resG_resG, smul_comm]⟩
  one_smul s := Subtype.ext <| funext fun i => by
    change resG X _ 1 • s.1 i = _
    rw [map_one, one_smul]
  mul_smul a b s := Subtype.ext <| funext fun i => by
    change resG X (inf_le_left : V ⊓ L.U i ≤ V) (a * b) • s.1 i =
      resG X (inf_le_left : V ⊓ L.U i ≤ V) a • (resG X (inf_le_left : V ⊓ L.U i ≤ V) b • s.1 i)
    rw [map_mul, mul_smul]
  smul_zero a := Subtype.ext <| funext fun i => smul_zero _
  smul_add a s t := Subtype.ext <| funext fun i => smul_add _ _ _
  add_smul a b s := Subtype.ext <| funext fun i => by
    change resG X (inf_le_left : V ⊓ L.U i ≤ V) (a + b) • s.1 i =
      resG X (inf_le_left : V ⊓ L.U i ≤ V) a • s.1 i + resG X (inf_le_left : V ⊓ L.U i ≤ V) b • s.1 i
    rw [map_add, add_smul]
  zero_smul s := Subtype.ext <| funext fun i => by
    change resG X _ 0 • s.1 i = 0
    rw [map_zero, zero_smul]

def secRes {V W : X.Opens} (h : W ≤ V) : secGroup F L V →+ secGroup F L W where
  toFun s := ⟨fun i => resM F (inf_le_inf_right _ h) (s.1 i), fun i j => by
    rw [resM_resM, resM_resM]
    exact secGroup_rel s i j _ _ _⟩
  map_zero' := Subtype.ext <| funext fun i => map_zero _
  map_add' s t := Subtype.ext <| funext fun i => map_add _ _ _

theorem secRes_smul {V W : X.Opens} (h : W ≤ V) (r : Γ(X, V)) (m : secGroup F L V) :
    secRes F L h (r • m) = resG X h r • secRes F L h m :=
  Subtype.ext <| funext fun i => by
    change resM F _ (resG X _ r • m.1 i) = resG X _ (resG X h r) • resM F _ (m.1 i)
    rw [resM_smul, resG_resG, resG_resG]

def secPresheaf : TopCat.Presheaf Ab.{0} X where
  obj V := AddCommGrpCat.of (secGroup F L V.unop)
  map f := AddCommGrpCat.ofHom (secRes F L (leOfHom f.unop))
  map_id V := by
    ext s i
    exact resM_self _ _
  map_comp f g := by
    ext s i
    exact (resM_resM _ _ _).symm

theorem isSheaf_secPresheaf : (secPresheaf F L).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have hc (i : L.ι) : iSup W ⊓ L.U i ≤ ⨆ k, W k ⊓ L.U i := by rw [iSup_inf_eq]
  have hW (i : L.ι) (k : κ) : W k ⊓ L.U i ≤ iSup W ⊓ L.U i := inf_le_inf_right _ (le_iSup W k)
  have H (i : L.ι) : ∃ b : Γ(F, iSup W ⊓ L.U i), ∀ k, resM F (hW i k) b = (sf k).1 i := by
    refine exists_sec_of_cover (fun k => W k ⊓ L.U i) (hW i) (hc i) (fun k => (sf k).1 i)
      fun k l => ?_
    have e : resM F (inf_le_inf_right (L.U i) (inf_le_left : W k ⊓ W l ≤ W k)) ((sf k).1 i) =
        resM F (inf_le_inf_right (L.U i) (inf_le_right : W k ⊓ W l ≤ W l)) ((sf l).1 i) :=
      congrFun (congrArg Subtype.val (hsf k l)) i
    have := congrArg (resM F (le_inf (inf_le_inf inf_le_left inf_le_left)
      (inf_le_left.trans inf_le_right) :
        (W k ⊓ L.U i) ⊓ (W l ⊓ L.U i) ≤ W k ⊓ W l ⊓ L.U i)) e
    simpa only [resM_resM] using this
  choose b hb using H
  refine ⟨⟨b, fun i j => ?_⟩, fun k => Subtype.ext (funext fun i => hb i k), fun t ht => ?_⟩
  · refine sec_ext_of_cover (fun k => W k ⊓ L.U i ⊓ L.U j)
      (fun k => inf_le_inf_right _ (hW i k)) (by rw [iSup_inf_eq, iSup_inf_eq]) fun k => ?_
    have := (sf k).2 i j
    rw [← hb i k, ← hb j k] at this
    simpa only [resM_smul, resM_resM, resG_resG] using this
  · refine Subtype.ext (funext fun i => sec_ext_of_cover _ (hW i) (hc i) fun k => ?_)
    rw [hb i k]
    exact congrFun (congrArg Subtype.val (ht k)) i

end Twist

def twist {X : Scheme.{0}} (F : X.Modules) (L : LB X) : X.Modules :=
  letI : ∀ V, Module (X.ringCatSheaf.obj.obj V) ((Twist.secPresheaf F L).obj V) :=
    fun V => Twist.secGroupModule F L V.unop
  { val := PresheafOfModules.ofPresheaf (Twist.secPresheaf F L) fun _ _ f r m =>
      Twist.secRes_smul F L (leOfHom f.unop) r m
    isSheaf := Twist.isSheaf_secPresheaf F L }

namespace Twist

variable {X Y : Scheme.{0}} {F G H : X.Modules} {L M N : LB X}

def coord {V : X.Opens} (s : Γ(twist F L, V)) (i : L.ι) : Γ(F, V ⊓ L.U i) :=
  (show secGroup F L V from s).1 i

theorem coord_mem {V : X.Opens} (s : Γ(twist F L, V)) : coord s ∈ secGroup F L V :=
  (show secGroup F L V from s).2

def mkSec {V : X.Opens} (f : ∀ i, Γ(F, V ⊓ L.U i)) (hf : f ∈ secGroup F L V) : Γ(twist F L, V) :=
  (⟨f, hf⟩ : secGroup F L V)

@[simp] theorem coord_mkSec {V : X.Opens} (f : ∀ i, Γ(F, V ⊓ L.U i)) (hf : f ∈ secGroup F L V) :
    coord (mkSec f hf) = f := rfl

@[ext] theorem sec_ext {V : X.Opens} {s t : Γ(twist F L, V)} (h : ∀ i, coord s i = coord t i) :
    s = t := Subtype.ext (funext h)

@[simp] theorem coord_zero {V : X.Opens} (i : L.ι) : coord (0 : Γ(twist F L, V)) i = 0 := rfl

@[simp] theorem coord_add {V : X.Opens} (s t : Γ(twist F L, V)) (i : L.ι) :
    coord (s + t) i = coord s i + coord t i := rfl

@[simp] theorem coord_neg {V : X.Opens} (s : Γ(twist F L, V)) (i : L.ι) :
    coord (-s) i = - coord s i := rfl

@[simp] theorem coord_sub {V : X.Opens} (s t : Γ(twist F L, V)) (i : L.ι) :
    coord (s - t) i = coord s i - coord t i := rfl

@[simp] theorem coord_smul {V : X.Opens} (a : Γ(X, V)) (s : Γ(twist F L, V)) (i : L.ι) :
    coord (a • s) i = resG X (inf_le_left : V ⊓ L.U i ≤ V) a • coord s i := rfl

@[simp] theorem coord_resM {V W : X.Opens} (h : W ≤ V) (s : Γ(twist F L, V)) (i : L.ι) :
    coord (resM (twist F L) h s) i = resM F (inf_le_inf_right _ h) (coord s i) := rfl

theorem coord_rel {V : X.Opens} (s : Γ(twist F L, V)) (i j : L.ι)
    {W : X.Opens} (hi : W ≤ V ⊓ L.U i) (hj : W ≤ V ⊓ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resM F hi (coord s i) = resG X hij (L.g i j : Γ(X, L.U i ⊓ L.U j)) • resM F hj (coord s j) :=
  secGroup_rel (show secGroup F L V from s) i j hi hj hij

theorem sec_ext_of_charts {ι : Type*} {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤) {V : X.Opens}
    {s t : Γ(twist F L, V)}
    (h : ∀ i k, resM F (inf_le_left : V ⊓ L.U i ⊓ U k ≤ V ⊓ L.U i) (coord s i) =
      resM F inf_le_left (coord t i)) : s = t :=
  sec_ext fun i => sec_ext_of_cover (fun k => V ⊓ L.U i ⊓ U k) (fun _ => inf_le_left)
    (le_iSup_inf hU _) (h i)

variable (L) in

def map (φ : F ⟶ G) : twist F L ⟶ twist G L :=
  homOfLinear
    (fun V =>
      { toFun := fun s => mkSec (fun i => φ.app _ (coord s i)) fun i j => by
          rw [← app_resM, ← app_resM, ← Scheme.Modules.Hom.app_smul]
          exact congrArg _ (coord_mem s i j)
        map_add' := fun s t => sec_ext fun i => map_add _ _ _
        map_smul' := fun a s => sec_ext fun i => φ.app_smul _ _ })
    fun h s => sec_ext fun i => app_resM φ _ _

@[simp] theorem coord_map_app (φ : F ⟶ G) {V : X.Opens} (s : Γ(twist F L, V)) (i : L.ι) :
    coord ((map L φ).app V s) i = φ.app _ (coord s i) := rfl

end Twist

def twistFunctor {X : Scheme.{0}} (L : LB X) : X.Modules ⥤ X.Modules where
  obj F := twist F L
  map φ := Twist.map L φ
  map_id _ := rfl
  map_comp _ _ := rfl

namespace Twist

variable {X Y : Scheme.{0}} {F G H : X.Modules} {L M N : LB X}

@[simp] theorem twistFunctor_obj (L : LB X) (F : X.Modules) :
    (twistFunctor L).obj F = twist F L := rfl

@[simp] theorem twistFunctor_map (L : LB X) (φ : F ⟶ G) : (twistFunctor L).map φ = map L φ := rfl

@[simp] theorem map_id (L : LB X) (F : X.Modules) : map L (𝟙 F) = 𝟙 (twist F L) := rfl

@[reassoc] theorem map_comp (L : LB X) (φ : F ⟶ G) (ψ : G ⟶ H) :
    map L (φ ≫ ψ) = map L φ ≫ map L ψ := rfl

instance (L : LB X) : (twistFunctor L).Additive where
  map_add := rfl

theorem hom_ext {φ ψ : G ⟶ twist F L}
    (h : ∀ (V : X.Opens) (s : Γ(G, V)) (i : L.ι), coord (φ.app V s) i = coord (ψ.app V s) i) :
    φ = ψ := by
  ext V s : 3
  exact sec_ext (h V s)

def chartEquiv (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) :
    Γ(twist F L, V) ≃ₗ[Γ(X, V)] Γ(F, V) where
  toFun s := resM F (le_inf le_rfl h) (coord s i)
  invFun t := mkSec (fun j => resG X (le_inf inf_le_right (inf_le_left.trans h))
      (L.g j i : Γ(X, L.U j ⊓ L.U i)) • resM F inf_le_left t) fun j k => by
    simp only [resM_smul, resM_resM, resG_resG, smul_smul]
    rw [resG_cocycle hL j k i]
  map_add' s t := map_add _ _ _
  map_smul' a s := by
    simp only [coord_smul, resM_smul, resG_resG, resG_self, RingHom.id_apply]
  left_inv s := sec_ext fun j => by
    simp only [coord_mkSec, resM_resM]
    rw [← coord_rel s j i le_rfl, resM_self]
  right_inv t := by
    change resM F _ (_ • _) = _
    simp only [resM_smul, resM_resM, resG_resG, resM_self, resG_g_self hL, one_smul]

theorem chartEquiv_apply (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (s : Γ(twist F L, V)) : chartEquiv hL i h s = resM F (le_inf le_rfl h) (coord s i) := rfl

theorem coord_chartEquiv_symm (hL : L.IsLB) (i j : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (t : Γ(F, V)) : coord ((chartEquiv hL i h).symm t) j =
      resG X (le_inf inf_le_right (inf_le_left.trans h)) (L.g j i : Γ(X, L.U j ⊓ L.U i)) •
        resM F inf_le_left t := rfl

theorem chartEquiv_resM (hL : L.IsLB) (i : L.ι) {V W : X.Opens} (h : V ≤ L.U i) (h' : W ≤ V)
    (s : Γ(twist F L, V)) :
    chartEquiv hL i (h'.trans h) (resM (twist F L) h' s) = resM F h' (chartEquiv hL i h s) := by
  simp only [chartEquiv_apply, coord_resM, resM_resM]

theorem chartEquiv_change (hL : L.IsLB) (i j : L.ι) {V : X.Opens} (hi : V ≤ L.U i)
    (hj : V ≤ L.U j) (s : Γ(twist F L, V)) :
    chartEquiv hL i hi s =
      resG X (le_inf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) • chartEquiv hL j hj s :=
  coord_rel s i j _ _ _

theorem chartEquiv_map_app (hL : L.IsLB) (φ : F ⟶ G) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (s : Γ(twist F L, V)) :
    chartEquiv hL i h ((map L φ).app V s) = φ.app V (chartEquiv hL i h s) :=
  (app_resM φ _ _).symm

variable (F) in

def restrictIso (hL : L.IsLB) (i : L.ι) (g : Y ⟶ X) [IsOpenImmersion g]
    (hg : g.opensRange ≤ L.U i) : (twist F L).restrict g ≅ F.restrict g :=
  restrictIsoOfLinear (fun _ h => chartEquiv hL i h) (chartEquiv_resM hL i) g hg

theorem restrictIso_hom_app (hL : L.IsLB) (i : L.ι) (g : Y ⟶ X) [IsOpenImmersion g]
    (hg : g.opensRange ≤ L.U i) (W : Y.Opens) (s : Γ(twist F L, g ''ᵁ W)) :
    ((restrictIso F hL i g hg).hom.app W s : Γ(F, g ''ᵁ W)) =
      chartEquiv hL i ((g.image_le_opensRange W).trans hg) s := rfl

def restrictNatIso (hL : L.IsLB) (i : L.ι) (g : Y ⟶ X) [IsOpenImmersion g]
    (hg : g.opensRange ≤ L.U i) :
    twistFunctor L ⋙ Scheme.Modules.restrictFunctor g ≅ Scheme.Modules.restrictFunctor g :=
  NatIso.ofComponents (fun F => restrictIso F hL i g hg) fun φ => by
    ext W s : 3
    exact chartEquiv_map_app hL φ i ((g.image_le_opensRange W).trans hg) s

variable (F) in

def chartIso (hL : L.IsLB) (i : L.ι) : (twist F L).restrict (L.U i).ι ≅ F.restrict (L.U i).ι :=
  restrictIso F hL i _ (L.U i).opensRange_ι.le

theorem isQuasicoherent_twist_iff (hL : L.IsLB) :
    (twist F L).IsQuasicoherent ↔ F.IsQuasicoherent :=
  ⟨fun _ => isQuasicoherent_of_locally_iso hL.cover (chartIso F hL),
    fun _ => isQuasicoherent_of_locally_iso hL.cover fun i => (chartIso F hL i).symm⟩

theorem isQuasicoherent_twist (hL : L.IsLB) [h : F.IsQuasicoherent] :
    (twist F L).IsQuasicoherent := (isQuasicoherent_twist_iff hL).2 h

theorem isFiniteType_twist_iff (hL : L.IsLB) : (twist F L).IsFiniteType ↔ F.IsFiniteType :=
  ⟨fun _ => isFiniteType_of_locally_iso hL.cover fun i W h =>
      restrictIso F hL i W.ι (W.opensRange_ι.le.trans h),
    fun _ => isFiniteType_of_locally_iso hL.cover fun i W h =>
      (restrictIso F hL i W.ι (W.opensRange_ι.le.trans h)).symm⟩

theorem isFiniteType_twist (hL : L.IsLB) [h : F.IsFiniteType] : (twist F L).IsFiniteType :=
  (isFiniteType_twist_iff hL).2 h

theorem finite_sections_twist_iff (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) :
    Module.Finite Γ(X, V) Γ(twist F L, V) ↔ Module.Finite Γ(X, V) Γ(F, V) :=
  Module.Finite.equiv_iff (chartEquiv hL i h)

variable (F) in

def stalkEquiv (hL : L.IsLB) (i : L.ι) {x : X} (hx : x ∈ L.U i) :
    ((twist F L).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] (F.presheaf.stalk x :) :=
  stalkEquivOfLinear (fun _ h => chartEquiv hL i h) (chartEquiv_resM hL i) hx

theorem stalkEquiv_germ (hL : L.IsLB) (i : L.ι) {x : X} (hx : x ∈ L.U i) {V : X.Opens}
    (hxV : x ∈ V) (s : Γ(twist F L, V)) :
    stalkEquiv F hL i hx ((twist F L).presheaf.germ V x hxV s) =
      F.presheaf.germ (V ⊓ L.U i) x ⟨hxV, hx⟩ (coord s i) := by
  have hx' : x ∈ V ⊓ L.U i := ⟨hxV, hx⟩
  rw [← germ_resM (inf_le_left : V ⊓ L.U i ≤ V) hx']
  refine (stalkEquivOfLinear_germ _ _ hx inf_le_right hx' _).trans ?_
  rw [chartEquiv_apply, coord_resM, resM_resM, resM_self]

theorem nonempty_stalkEquiv (hL : L.IsLB) (x : X) :
    Nonempty (((twist F L).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] (F.presheaf.stalk x :)) :=
  let ⟨i, hi⟩ := Semi.LB.mem_of_cover hL x
  ⟨stalkEquiv F hL i hi⟩

theorem nontrivial_stalk_twist_iff (hL : L.IsLB) (x : X) :
    Nontrivial ((twist F L).presheaf.stalk x :) ↔ Nontrivial (F.presheaf.stalk x :) :=
  let ⟨e⟩ := nonempty_stalkEquiv (F := F) hL x
  e.toEquiv.nontrivial_congr

theorem support_twist (hL : L.IsLB) : QCoh.support (twist F L) = QCoh.support F :=
  Set.ext (nontrivial_stalk_twist_iff hL)

theorem suppDim_twist (hL : L.IsLB) : QCoh.suppDim (twist F L) = QCoh.suppDim F := by
  rw [QCoh.suppDim, QCoh.suppDim, support_twist hL]

theorem assPoints_twist (hL : L.IsLB) : QCoh.assPoints (twist F L) = QCoh.assPoints F :=
  Set.ext fun x => by
    obtain ⟨e⟩ := nonempty_stalkEquiv (F := F) hL x
    rw [QCoh.assPoints, QCoh.assPoints, Set.mem_setOf_eq, Set.mem_setOf_eq,
      LinearEquiv.AssociatedPrimes.eq e]

theorem isFiniteQC_twist_iff (hL : L.IsLB) : QCoh.IsFiniteQC (twist F L) ↔ QCoh.IsFiniteQC F := by
  rw [QCoh.isFiniteQC_iff_isFiniteType, QCoh.isFiniteQC_iff_isFiniteType,
    isQuasicoherent_twist_iff hL, isFiniteType_twist_iff hL]

theorem isFiniteQC_twist (hL : L.IsLB) [h : QCoh.IsFiniteQC F] : QCoh.IsFiniteQC (twist F L) :=
  (isFiniteQC_twist_iff hL).2 h

theorem isFlatOver_twist_iff (hL : L.IsLB) [F.IsQuasicoherent] {R : Type*} [CommRing R]
    (ρ : R →+* Γ(X, ⊤)) : QCoh.IsFlatOver (twist F L) ρ ↔ QCoh.IsFlatOver F ρ := by
  haveI := isQuasicoherent_twist (F := F) hL
  rw [QCoh.isFlatOver_iff_stalk, QCoh.isFlatOver_iff_stalk]
  refine forall_congr' fun x => ?_
  obtain ⟨e⟩ := nonempty_stalkEquiv (F := F) hL x
  letI := QCoh.baseModuleStalk F ρ x
  letI := QCoh.baseModuleStalk (twist F L) ρ x
  exact Module.Flat.equiv_iff (e.toAddEquiv.toLinearEquiv fun r t => e.map_smul _ t)

variable (L) in

def unitTwistIso : twist (unitMod X) L ≅ toMod L :=
  isoOfLinear
    (fun V =>
      { toFun := fun s => LB.mkSec (coord s) (coord_mem s)
        invFun := fun s => mkSec (F := unitMod X) (LB.coord s) (LB.coord_mem s)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    fun _ _ => rfl

@[simp] theorem coord_unitTwistIso_hom_app {V : X.Opens} (s : Γ(twist (unitMod X) L, V))
    (i : L.ι) : LB.coord ((unitTwistIso L).hom.app V s) i = coord s i := rfl

@[simp] theorem coord_unitTwistIso_inv_app {V : X.Opens} (s : Γ(toMod L, V)) (i : L.ι) :
    coord ((unitTwistIso L).inv.app V s) i = LB.coord s i := rfl

def tmulFun {V : X.Opens} (t : Γ(F, V)) (σ : Γ(toMod L, V)) : Γ(twist F L, V) :=
  mkSec (fun i => LB.coord σ i • resM F inf_le_left t) fun i j => by
    simp only [resM_smul, resM_resM, smul_smul]
    rw [LB.coord_mem σ i j]

theorem coord_tmulFun {V : X.Opens} (t : Γ(F, V)) (σ : Γ(toMod L, V)) (i : L.ι) :
    coord (tmulFun t σ) i = LB.coord σ i • resM F inf_le_left t := rfl

variable (F L) in

def tmul (V : X.Opens) : Γ(F, V) →ₗ[Γ(X, V)] Γ(toMod L, V) →ₗ[Γ(X, V)] Γ(twist F L, V) :=
  LinearMap.mk₂ _ tmulFun
    (fun t t' σ => sec_ext fun i => by
      rw [coord_add, coord_tmulFun, coord_tmulFun, coord_tmulFun, map_add, smul_add])
    (fun a t σ => sec_ext fun i => by
      rw [coord_smul, coord_tmulFun, coord_tmulFun, resM_smul, smul_comm])
    (fun t σ σ' => sec_ext fun i => by
      rw [coord_add, coord_tmulFun, coord_tmulFun, coord_tmulFun, LB.coord_add, add_smul])
    (fun a t σ => sec_ext fun i => by
      rw [coord_smul, coord_tmulFun, coord_tmulFun, LB.coord_smul, mul_smul])

@[simp] theorem coord_tmul {V : X.Opens} (t : Γ(F, V)) (σ : Γ(toMod L, V)) (i : L.ι) :
    coord (tmul F L V t σ) i = LB.coord σ i • resM F inf_le_left t := rfl

theorem resM_tmul {V W : X.Opens} (h : W ≤ V) (t : Γ(F, V)) (σ : Γ(toMod L, V)) :
    resM (twist F L) h (tmul F L V t σ) = tmul F L W (resM F h t) (resM (toMod L) h σ) :=
  sec_ext fun i => by
    rw [coord_resM, coord_tmul, coord_tmul, resM_smul, resM_resM, resM_resM]
    rfl

theorem chartEquiv_tmul (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) (t : Γ(F, V))
    (σ : Γ(toMod L, V)) : chartEquiv hL i h (tmul F L V t σ) = LB.chartEquiv hL i h σ • t := by
  rw [chartEquiv_apply, coord_tmul, resM_smul, resM_resM, resM_self, LB.chartEquiv_apply]

theorem map_app_tmul (φ : F ⟶ G) {V : X.Opens} (t : Γ(F, V)) (σ : Γ(toMod L, V)) :
    (map L φ).app V (tmul F L V t σ) = tmul G L V (φ.app V t) σ :=
  sec_ext fun i => by
    rw [coord_map_app, coord_tmul, coord_tmul, Scheme.Modules.Hom.app_smul, app_resM]

variable (F) in

def secHom (σ : LB.Sec L) : F ⟶ twist F L :=
  homOfLinear (fun V => (tmul F L V).flip (LB.ofSec σ V)) fun h t => by
    refine Eq.trans ?_ (resM_tmul h t _).symm
    exact congrArg (tmul F L _ (resM F h t)) (LB.map_ofSec σ h).symm

@[simp] theorem coord_secHom_app (σ : LB.Sec L) {V : X.Opens} (t : Γ(F, V)) (i : L.ι) :
    coord ((secHom F σ).app V t) i =
      resG X (inf_le_right : V ⊓ L.U i ≤ L.U i) (σ.f i) • resM F inf_le_left t := rfl

theorem chartEquiv_secHom_app (hL : L.IsLB) (σ : LB.Sec L) (i : L.ι) {V : X.Opens}
    (h : V ≤ L.U i) (t : Γ(F, V)) :
    chartEquiv hL i h ((secHom F σ).app V t) = resG X h (σ.f i) • t := by
  rw [chartEquiv_apply, coord_secHom_app, resM_smul, resM_resM, resM_self, resG_resG]

@[reassoc] theorem secHom_naturality (σ : LB.Sec L) (φ : F ⟶ G) :
    φ ≫ secHom G σ = secHom F σ ≫ map L φ :=
  hom_ext fun V t i => congrArg (coord · i) (map_app_tmul φ t (LB.ofSec σ V)).symm

theorem isUnit_resG_f (σ : LB.Sec L) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (hV : V ≤ Out.nonzeroLocus σ) : IsUnit (resG X h (σ.f i)) :=
  QCoh.isUnit_res_of_le_basicOpen _ h ((le_inf hV h).trans (nonzeroLocus_inf_chart σ i).le)

theorem bijective_of_eq_smul {A B : Type*} {V : X.Opens} {f : A → B} {p : A → Γ(F, V)}
    {q : B → Γ(F, V)} (hp : Function.Bijective p) (hq : Function.Bijective q) {u : Γ(X, V)}
    (hu : IsUnit u) (h : ∀ a, q (f a) = u • p a) : Function.Bijective f := by
  rw [← Function.Bijective.of_comp_iff' hq]
  exact (funext h : q ∘ f = (fun s => u • s) ∘ p) ▸ (bijective_smul_of_isUnit hu).comp hp

theorem bijective_secHom_app (hL : L.IsLB) (σ : LB.Sec L) {V : X.Opens}
    (hV : V ≤ Out.nonzeroLocus σ) : Function.Bijective ((secHom F σ).app V) :=
  bijective_app_of_cover _ hL.cover V fun i _ h hi =>
    bijective_of_eq_smul Function.bijective_id (chartEquiv hL i hi).bijective
      (isUnit_resG_f σ i hi (h.trans hV)) (chartEquiv_secHom_app hL σ i hi)

theorem isIso_secHom_genSec (hL : L.IsLB) (t : LB.Gen L) (ht : t.IsGen) :
    IsIso (secHom F (DVR.genSec t ht)) :=
  isIso_of_bijective _ fun _ =>
    bijective_secHom_app hL _ (le_top.trans (nonzeroLocus_genSec hL t ht).ge)

variable (F) in

def genIso (hL : L.IsLB) (t : LB.Gen L) (ht : t.IsGen) : F ≅ twist F L :=
  haveI := isIso_secHom_genSec (F := F) hL t ht
  asIso (secHom F (DVR.genSec t ht))

theorem genIso_hom (hL : L.IsLB) (t : LB.Gen L) (ht : t.IsGen) :
    (genIso F hL t ht).hom = secHom F (DVR.genSec t ht) := rfl

def genNatIso (hL : L.IsLB) (t : LB.Gen L) (ht : t.IsGen) : 𝟭 X.Modules ≅ twistFunctor L :=
  NatIso.ofComponents (fun F => genIso F hL t ht) fun φ => secHom_naturality _ φ

theorem isGen_one_triv : LB.Gen.IsGen (L := LB.triv X) ⟨fun _ => 1⟩ :=
  fun _ _ => (one_mul _).symm

variable (F) in

def trivIso : F ≅ twist F (LB.triv X) := genIso F (LB.isLB_triv X) _ isGen_one_triv

theorem coord_trivIso_hom_app {V : X.Opens} (t : Γ(F, V)) (i : PUnit.{1}) :
    coord (L := LB.triv X) ((trivIso F).hom.app V t) i = resM F inf_le_left t := by
  change resG X (inf_le_right : V ⊓ ⊤ ≤ ⊤) 1 • resM F inf_le_left t = _
  rw [map_one, one_smul]

theorem resG_div_g_mul (p q : (LB.div N L).ι) {W : X.Opens}
    (h : W ≤ (LB.div N L).U p ⊓ (LB.div N L).U q) (hL : W ≤ L.U p.2 ⊓ L.U q.2)
    (hN : W ≤ N.U p.1 ⊓ N.U q.1) :
    resG X h ((LB.div N L).g p q : Γ(X, (LB.div N L).U p ⊓ (LB.div N L).U q)) *
      resG X hL (L.g p.2 q.2 : Γ(X, L.U p.2 ⊓ L.U q.2)) =
        resG X hN (N.g p.1 q.1 : Γ(X, N.U p.1 ⊓ N.U q.1)) := by
  have e : res h ((LB.div N L).g p q) = res hN (N.g p.1 q.1) * (res hL (L.g p.2 q.2))⁻¹ :=
    Semi.LB.res_dg N L p q h
  rw [← val_res, ← val_res, ← val_res, e, Units.val_mul, Units.inv_mul_cancel_right]

theorem div_U_le_left (p : (LB.div N L).ι) : (LB.div N L).U p ≤ N.U p.1 := inf_le_left

theorem div_U_le_right (p : (LB.div N L).ι) : (LB.div N L).U p ≤ L.U p.2 := inf_le_right

theorem resM_chartEquiv_symm (hL : L.IsLB) (i : L.ι) {V W : X.Opens} (h : V ≤ L.U i) (h' : W ≤ V)
    (t : Γ(F, V)) : resM (twist F L) h' ((chartEquiv hL i h).symm t) =
      (chartEquiv hL i (h'.trans h)).symm (resM F h' t) := by
  rw [LinearEquiv.eq_symm_apply, chartEquiv_resM hL i h, LinearEquiv.apply_symm_apply]

def divFun (hL : L.IsLB) {V : X.Opens} (t : Γ(twist F N, V)) :
    Γ(twist (twist F L) (LB.div N L), V) :=
  mkSec (fun p : (LB.div N L).ι => (chartEquiv hL p.2 (inf_le_right.trans (div_U_le_right p))).symm
      (resM F (inf_le_inf_left V (div_U_le_left p)) (coord t p.1)))
    fun (p q : (LB.div N L).ι) => by
      have hp : V ⊓ (LB.div N L).U p ⊓ (LB.div N L).U q ≤ (LB.div N L).U p :=
        inf_le_left.trans inf_le_right
      have hq : V ⊓ (LB.div N L).U p ⊓ (LB.div N L).U q ≤ (LB.div N L).U q := inf_le_right
      apply (chartEquiv hL p.2 (hp.trans (div_U_le_right p))).injective
      rw [resM_chartEquiv_symm, resM_chartEquiv_symm, LinearEquiv.apply_symm_apply, map_smul,
        chartEquiv_change hL p.2 q.2 _ (hq.trans (div_U_le_right q)),
        LinearEquiv.apply_symm_apply, smul_smul, resG_div_g_mul p q _ _
          (le_inf (hp.trans (div_U_le_left p)) (hq.trans (div_U_le_left q))),
        resM_resM, resM_resM]
      exact coord_rel t p.1 q.1 _ _ _

theorem coord_divFun (hL : L.IsLB) {V : X.Opens} (t : Γ(twist F N, V)) (p : (LB.div N L).ι) :
    coord (divFun hL t) p = (chartEquiv hL p.2 (inf_le_right.trans (div_U_le_right p))).symm
      (resM F (inf_le_inf_left V (div_U_le_left p)) (coord t p.1)) := rfl

variable (F N) in

def divHom (hL : L.IsLB) : twist F N ⟶ twist (twist F L) (LB.div N L) :=
  homOfLinear
    (fun V =>
      { toFun := divFun hL
        map_add' := fun s t => sec_ext fun (p : (LB.div N L).ι) => by
          rw [coord_add, coord_divFun, coord_divFun, coord_divFun, coord_add, map_add, map_add]
        map_smul' := fun a s => sec_ext fun (p : (LB.div N L).ι) => by
          rw [RingHom.id_apply, coord_smul, coord_divFun, coord_divFun, coord_smul, resM_smul,
            map_smul, resG_resG] })
    fun h t => sec_ext fun (p : (LB.div N L).ι) => by
      change coord (divFun hL (resM _ h t)) p = coord (resM _ h (divFun hL t)) p
      rw [coord_resM, coord_divFun, coord_divFun, coord_resM, resM_chartEquiv_symm, resM_resM,
        resM_resM]

theorem coord_coord_divHom_app (hL : L.IsLB) {V : X.Opens} (t : Γ(twist F N, V)) (n : N.ι)
    (l' l : L.ι) {W : X.Opens} (h : W ≤ V ⊓ (LB.div N L).U (n, l') ⊓ L.U l) (hn : W ≤ V ⊓ N.U n)
    (hl : W ≤ L.U l ⊓ L.U l') :
    resM F h (coord (coord ((divHom F N hL).app V t) (n, l')) l) =
      resG X hl (L.g l l' : Γ(X, L.U l ⊓ L.U l')) • resM F hn (coord t n) := by
  change resM F h (_ • resM F _ (resM F _ _)) = _
  rw [resM_smul, resM_resM, resM_resM, resG_resG]

theorem chartEquiv_divHom_app (hL : L.IsLB) (hN : N.IsLB) (p : (LB.div N L).ι) {V : X.Opens}
    (h : V ≤ (LB.div N L).U p) (t : Γ(twist F N, V)) :
    chartEquiv hL p.2 (h.trans (div_U_le_right p))
      (chartEquiv (Semi.LB.isLB_div hN hL) p h ((divHom F N hL).app V t)) =
        chartEquiv hN p.1 (h.trans (div_U_le_left p)) t := by
  change chartEquiv hL _ _ (resM _ _ ((chartEquiv hL _ _).symm (resM F _ _))) = _
  rw [resM_chartEquiv_symm, LinearEquiv.apply_symm_apply, resM_resM, chartEquiv_apply]

theorem isIso_divHom (hL : L.IsLB) (hN : N.IsLB) : IsIso (divHom F N hL) :=
  isIso_of_cover _ (Semi.LB.isLB_div hN hL).cover fun p _ h =>
    bijective_of_eq_smul (chartEquiv hN p.1 (h.trans (div_U_le_left p))).bijective
      ((chartEquiv hL p.2 (h.trans (div_U_le_right p))).bijective.comp
        (chartEquiv (Semi.LB.isLB_div hN hL) p h).bijective) isUnit_one
      fun t => (chartEquiv_divHom_app hL hN p h t).trans (one_smul _ _).symm

@[reassoc] theorem divHom_naturality (hL : L.IsLB) (φ : F ⟶ G) :
    map N φ ≫ divHom G N hL = divHom F N hL ≫ map (LB.div N L) (map L φ) :=
  hom_ext fun V t p => sec_ext fun l => by
    change _ • resM G _ (resM G _ (φ.app _ _)) = φ.app _ (_ • resM F _ (resM F _ _))
    rw [Scheme.Modules.Hom.app_smul, app_resM, app_resM]

variable (F) in

def divIso (hL : L.IsLB) (hN : N.IsLB) : twist F N ≅ twist (twist F L) (LB.div N L) :=
  haveI := isIso_divHom (F := F) hL hN
  asIso (divHom F N hL)

theorem divIso_hom (hL : L.IsLB) (hN : N.IsLB) : (divIso F hL hN).hom = divHom F N hL := rfl

def divNatIso (hL : L.IsLB) (hN : N.IsLB) :
    twistFunctor N ≅ twistFunctor L ⋙ twistFunctor (LB.div N L) :=
  NatIso.ofComponents (fun F => divIso F hL hN) fun φ => divHom_naturality hL φ

theorem coord_divIso_inv_app (hL : L.IsLB) (hN : N.IsLB) {V : X.Opens}
    (s : Γ(twist (twist F L) (LB.div N L), V)) (n : N.ι) (l : L.ι) {W : X.Opens}
    (hn : W ≤ V ⊓ N.U n) (h : W ≤ V ⊓ (LB.div N L).U (n, l) ⊓ L.U l) :
    resM F hn (coord ((divIso F hL hN).inv.app V s) n) = resM F h (coord (coord s (n, l)) l) := by
  have e : (divHom F N hL).app V ((divIso F hL hN).inv.app V s) = s :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ V s) (divIso F hL hN).inv_hom_id
  have := coord_coord_divHom_app hL ((divIso F hL hN).inv.app V s) n l l h hn
    (le_inf (h.trans inf_le_right) (h.trans inf_le_right))
  rw [e, resG_g_self hL, one_smul] at this
  exact this.symm

def swapCoord {V : X.Opens} (s : Γ(twist (twist F L) M, V)) (l : L.ι) :
    Γ(twist F M, V ⊓ L.U l) :=
  mkSec (fun m => resM F (inf_right_comm V (L.U l) (M.U m)).le (coord (coord s m) l))
    fun m m' => by
      have h : V ⊓ L.U l ⊓ M.U m ⊓ M.U m' ≤ V ⊓ M.U m ⊓ M.U m' ⊓ L.U l :=
        le_inf (inf_le_inf_right _ (inf_le_inf_right _ inf_le_left))
          (inf_le_left.trans (inf_le_left.trans inf_le_right))
      have := congrArg (fun r => resM F h (coord r l)) (coord_mem s m m')
      simpa only [coord_resM, coord_smul, resM_smul, resM_resM, resG_resG] using this

theorem coord_swapCoord {V : X.Opens} (s : Γ(twist (twist F L) M, V)) (l : L.ι) (m : M.ι) :
    coord (swapCoord s l) m =
      resM F (inf_right_comm V (L.U l) (M.U m)).le (coord (coord s m) l) := rfl

def swapFun {V : X.Opens} (s : Γ(twist (twist F L) M, V)) : Γ(twist (twist F M) L, V) :=
  mkSec (swapCoord s) fun l l' => sec_ext fun m => by
    rw [coord_resM, coord_smul, coord_resM, coord_swapCoord, coord_swapCoord, resM_resM, resM_resM,
      resG_resG]
    exact coord_rel (coord s m) l l' _ _ _

theorem coord_coord_swapFun {V : X.Opens} (s : Γ(twist (twist F L) M, V)) (l : L.ι) (m : M.ι) :
    coord (coord (swapFun s) l) m =
      resM F (inf_right_comm V (L.U l) (M.U m)).le (coord (coord s m) l) := rfl

variable (F L M) in

def swapHom : twist (twist F L) M ⟶ twist (twist F M) L :=
  homOfLinear
    (fun V =>
      { toFun := swapFun
        map_add' := fun s t => sec_ext fun l => sec_ext fun m => by
          rw [coord_add, coord_add, coord_coord_swapFun, coord_coord_swapFun, coord_coord_swapFun,
            coord_add, coord_add, map_add]
        map_smul' := fun a s => sec_ext fun l => sec_ext fun m => by
          rw [RingHom.id_apply, coord_smul, coord_smul, coord_coord_swapFun, coord_coord_swapFun,
            coord_smul, coord_smul, resM_smul, resG_resG, resG_resG, resG_resG] })
    fun h s => sec_ext fun l => sec_ext fun m => by
      change coord (coord (swapFun (resM _ h s)) l) m = coord (coord (resM _ h (swapFun s)) l) m
      rw [coord_resM, coord_resM, coord_coord_swapFun, coord_coord_swapFun, coord_resM, coord_resM,
        resM_resM, resM_resM]

@[simp] theorem coord_coord_swapHom_app {V : X.Opens} (s : Γ(twist (twist F L) M, V)) (l : L.ι)
    (m : M.ι) : coord (coord ((swapHom F L M).app V s) l) m =
      resM F (inf_right_comm V (L.U l) (M.U m)).le (coord (coord s m) l) := rfl

theorem swapHom_swapHom : swapHom F L M ≫ swapHom F M L = 𝟙 _ :=
  hom_ext fun V s m => sec_ext fun l => by
    change coord (coord (swapFun (swapFun s)) m) l = coord (coord s m) l
    rw [coord_coord_swapFun, coord_coord_swapFun, resM_resM, resM_self]

variable (F L M) in

def swapIso : twist (twist F L) M ≅ twist (twist F M) L where
  hom := swapHom F L M
  inv := swapHom F M L
  hom_inv_id := swapHom_swapHom
  inv_hom_id := swapHom_swapHom

variable (L M) in

def swapNatIso : twistFunctor L ⋙ twistFunctor M ≅ twistFunctor M ⋙ twistFunctor L :=
  NatIso.ofComponents (fun F => swapIso F L M) fun φ =>
    hom_ext fun _ _ _ => sec_ext fun _ => (app_resM φ _ _).symm

variable (F) in

def homOfSec (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) : twist F L ⟶ twist F M :=
  secHom (twist F L) w ≫ (divIso F hL hM).inv

theorem coord_homOfSec_app (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) {V : X.Opens}
    (s : Γ(twist F L, V)) (p : M.ι) (q : L.ι) {W : X.Opens}
    (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q) (h : W ≤ M.U p ⊓ L.U q) :
    resM F hp (coord ((homOfSec F hL hM w).app V s) p) =
      resG X h (LB.homCoord w p q) • resM F hq (coord s q) := by
  have h' : W ≤ V ⊓ (LB.div M L).U (p, q) ⊓ L.U q :=
    le_inf (le_inf (hp.trans inf_le_left) h) (h.trans inf_le_right)
  refine (coord_divIso_inv_app hL hM ((secHom (twist F L) w).app V s) p q hp h').trans ?_
  have key (r : (LB.div M L).ι) (hr : W ≤ V ⊓ (LB.div M L).U r ⊓ L.U q) :
      resM F hr (coord (coord ((secHom (twist F L) w).app V s) r) q) =
        resG X (hr.trans (inf_le_left.trans inf_le_right)) (w.f r) • resM F hq (coord s q) := by
    rw [coord_secHom_app, coord_smul, coord_resM, resM_smul, resM_resM, resG_resG, resG_resG]
  exact key (p, q) h'

theorem chartEquiv_homOfSec_app (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) (p : M.ι)
    (q : L.ι) {V : X.Opens} (hp : V ≤ M.U p) (hq : V ≤ L.U q) (s : Γ(twist F L, V)) :
    chartEquiv hM p hp ((homOfSec F hL hM w).app V s) =
      resG X (le_inf hp hq) (LB.homCoord w p q) • chartEquiv hL q hq s :=
  coord_homOfSec_app hL hM w s p q _ _ _

@[reassoc] theorem homOfSec_naturality (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L))
    (φ : F ⟶ G) : map L φ ≫ homOfSec G hL hM w = homOfSec F hL hM w ≫ map M φ := by
  rw [homOfSec, homOfSec, secHom_naturality_assoc, Category.assoc]
  exact congrArg _ ((divNatIso hL hM).inv.naturality φ)

theorem bijective_homOfSec_app (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L))
    {V : X.Opens} (hV : V ≤ Out.nonzeroLocus w) :
    Function.Bijective ((homOfSec F hL hM w).app V) :=
  (ConcreteCategory.bijective_of_isIso ((divIso F hL hM).inv.app V)).comp
    (bijective_secHom_app (Semi.LB.isLB_div hM hL) w hV)

variable (F) in

def isoOfGen (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) :
    twist F L ≅ twist F M :=
  genIso (twist F L) (Semi.LB.isLB_div hM hL) w hw ≪≫ (divIso F hL hM).symm

theorem isoOfGen_hom (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) :
    (isoOfGen F hL hM w hw).hom = homOfSec F hL hM (DVR.genSec w hw) := rfl

def isoUnit (w : LB.Iso L M) (p : M.ι) (q : L.ι) : Γ(X, M.U p ⊓ L.U q)ˣ := w.s (p, q)

theorem coord_isoOfGen_hom_app (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(twist F L, V)) (p : M.ι) (q : L.ι) {W : X.Opens}
    (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q) (h : W ≤ M.U p ⊓ L.U q) :
    resM F hp (coord ((isoOfGen F hL hM w hw).hom.app V s) p) =
      resG X h (isoUnit w p q : Γ(X, M.U p ⊓ L.U q)) • resM F hq (coord s q) :=
  coord_homOfSec_app hL hM _ s p q hp hq h

def natIsoOfGen (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen) :
    twistFunctor L ≅ twistFunctor M :=
  NatIso.ofComponents (fun F => isoOfGen F hL hM w hw) fun φ => homOfSec_naturality hL hM _ φ

theorem nonempty_iso_of_lbIso (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M) :
    Nonempty (twist F L ≅ twist F M) :=
  let ⟨w, hw⟩ := h
  ⟨isoOfGen F hL hM w hw⟩

theorem eq_homOfSec (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L))
    (φ : twist F L ⟶ twist F M)
    (h : ∀ (V : X.Opens) (s : Γ(twist F L, V)) (p : M.ι) (q : L.ι),
      resM F (inf_le_left : V ⊓ M.U p ⊓ L.U q ≤ V ⊓ M.U p) (coord (φ.app V s) p) =
        resG X (inf_le_inf_right _ inf_le_right : V ⊓ M.U p ⊓ L.U q ≤ M.U p ⊓ L.U q)
          (LB.homCoord w p q) • resM F (inf_le_inf_right _ inf_le_left) (coord s q)) :
    φ = homOfSec F hL hM w := by
  ext V s : 3
  exact sec_ext_of_charts hL.cover fun p q =>
    (h V s p q).trans (coord_homOfSec_app hL hM w s p q _ _ _).symm

theorem isoOfGen_idIso_hom (hL : L.IsLB) :
    (isoOfGen F hL hL (idIso L) (idIso_isGen hL)).hom = 𝟙 _ :=
  (eq_homOfSec hL hL _ _ fun _ s p q => coord_rel s p q _ _ _).symm

theorem coord_isoOfGen_inv_app (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (t : Γ(twist F M, V)) (p : M.ι) (q : L.ι) {W : X.Opens}
    (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q) (h : W ≤ M.U p ⊓ L.U q) :
    resM F hq (coord ((isoOfGen F hL hM w hw).inv.app V t) q) =
      (((res h (isoUnit w p q))⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) • resM F hp (coord t p) := by
  have e : (isoOfGen F hL hM w hw).hom.app V ((isoOfGen F hL hM w hw).inv.app V t) = t :=
    congrArg (fun φ => Scheme.Modules.Hom.app φ V t) (isoOfGen F hL hM w hw).inv_hom_id
  have := coord_isoOfGen_hom_app hL hM w hw ((isoOfGen F hL hM w hw).inv.app V t) p q hp hq h
  rw [e] at this
  rw [this, ← val_res, smul_smul, Units.inv_mul, one_smul]

theorem homOfSec_comp (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) (w : LB.Sec (LB.div M L))
    (v : LB.Sec (LB.div N M)) (u : LB.Sec (LB.div N L))
    (h : ∀ (r : N.ι) (p : M.ι) (q : L.ι),
      resG X (inf_le_left : N.U r ⊓ L.U q ⊓ M.U p ≤ N.U r ⊓ L.U q) (LB.homCoord u r q) =
        resG X (inf_le_inf_right _ inf_le_left) (LB.homCoord v r p) *
          resG X (le_inf inf_le_right (inf_le_left.trans inf_le_right)) (LB.homCoord w p q)) :
    homOfSec F hL hM w ≫ homOfSec F hM hN v = homOfSec F hL hN u :=
  eq_homOfSec hL hN u _ fun V s r q => by
    refine sec_ext_of_cover (fun p => V ⊓ N.U r ⊓ L.U q ⊓ M.U p) (fun _ => inf_le_left)
      (le_iSup_inf hM.cover _) fun p => ?_
    have l : V ⊓ N.U r ⊓ L.U q ⊓ M.U p ≤ N.U r ⊓ L.U q ⊓ M.U p :=
      inf_le_inf_right _ (inf_le_inf_right _ inf_le_right)
    have lp : V ⊓ N.U r ⊓ L.U q ⊓ M.U p ≤ V ⊓ M.U p :=
      inf_le_inf_right _ (inf_le_left.trans inf_le_left)
    have lq : V ⊓ N.U r ⊓ L.U q ⊓ M.U p ≤ V ⊓ L.U q :=
      inf_le_left.trans (inf_le_inf_right _ inf_le_left)
    have e := congrArg (resG X l) (h r p q)
    rw [map_mul, resG_resG, resG_resG, resG_resG] at e
    rw [resM_smul, resM_resM, resM_resM, resG_resG, e, mul_smul,
      ← coord_homOfSec_app hL hM w s p q lp lq]
    exact coord_homOfSec_app hM hN v _ r p _ lp _

theorem homOfSec_unitTwistIso (hL : L.IsLB) (hM : M.IsLB) (w : LB.Sec (LB.div M L)) :
    homOfSec (unitMod X) hL hM w ≫ (unitTwistIso M).hom =
      (unitTwistIso L).hom ≫ LB.homOfSec hL hM w := by
  ext V s : 3
  exact LB.sec_ext_of_cover hL.cover fun p q =>
    (coord_homOfSec_app hL hM w s p q _ _ _).trans
      (LB.coord_mulFun' hL hM w ((unitTwistIso L).hom.app V s) p q).symm

variable (F) in

def twistTwistIso (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) (w : LB.Gen (LB.div (LB.div N L) M))
    (hw : w.IsGen) : twist (twist F L) M ≅ twist F N :=
  isoOfGen (twist F L) hM (Semi.LB.isLB_div hN hL) w hw ≪≫ (divIso F hL hN).symm

def tripleUnit (w : LB.Gen (LB.div (LB.div N L) M)) (n : N.ι) (l : L.ι) (m : M.ι) :
    Γ(X, N.U n ⊓ L.U l ⊓ M.U m)ˣ := w.s ((n, l), m)

theorem coord_twistTwistIso_hom_app (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (w : LB.Gen (LB.div (LB.div N L) M)) (hw : w.IsGen) {V : X.Opens}
    (s : Γ(twist (twist F L) M, V)) (n : N.ι) (l : L.ι) (m : M.ι) {W : X.Opens}
    (hn : W ≤ V ⊓ N.U n) (hm : W ≤ V ⊓ M.U m ⊓ L.U l) (h : W ≤ N.U n ⊓ L.U l ⊓ M.U m) :
    resM F hn (coord ((twistTwistIso F hL hM hN w hw).hom.app V s) n) =
      resG X h (tripleUnit w n l m : Γ(X, N.U n ⊓ L.U l ⊓ M.U m)) •
        resM F hm (coord (coord s m) l) := by
  have h₁ : W ≤ V ⊓ (LB.div N L).U (n, l) := le_inf (hn.trans inf_le_left) (h.trans inf_le_left)
  have h₂ : W ≤ L.U l := hm.trans inf_le_right
  refine (coord_divIso_inv_app hL hN
    ((isoOfGen (twist F L) hM (Semi.LB.isLB_div hN hL) w hw).hom.app V s) n l hn
    (le_inf h₁ h₂)).trans ?_
  have e := congrArg (fun r => resM F (le_inf le_rfl h₂ : W ≤ W ⊓ L.U l) (coord r l))
    (coord_isoOfGen_hom_app hM (Semi.LB.isLB_div hN hL) w hw s (n, l) m h₁
      (hm.trans inf_le_left) h)
  simp only [coord_resM, coord_smul, resM_smul, resM_resM, resG_resG] at e
  exact e.trans (congrArg (· • _) (resG_self _ _))

def twistTwistNatIso (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (w : LB.Gen (LB.div (LB.div N L) M)) (hw : w.IsGen) :
    twistFunctor L ⋙ twistFunctor M ≅ twistFunctor N :=
  (twistFunctor L).isoWhiskerLeft (natIsoOfGen hM (Semi.LB.isLB_div hN hL) w hw) ≪≫
    (divNatIso hL hN).symm

theorem twistTwistNatIso_hom_app (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (w : LB.Gen (LB.div (LB.div N L) M)) (hw : w.IsGen) (F : X.Modules) :
    (twistTwistNatIso hL hM hN w hw).hom.app F = (twistTwistIso F hL hM hN w hw).hom := rfl

@[reassoc] theorem twistTwistIso_naturality (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (w : LB.Gen (LB.div (LB.div N L) M)) (hw : w.IsGen) (φ : F ⟶ G) :
    map M (map L φ) ≫ (twistTwistIso G hL hM hN w hw).hom =
      (twistTwistIso F hL hM hN w hw).hom ≫ map N φ :=
  (twistTwistNatIso hL hM hN w hw).hom.naturality φ

theorem nonempty_twistTwistIso (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB)
    (h : LBIso M (LB.div N L)) : Nonempty (twist (twist F L) M ≅ twist F N) :=
  let ⟨w, hw⟩ := h
  ⟨twistTwistIso F hL hM hN w hw⟩

def twistToModIso (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) (w : LB.Gen (LB.div (LB.div N L) M))
    (hw : w.IsGen) : twist (toMod L) M ≅ toMod N :=
  (twistFunctor M).mapIso (unitTwistIso L).symm ≪≫ twistTwistIso (unitMod X) hL hM hN w hw ≪≫
    unitTwistIso N

def twistInvNatIso (hL : L.IsLB) :
    𝟭 X.Modules ≅ twistFunctor L ⋙ twistFunctor (LB.div (LB.triv X) L) :=
  genNatIso (LB.isLB_triv X) _ isGen_one_triv ≪≫ divNatIso hL (LB.isLB_triv X)

def twistEquivalence (hL : L.IsLB) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (twistFunctor L) (twistFunctor (LB.div (LB.triv X) L))
    (twistInvNatIso hL) (swapNatIso _ _ ≪≫ (twistInvNatIso hL).symm)

@[simp] theorem twistEquivalence_functor (hL : L.IsLB) :
    (twistEquivalence hL).functor = twistFunctor L := rfl

@[simp] theorem twistEquivalence_inverse (hL : L.IsLB) :
    (twistEquivalence hL).inverse = twistFunctor (LB.div (LB.triv X) L) := rfl

theorem isEquivalence_twistFunctor (hL : L.IsLB) : (twistFunctor L).IsEquivalence :=
  (twistEquivalence hL).isEquivalence_functor

theorem preservesLimits_twistFunctor (hL : L.IsLB) : Limits.PreservesLimits (twistFunctor L) :=
  haveI := isEquivalence_twistFunctor hL
  inferInstance

theorem preservesColimits_twistFunctor (hL : L.IsLB) :
    Limits.PreservesColimits (twistFunctor L) :=
  haveI := isEquivalence_twistFunctor hL
  inferInstance

theorem preservesFiniteLimits_twistFunctor (hL : L.IsLB) :
    Limits.PreservesFiniteLimits (twistFunctor L) :=
  haveI := isEquivalence_twistFunctor hL
  inferInstance

theorem preservesFiniteColimits_twistFunctor (hL : L.IsLB) :
    Limits.PreservesFiniteColimits (twistFunctor L) :=
  haveI := isEquivalence_twistFunctor hL
  inferInstance

theorem exact_map_iff (hL : L.IsLB) (S : ShortComplex X.Modules) :
    (S.map (twistFunctor L)).Exact ↔ S.Exact :=
  haveI := isEquivalence_twistFunctor hL
  S.exact_map_iff_of_faithful (twistFunctor L)

theorem shortExact_map (hL : L.IsLB) {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (twistFunctor L)).ShortExact :=
  haveI := isEquivalence_twistFunctor hL
  hS.map_of_exact (twistFunctor L)

theorem mono_map_iff (hL : L.IsLB) (φ : F ⟶ G) : Mono (map L φ) ↔ Mono φ :=
  haveI := isEquivalence_twistFunctor hL
  (twistFunctor L).mono_map_iff_mono φ

theorem epi_map_iff (hL : L.IsLB) (φ : F ⟶ G) : Epi (map L φ) ↔ Epi φ :=
  haveI := isEquivalence_twistFunctor hL
  (twistFunctor L).epi_map_iff_epi φ

theorem isIso_map_iff (hL : L.IsLB) (φ : F ⟶ G) : IsIso (map L φ) ↔ IsIso φ :=
  haveI := isEquivalence_twistFunctor hL
  isIso_iff_of_reflects_iso φ (twistFunctor L)

theorem isZero_twist_iff (hL : L.IsLB) : Limits.IsZero (twist F L) ↔ Limits.IsZero F :=
  ⟨fun h => ((twistFunctor _).map_isZero h).of_iso ((twistInvNatIso hL).app F),
    fun h => (twistFunctor L).map_isZero h⟩

section PushPull

variable (f : Y ⟶ X)

theorem le_pull_inf (V : X.Opens) (i : L.ι) :
    f ⁻¹ᵁ (V ⊓ L.U i) ≤ f ⁻¹ᵁ V ⊓ (L.pull f).U fun _ => i :=
  fun _ hx => ⟨hx.1, (LB.pull_U f fun _ => i).ge hx.2⟩

set_option backward.isDefEq.respectTransparency false in

def projFun {G : Y.Modules} {V : X.Opens} (s : Γ(twist G (L.pull f), f ⁻¹ᵁ V)) :
    Γ(twist ((Scheme.Modules.pushforward f).obj G) L, V) :=
  mkSec (fun i => resM G (le_pull_inf f V i) (coord s fun _ => i)) fun i j => by
    have hi : f ⁻¹ᵁ (V ⊓ L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ (V ⊓ L.U i) := f.preimage_mono inf_le_left
    have hj : f ⁻¹ᵁ (V ⊓ L.U i ⊓ L.U j) ≤ f ⁻¹ᵁ (V ⊓ L.U j) :=
      f.preimage_mono (inf_le_inf_right _ inf_le_left)
    change resM G hi (resM G (le_pull_inf f V i) (coord s fun _ => i)) =
      (f.app (V ⊓ L.U i ⊓ L.U j)).hom (resG X (inf_le_inf_right _ inf_le_right)
        (L.g i j : Γ(X, L.U i ⊓ L.U j))) •
          resM G hj (resM G (le_pull_inf f V j) (coord s fun _ => j))
    rw [resM_resM, resM_resM, coord_rel s (fun _ => i) (fun _ => j) _ (hj.trans (le_pull_inf f V j))
      (le_inf ((hi.trans (le_pull_inf f V i)).trans inf_le_right)
        ((hj.trans (le_pull_inf f V j)).trans inf_le_right)),
      LB.resG_pull_g, ← Scheme.Hom.appLE_eq_app, LB.appLE_resG]

set_option backward.isDefEq.respectTransparency false in

def projInv {G : Y.Modules} {V : X.Opens}
    (s : Γ(twist ((Scheme.Modules.pushforward f).obj G) L, V)) :
    Γ(twist G (L.pull f), f ⁻¹ᵁ V) :=
  mkSec (fun j => resM G (LB.pull_inf_le f V j) (coord s (j PUnit.unit))) fun i j => by
    have e : f ⁻¹ᵁ V ⊓ (L.pull f).U i ⊓ (L.pull f).U j ≤
        f ⁻¹ᵁ (V ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.pull_inf_le f V i) (LB.pull_U_le f j)
    have h : resM G (f.preimage_mono inf_le_left) (coord s (i PUnit.unit)) =
        (f.app (V ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))).hom
          (resG X (inf_le_inf_right _ inf_le_right) (L.g (i PUnit.unit) (j PUnit.unit) :
            Γ(X, L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)))) •
          resM G (f.preimage_mono (inf_le_inf_right _ inf_le_left)) (coord s (j PUnit.unit)) :=
      coord_mem s (i PUnit.unit) (j PUnit.unit)
    have := congrArg (resM G e) h
    rw [resM_smul, resM_resM, resM_resM, LB.resG_app, LB.appLE_resG] at this
    rw [resM_resM, resM_resM, LB.resG_pull_g]
    exact this

variable (L) in

def projIso (G : Y.Modules) :
    (Scheme.Modules.pushforward f).obj (twist G (L.pull f)) ≅
      twist ((Scheme.Modules.pushforward f).obj G) L :=
  isoOfLinear (F := (Scheme.Modules.pushforward f).obj (twist G (L.pull f)))
    (fun V =>
      { toFun := projFun f
        invFun := projInv f
        map_add' := fun s t => sec_ext fun i => map_add (resM G (le_pull_inf f V i)) _ _
        map_smul' := fun a s => sec_ext fun i => by
          change resM G (le_pull_inf f V i)
              (resG Y (inf_le_left : f ⁻¹ᵁ V ⊓ (L.pull f).U (fun _ => i) ≤ f ⁻¹ᵁ V)
                ((f.app V).hom a) • coord (F := G) (V := f ⁻¹ᵁ V) s fun _ => i) =
            (f.app (V ⊓ L.U i)).hom (resG X inf_le_left a) •
              resM G (le_pull_inf f V i) (coord (F := G) (V := f ⁻¹ᵁ V) s fun _ => i)
          rw [resM_smul, resG_resG, LB.resG_app, ← Scheme.Hom.appLE_eq_app, LB.appLE_resG]
        left_inv := fun s => sec_ext (F := G) fun j =>
          (resM_resM (le_pull_inf f V _) (LB.pull_inf_le f V j) _).trans (resM_self _ _)
        right_inv := fun s => sec_ext fun i =>
          (resM_resM (F := G) (LB.pull_inf_le f V _) (le_pull_inf f V i) _).trans (resM_self _ _) })
    fun {V W} h s => sec_ext fun i =>
      (resM_resM (F := G) _ (le_pull_inf f W i) _).trans
        (resM_resM (F := G) (le_pull_inf f V i) (f.preimage_mono (inf_le_inf_right _ h)) _).symm

theorem coord_projIso_hom_app (G : Y.Modules) {V : X.Opens}
    (s : Γ(twist G (L.pull f), f ⁻¹ᵁ V)) (i : L.ι) :
    (coord ((projIso L f G).hom.app V s) i : Γ(G, f ⁻¹ᵁ (V ⊓ L.U i))) =
      resM G (le_pull_inf f V i) (coord s fun _ => i) := rfl

theorem coord_projIso_inv_app (G : Y.Modules) {V : X.Opens}
    (s : Γ(twist ((Scheme.Modules.pushforward f).obj G) L, V)) (j : (L.pull f).ι) :
    coord (F := G) (V := f ⁻¹ᵁ V) ((projIso L f G).inv.app V s) j =
      resM G (LB.pull_inf_le f V j) (coord s (j PUnit.unit)) := rfl

variable (L) in

def projNatIso : twistFunctor (L.pull f) ⋙ Scheme.Modules.pushforward f ≅
    Scheme.Modules.pushforward f ⋙ twistFunctor L :=
  NatIso.ofComponents (projIso L f) fun φ =>
    hom_ext fun V _ i => (app_resM φ (le_pull_inf f V i) _).symm

variable (F L) in

def pullbackHom : (Scheme.Modules.pullback f).obj (twist F L) ⟶
    twist ((Scheme.Modules.pullback f).obj F) (L.pull f) :=
  mateHom (Scheme.Modules.pullbackPushforwardAdjunction f) (twistFunctor L)
    (twistFunctor (L.pull f)) (projNatIso L f).symm F

theorem coord_pullbackHom_app_unit {V : X.Opens} (s : Γ(twist F L, V)) (j : (L.pull f).ι) :
    coord ((pullbackHom F L f).app (f ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (twist F L)).app V s)) j =
    resM ((Scheme.Modules.pullback f).obj F) (LB.pull_inf_le f V j)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app _
        (coord s (j PUnit.unit))) := by
  have e : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (twist F L) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom F L f) =
        map L ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) ≫
          (projIso L f _).inv :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  exact congrArg (fun φ => coord (F := (Scheme.Modules.pullback f).obj F) (V := f ⁻¹ᵁ V)
    (Scheme.Modules.Hom.app φ V s) j) e

@[reassoc] theorem pullbackHom_naturality (φ : F ⟶ G) :
    (Scheme.Modules.pullback f).map (map L φ) ≫ pullbackHom G L f =
      pullbackHom F L f ≫ map (L.pull f) ((Scheme.Modules.pullback f).map φ) :=
  mateHom_naturality _ (twistFunctor L) (twistFunctor (L.pull f)) _ φ

theorem isIso_pullbackHom (hL : L.IsLB) : IsIso (pullbackHom F L f) :=
  haveI := isEquivalence_twistFunctor hL
  haveI := isEquivalence_twistFunctor (Semi.LB.isLB_pull hL f)
  isIso_mateHom _ _ _ _ _

variable (F) in

def pullbackIso (hL : L.IsLB) : (Scheme.Modules.pullback f).obj (twist F L) ≅
    twist ((Scheme.Modules.pullback f).obj F) (L.pull f) :=
  haveI := isIso_pullbackHom (F := F) f hL
  asIso (pullbackHom F L f)

theorem pullbackIso_hom (hL : L.IsLB) : (pullbackIso F f hL).hom = pullbackHom F L f := rfl

def pullbackNatIso (hL : L.IsLB) : twistFunctor L ⋙ Scheme.Modules.pullback f ≅
    Scheme.Modules.pullback f ⋙ twistFunctor (L.pull f) :=
  NatIso.ofComponents (fun F => pullbackIso F f hL) fun φ => pullbackHom_naturality f φ

end PushPull

section Refine

variable (r : M.ι → L.ι) (hU : ∀ m, M.U m ≤ L.U (r m))
  (hg : ∀ m m', M.g m m' = res (inf_le_inf (hU m) (hU m')) (L.g (r m) (r m')))

variable (F) in

def refineHom : twist F L ⟶ twist F M :=
  homOfLinear
    (fun V =>
      { toFun := fun s => mkSec (fun m => resM F (inf_le_inf_left V (hU m)) (coord s (r m)))
          fun m m' => by
            rw [resM_resM, resM_resM, hg, val_res, resG_resG]
            exact coord_rel s _ _ _ _ _
        map_add' := fun s t => sec_ext fun m => map_add (resM F (inf_le_inf_left V (hU m))) _ _
        map_smul' := fun a s => sec_ext fun m =>
          (resM_smul (inf_le_inf_left V (hU m)) _ _).trans (congrArg (· • _) (resG_resG _ _ _)) })
    fun {V W} h s => sec_ext fun m =>
      (resM_resM _ (inf_le_inf_left W (hU m)) _).trans
        (resM_resM (inf_le_inf_left V (hU m)) _ _).symm

@[simp] theorem coord_refineHom_app {V : X.Opens} (s : Γ(twist F L, V)) (m : M.ι) :
    coord ((refineHom F r hU hg).app V s) m =
      resM F (inf_le_inf_left V (hU m)) (coord s (r m)) := rfl

@[reassoc] theorem refineHom_naturality (φ : F ⟶ G) :
    map L φ ≫ refineHom G r hU hg = refineHom F r hU hg ≫ map M φ :=
  hom_ext fun V _ m => (app_resM φ (inf_le_inf_left V (hU m)) _).symm

theorem isIso_refineHom (hL : L.IsLB) (hM : M.IsLB) : IsIso (refineHom F r hU hg) :=
  isIso_of_cover _ hM.cover fun m _ h =>
    bijective_of_eq_smul (chartEquiv hL (r m) (h.trans (hU m))).bijective
      (chartEquiv hM m h).bijective isUnit_one fun s => by
        rw [one_smul, chartEquiv_apply, chartEquiv_apply, coord_refineHom_app, resM_resM]

variable (F) in

def refineIso (hL : L.IsLB) (hM : M.IsLB) : twist F L ≅ twist F M :=
  haveI := isIso_refineHom (F := F) r hU hg hL hM
  asIso (refineHom F r hU hg)

theorem refineIso_hom (hL : L.IsLB) (hM : M.IsLB) :
    (refineIso F r hU hg hL hM).hom = refineHom F r hU hg := rfl

end Refine

end Twist

abbrev lbZPow {X : Scheme.{0}} (L : LB X) (n : ℤ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => n)

abbrev twistZ {X : Scheme.{0}} (F : X.Modules) (L : LB X) (n : ℤ) : X.Modules :=
  twist F (lbZPow L n)

namespace Twist

variable {X Y : Scheme.{0}} {F G H : X.Modules} {L M N : LB X}

section Pow

variable {n m m' k k' l : ℤ}

theorem lbZPow_natCast (L : LB X) (n : ℕ) : lbZPow L n = lbPow L n := rfl

theorem twistZ_natCast (F : X.Modules) (L : LB X) (n : ℕ) :
    twistZ F L n = twist F (lbPow L n) := rfl

theorem isLB_lbZPow (hL : L.IsLB) (n : ℤ) : (lbZPow L n).IsLB := Semi.LB.isLB_linComb hL _ _

variable (L) in

def zidx (n : ℤ) (i : L.ι) : (lbZPow L n).ι := fun _ => i

theorem zpow_U_le (j : (lbZPow L n).ι) : (lbZPow L n).U j ≤ L.U (j PUnit.unit) :=
  Semi.LB.wchart_le L (fun _ : PUnit.{1} => 𝟙 X) j PUnit.unit

theorem le_zpow_U (j : (lbZPow L n).ι) : L.U (j PUnit.unit) ≤ (lbZPow L n).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem le_zidx_U (n : ℤ) (i : L.ι) : L.U i ≤ (lbZPow L n).U (zidx L n i) :=
  le_zpow_U (zidx L n i)

theorem res_zpow_g (i j : (lbZPow L n).ι) {W : X.Opens}
    (h : W ≤ (lbZPow L n).U i ⊓ (lbZPow L n).U j)
    (h' : W ≤ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :
    res h ((lbZPow L n).g i j) = res h' (L.g (i PUnit.unit) (j PUnit.unit)) ^ n := by
  have := Semi.LB.res_lcg L (fun _ : PUnit.{1} => 𝟙 X) (fun _ => n) i j h
  rw [Fintype.prod_unique] at this
  exact this

def zcoord {V : X.Opens} (s : Γ(twistZ F L n, V)) (i : L.ι) : Γ(F, V ⊓ L.U i) :=
  resM F (inf_le_inf_left V (le_zidx_U n i)) (coord s (zidx L n i))

theorem zcoord_rel {V : X.Opens} (s : Γ(twistZ F L n, V)) (i j : L.ι)
    {W : X.Opens} (hi : W ≤ V ⊓ L.U i) (hj : W ≤ V ⊓ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resM F hi (zcoord s i) =
      ((res hij (L.g i j) ^ n : Γ(X, W)ˣ) : Γ(X, W)) • resM F hj (zcoord s j) := by
  have h := hij.trans (inf_le_inf (le_zidx_U n i) (le_zidx_U n j))
  rw [zcoord, zcoord, resM_resM, resM_resM, coord_rel s (zidx L n i) (zidx L n j) _ _ h, ← val_res,
    res_zpow_g _ _ h hij]
  rfl

theorem coord_eq_zcoord {V : X.Opens} (s : Γ(twistZ F L n, V)) (j : (lbZPow L n).ι) :
    coord s j = resM F (inf_le_inf_left V (zpow_U_le j)) (zcoord s (j PUnit.unit)) :=
  ((resM_resM _ _ _).trans (resM_self _ _)).symm

theorem zsec_ext {V : X.Opens} {s t : Γ(twistZ F L n, V)} (h : ∀ i, zcoord s i = zcoord t i) :
    s = t :=
  sec_ext fun j => by rw [coord_eq_zcoord, coord_eq_zcoord, h]

def zmkSec {V : X.Opens} (f : ∀ i, Γ(F, V ⊓ L.U i))
    (hf : ∀ i j, resM F (inf_le_left : V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i) (f i) =
      ((res (inf_le_inf_right _ inf_le_right : V ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) (L.g i j) ^ n :
        Γ(X, V ⊓ L.U i ⊓ L.U j)ˣ) : Γ(X, V ⊓ L.U i ⊓ L.U j)) •
          resM F (inf_le_inf_right _ inf_le_left) (f j)) : Γ(twistZ F L n, V) :=
  mkSec (fun j => resM F (inf_le_inf_left V (zpow_U_le j)) (f (j PUnit.unit))) fun i j => by
    have h : V ⊓ (lbZPow L n).U i ⊓ (lbZPow L n).U j ≤
        V ⊓ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit) :=
      inf_le_inf (inf_le_inf_left V (zpow_U_le i)) (zpow_U_le j)
    have := congrArg (resM F h) (hf (i PUnit.unit) (j PUnit.unit))
    rw [resM_smul, resM_resM, resM_resM, ← val_res, map_zpow, Semi.LB.res_res] at this
    rw [resM_resM, resM_resM, ← val_res,
      res_zpow_g i j _ (h.trans (inf_le_inf_right _ inf_le_right))]
    exact this

@[simp] theorem zcoord_zmkSec {V : X.Opens} (f : ∀ i, Γ(F, V ⊓ L.U i)) (hf) (i : L.ι) :
    zcoord (zmkSec (n := n) f hf) i = f i :=
  (resM_resM _ _ _).trans (resM_self _ _)

@[simp] theorem zcoord_zero {V : X.Opens} (i : L.ι) : zcoord (0 : Γ(twistZ F L n, V)) i = 0 :=
  map_zero (resM F _)

@[simp] theorem zcoord_add {V : X.Opens} (s t : Γ(twistZ F L n, V)) (i : L.ι) :
    zcoord (s + t) i = zcoord s i + zcoord t i := map_add (resM F _) _ _

@[simp] theorem zcoord_smul {V : X.Opens} (a : Γ(X, V)) (s : Γ(twistZ F L n, V)) (i : L.ι) :
    zcoord (a • s) i = resG X (inf_le_left : V ⊓ L.U i ≤ V) a • zcoord s i := by
  rw [zcoord, zcoord, coord_smul, resM_smul, resG_resG]

@[simp] theorem zcoord_resM {V W : X.Opens} (h : W ≤ V) (s : Γ(twistZ F L n, V)) (i : L.ι) :
    zcoord (resM (twistZ F L n) h s) i = resM F (inf_le_inf_right _ h) (zcoord s i) := by
  rw [zcoord, zcoord, coord_resM, resM_resM, resM_resM]

@[simp] theorem zcoord_map_app (φ : F ⟶ G) {V : X.Opens} (s : Γ(twistZ F L n, V)) (i : L.ι) :
    zcoord ((map (lbZPow L n) φ).app V s) i = φ.app _ (zcoord s i) := (app_resM φ _ _).symm

@[simp] theorem zcoord_eqToHom_app (h : n = k) (e : twistZ F L n = twistZ F L k) {V : X.Opens}
    (s : Γ(twistZ F L n, V)) (i : L.ι) :
    zcoord (Scheme.Modules.Hom.app (eqToHom e) V s) i = zcoord s i := by
  subst h
  rfl

theorem zhom_ext {φ ψ : G ⟶ twistZ F L n}
    (h : ∀ (V : X.Opens) (s : Γ(G, V)) (i : L.ι), zcoord (φ.app V s) i = zcoord (ψ.app V s) i) :
    φ = ψ := by
  ext V s : 3
  exact zsec_ext (h V s)

def zchartEquiv (hL : L.IsLB) (n : ℤ) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i) :
    Γ(twistZ F L n, V) ≃ₗ[Γ(X, V)] Γ(F, V) :=
  chartEquiv (isLB_lbZPow hL n) (zidx L n i) (h.trans (le_zidx_U n i))

theorem zchartEquiv_apply (hL : L.IsLB) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (s : Γ(twistZ F L n, V)) :
    zchartEquiv hL n i h s = resM F (le_inf le_rfl h) (zcoord s i) := (resM_resM _ _ _).symm

theorem zchartEquiv_resM (hL : L.IsLB) (i : L.ι) {V W : X.Opens} (h : V ≤ L.U i) (h' : W ≤ V)
    (s : Γ(twistZ F L n, V)) :
    zchartEquiv hL n i (h'.trans h) (resM (twistZ F L n) h' s) =
      resM F h' (zchartEquiv hL n i h s) :=
  chartEquiv_resM _ _ _ h' s

theorem zchartEquiv_change (hL : L.IsLB) (i j : L.ι) {V : X.Opens} (hi : V ≤ L.U i)
    (hj : V ≤ L.U j) (s : Γ(twistZ F L n, V)) :
    zchartEquiv hL n i hi s =
      ((res (le_inf hi hj) (L.g i j) ^ n : Γ(X, V)ˣ) : Γ(X, V)) • zchartEquiv hL n j hj s := by
  rw [zchartEquiv_apply, zchartEquiv_apply]
  exact zcoord_rel s i j _ _ _

def zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) : Γ(X, L.U i) :=
  resG X (le_zidx_U m i) (σ.f (zidx L m i))

theorem zfun_rel (σ : LB.Sec (lbZPow L m)) (i j : L.ι) {W : X.Opens} (hi : W ≤ L.U i)
    (hj : W ≤ L.U j) (hij : W ≤ L.U i ⊓ L.U j) :
    resG X hi (zfun σ i) =
      ((res hij (L.g i j) ^ m : Γ(X, W)ˣ) : Γ(X, W)) * resG X hj (zfun σ j) := by
  have h := hij.trans (inf_le_inf (le_zidx_U m i) (le_zidx_U m j))
  rw [zfun, zfun, resG_resG, resG_resG, LB.sec_rel σ (zidx L m i) (zidx L m j) _ _ h, ← val_res,
    res_zpow_g _ _ h hij]
  rfl

theorem f_eq_zfun (σ : LB.Sec (lbZPow L m)) (j : (lbZPow L m).ι) :
    σ.f j = resG X (zpow_U_le j) (zfun σ (j PUnit.unit)) :=
  ((resG_resG _ _ _).trans (resG_self _ _)).symm

theorem zglobal_ext {σ τ : LB.Sec (lbZPow L m)} (h : ∀ i, zfun σ i = zfun τ i) : σ = τ :=
  LB.f_injective (funext fun j => by rw [f_eq_zfun, f_eq_zfun, h])

def zmkGlobal (f : ∀ i, Γ(X, L.U i))
    (hf : ∀ i j, resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (f i) =
      ((L.g i j ^ m : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * resG X inf_le_right (f j)) :
    LB.Sec (lbZPow L m) where
  f j := resG X (zpow_U_le j) (f (j PUnit.unit))
  compat i j := by
    have h := inf_le_inf (zpow_U_le i) (zpow_U_le j)
    have := congrArg (resG X h) (hf (i PUnit.unit) (j PUnit.unit))
    rw [map_mul, resG_resG, resG_resG, ← val_res, map_zpow, ← res_zpow_g i j le_rfl h, val_res,
      resG_self] at this
    exact (resG_resG _ _ _).trans (this.trans (congrArg (_ * ·) (resG_resG _ _ _).symm))

@[simp] theorem zfun_zmkGlobal (f : ∀ i, Γ(X, L.U i)) (hf) (i : L.ι) :
    zfun (zmkGlobal (m := m) f hf) i = f i :=
  (resG_resG _ _ _).trans (resG_self _ _)

@[simp] theorem zfun_zero (i : L.ι) : zfun (0 : LB.Sec (lbZPow L m)) i = 0 :=
  map_zero (resG X _)

@[simp] theorem zfun_add (σ τ : LB.Sec (lbZPow L m)) (i : L.ι) :
    zfun (σ + τ) i = zfun σ i + zfun τ i := map_add (resG X _) _ _

@[simp] theorem zfun_smul (a : Γ(X, ⊤)) (σ : LB.Sec (lbZPow L m)) (i : L.ι) :
    zfun (a • σ) i = resG X le_top a * zfun σ i := by
  rw [zfun, zfun, LB.smul_f, map_mul, resG_resG]

variable (L) in

def zone : LB.Sec (lbZPow L 0) :=
  zmkGlobal (fun _ => 1) fun i j => by rw [zpow_zero, map_one, map_one, Units.val_one, mul_one]

@[simp] theorem zfun_zone (i : L.ι) : zfun (zone L) i = 1 := zfun_zmkGlobal _ _ i

def zofSec (σ : LB.Sec L) : LB.Sec (lbZPow L 1) :=
  zmkGlobal σ.f fun i j => by rw [zpow_one]; exact σ.compat i j

@[simp] theorem zfun_zofSec (σ : LB.Sec L) (i : L.ι) : zfun (zofSec σ) i = σ.f i :=
  zfun_zmkGlobal _ _ i

def zmul (σ : LB.Sec (lbZPow L m)) (τ : LB.Sec (lbZPow L m')) : LB.Sec (lbZPow L (m + m')) :=
  zmkGlobal (fun i => zfun σ i * zfun τ i) fun i j => by
    have e : res (le_refl (L.U i ⊓ L.U j)) (L.g i j) = L.g i j := Units.ext (resG_self _ _)
    rw [map_mul, map_mul, zfun_rel σ i j _ inf_le_right le_rfl, zfun_rel τ i j _ inf_le_right le_rfl,
      e, zpow_add, Units.val_mul, mul_mul_mul_comm]

@[simp] theorem zfun_zmul (σ : LB.Sec (lbZPow L m)) (τ : LB.Sec (lbZPow L m')) (i : L.ι) :
    zfun (zmul σ τ) i = zfun σ i * zfun τ i := zfun_zmkGlobal _ _ i

theorem isUnit_resG_zfun (σ : LB.Sec (lbZPow L m)) (i : L.ι) {V : X.Opens} (h : V ≤ L.U i)
    (hV : V ≤ Out.nonzeroLocus σ) : IsUnit (resG X h (zfun σ i)) := by
  rw [zfun, resG_resG]
  exact isUnit_resG_f σ _ _ hV

def mulFun (σ : LB.Sec (lbZPow L m)) (h : n + m = k) {V : X.Opens} (s : Γ(twistZ F L n, V)) :
    Γ(twistZ F L k, V) :=
  zmkSec (fun i => resG X (inf_le_right : V ⊓ L.U i ≤ L.U i) (zfun σ i) • zcoord s i) fun i j => by
    have hij : V ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j := inf_le_inf_right _ inf_le_right
    rw [resM_smul, resM_smul, resG_resG, resG_resG, zfun_rel σ i j _ inf_le_right hij,
      zcoord_rel s i j _ (inf_le_inf_right _ inf_le_left) hij, smul_smul, smul_smul, ← h, zpow_add,
      Units.val_mul, mul_right_comm, mul_comm (Units.val _) (Units.val _)]

theorem zcoord_mulFun (σ : LB.Sec (lbZPow L m)) (h : n + m = k) {V : X.Opens}
    (s : Γ(twistZ F L n, V)) (i : L.ι) :
    zcoord (mulFun σ h s) i = resG X (inf_le_right : V ⊓ L.U i ≤ L.U i) (zfun σ i) • zcoord s i :=
  zcoord_zmkSec _ _ i

variable (F) in

def mulSecOfEq (σ : LB.Sec (lbZPow L m)) (h : n + m = k) : twistZ F L n ⟶ twistZ F L k :=
  homOfLinear
    (fun V =>
      { toFun := mulFun σ h
        map_add' := fun s t => zsec_ext fun i => by
          rw [zcoord_add, zcoord_mulFun, zcoord_mulFun, zcoord_mulFun, zcoord_add, smul_add]
        map_smul' := fun a s => zsec_ext fun i => by
          rw [RingHom.id_apply, zcoord_smul, zcoord_mulFun, zcoord_mulFun, zcoord_smul, smul_comm] })
    fun h' s => zsec_ext fun i => by
      change zcoord (mulFun σ h (resM _ h' s)) i = zcoord (resM _ h' (mulFun σ h s)) i
      rw [zcoord_resM, zcoord_mulFun, zcoord_mulFun, zcoord_resM, resM_smul, resG_resG]

variable (F) in

abbrev mulSec (σ : LB.Sec (lbZPow L m)) (n : ℤ) : twistZ F L n ⟶ twistZ F L (n + m) :=
  mulSecOfEq F σ rfl

@[simp] theorem zcoord_mulSecOfEq_app (σ : LB.Sec (lbZPow L m)) (h : n + m = k) {V : X.Opens}
    (s : Γ(twistZ F L n, V)) (i : L.ι) :
    zcoord ((mulSecOfEq F σ h).app V s) i =
      resG X (inf_le_right : V ⊓ L.U i ≤ L.U i) (zfun σ i) • zcoord s i :=
  zcoord_mulFun σ h s i

theorem zchartEquiv_mulSecOfEq_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) (h : n + m = k)
    (i : L.ι) {V : X.Opens} (hi : V ≤ L.U i) (s : Γ(twistZ F L n, V)) :
    zchartEquiv hL k i hi ((mulSecOfEq F σ h).app V s) =
      resG X hi (zfun σ i) • zchartEquiv hL n i hi s := by
  rw [zchartEquiv_apply, zchartEquiv_apply, zcoord_mulSecOfEq_app, resM_smul, resG_resG]

@[reassoc] theorem mulSec_eqToHom (σ : LB.Sec (lbZPow L m)) (h : n + m = k) :
    mulSec F σ n ≫ eqToHom (congrArg (twistZ F L) h) = mulSecOfEq F σ h := by
  subst h
  exact Category.comp_id _

@[reassoc] theorem mulSecOfEq_naturality (σ : LB.Sec (lbZPow L m)) (h : n + m = k) (φ : F ⟶ G) :
    map (lbZPow L n) φ ≫ mulSecOfEq G σ h = mulSecOfEq F σ h ≫ map (lbZPow L k) φ :=
  zhom_ext fun V s i => by
    change zcoord ((mulSecOfEq G σ h).app V ((map (lbZPow L n) φ).app V s)) i =
      zcoord ((map (lbZPow L k) φ).app V ((mulSecOfEq F σ h).app V s)) i
    rw [zcoord_mulSecOfEq_app, zcoord_map_app, zcoord_map_app, zcoord_mulSecOfEq_app,
      Scheme.Modules.Hom.app_smul]

def mulSecNatTrans (σ : LB.Sec (lbZPow L m)) (h : n + m = k) :
    twistFunctor (lbZPow L n) ⟶ twistFunctor (lbZPow L k) where
  app F := mulSecOfEq F σ h
  naturality _ _ φ := mulSecOfEq_naturality σ h φ

theorem mulSecOfEq_comp_of_zfun {m'' : ℤ} (σ : LB.Sec (lbZPow L m)) (τ : LB.Sec (lbZPow L m'))
    (ρ : LB.Sec (lbZPow L m'')) (hρ : ∀ i, zfun ρ i = zfun σ i * zfun τ i)
    (h₁ : n + m = k) (h₂ : k + m' = l) (h₃ : n + m'' = l) :
    mulSecOfEq F σ h₁ ≫ mulSecOfEq F τ h₂ = mulSecOfEq F ρ h₃ :=
  zhom_ext fun V s i => by
    change zcoord ((mulSecOfEq F τ h₂).app V ((mulSecOfEq F σ h₁).app V s)) i = _
    rw [zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, hρ, map_mul, mul_comm,
      mul_smul]

@[reassoc] theorem mulSecOfEq_comp (σ : LB.Sec (lbZPow L m)) (τ : LB.Sec (lbZPow L m'))
    (h₁ : n + m = k) (h₂ : k + m' = l) (h₃ : n + (m + m') = l) :
    mulSecOfEq F σ h₁ ≫ mulSecOfEq F τ h₂ = mulSecOfEq F (zmul σ τ) h₃ :=
  mulSecOfEq_comp_of_zfun σ τ _ (zfun_zmul σ τ) h₁ h₂ h₃

@[reassoc] theorem mulSecOfEq_comm (σ : LB.Sec (lbZPow L m)) (τ : LB.Sec (lbZPow L m'))
    (h₁ : n + m = k) (h₂ : k + m' = l) (h₃ : n + m' = k') (h₄ : k' + m = l) :
    mulSecOfEq F σ h₁ ≫ mulSecOfEq F τ h₂ = mulSecOfEq F τ h₃ ≫ mulSecOfEq F σ h₄ :=
  (mulSecOfEq_comp σ τ h₁ h₂ (by omega)).trans
    (mulSecOfEq_comp_of_zfun τ σ _ (fun i => (zfun_zmul σ τ i).trans (mul_comm _ _)) h₃ h₄ _).symm

theorem mulSec_comp (σ : LB.Sec (lbZPow L m)) (τ : LB.Sec (lbZPow L m')) (n : ℤ)
    (h : n + (m + m') = n + m + m' := by omega) :
    mulSec F σ n ≫ mulSec F τ (n + m) =
      mulSec F (zmul σ τ) n ≫ eqToHom (congrArg (twistZ F L) h) :=
  (mulSecOfEq_comp σ τ rfl rfl h).trans (mulSec_eqToHom _ h).symm

theorem mulSec_comm (σ : LB.Sec (lbZPow L m)) (τ : LB.Sec (lbZPow L m')) (n : ℤ)
    (h : n + m' + m = n + m + m' := by omega) :
    mulSec F σ n ≫ mulSec F τ (n + m) = mulSec F τ n ≫ mulSec F σ (n + m') ≫
      eqToHom (congrArg (twistZ F L) h) := by
  rw [mulSec_eqToHom σ h]
  exact mulSecOfEq_comm σ τ rfl rfl rfl h

@[simp] theorem mulSecOfEq_zone (h : n + 0 = n) : mulSecOfEq F (zone L) h = 𝟙 _ :=
  zhom_ext fun V s i => by
    rw [zcoord_mulSecOfEq_app, zfun_zone, map_one, one_smul]
    rfl

@[simp] theorem mulSecOfEq_zero (h : n + m = k) :
    mulSecOfEq F (0 : LB.Sec (lbZPow L m)) h = 0 :=
  zhom_ext fun V s i => by
    rw [zcoord_mulSecOfEq_app, zfun_zero, map_zero, zero_smul]
    exact (zcoord_zero i).symm

theorem mulSecOfEq_add (σ τ : LB.Sec (lbZPow L m)) (h : n + m = k) :
    mulSecOfEq F (σ + τ) h = mulSecOfEq F σ h + mulSecOfEq F τ h :=
  zhom_ext fun V s i => by
    change _ = zcoord ((mulSecOfEq F σ h).app V s + (mulSecOfEq F τ h).app V s) i
    rw [zcoord_add, zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, zfun_add,
      map_add, add_smul]

theorem mulSecOfEq_smul_app (a : Γ(X, ⊤)) (σ : LB.Sec (lbZPow L m)) (h : n + m = k) {V : X.Opens}
    (s : Γ(twistZ F L n, V)) :
    (mulSecOfEq F (a • σ) h).app V s = resG X (le_top : V ≤ ⊤) a • (mulSecOfEq F σ h).app V s :=
  zsec_ext fun i => by
    rw [zcoord_smul, zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, zfun_smul, map_mul, mul_smul,
      resG_resG, resG_resG]

theorem bijective_mulSecOfEq_app (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) (h : n + m = k)
    {V : X.Opens} (hV : V ≤ Out.nonzeroLocus σ) :
    Function.Bijective ((mulSecOfEq F σ h).app V) :=
  bijective_app_of_cover _ hL.cover V fun i _ h' hi =>
    bijective_of_eq_smul (zchartEquiv hL n i hi).bijective (zchartEquiv hL k i hi).bijective
      (isUnit_resG_zfun σ i hi (h'.trans hV)) (zchartEquiv_mulSecOfEq_app hL σ h i hi)

variable (L) in

def zoneGen : LB.Gen (lbZPow L 0) := ⟨fun _ => 1⟩

theorem isGen_zoneGen : (zoneGen L).IsGen := fun i j => by
  have e := res_zpow_g i j le_rfl (inf_le_inf (zpow_U_le i) (zpow_U_le j))
  rw [zpow_zero] at e
  have e' : (lbZPow L 0).g i j = 1 := (Units.ext (resG_self _ _)).symm.trans e
  rw [e', one_mul]
  exact (map_one _).trans (map_one _).symm

variable (F) in

def twistZZeroIso (hL : L.IsLB) : F ≅ twistZ F L 0 :=
  genIso F (isLB_lbZPow hL 0) (zoneGen L) isGen_zoneGen

@[simp] theorem zcoord_twistZZeroIso_hom_app (hL : L.IsLB) {V : X.Opens} (t : Γ(F, V)) (i : L.ι) :
    zcoord ((twistZZeroIso F hL).hom.app V t) i = resM F inf_le_left t := by
  have e : coord ((twistZZeroIso F hL).hom.app V t) (zidx L 0 i) =
    resG X (inf_le_right : V ⊓ (lbZPow L 0).U (zidx L 0 i) ≤ _) 1 • resM F inf_le_left t := rfl
  rw [zcoord, e, map_one, one_smul, resM_resM]

variable (F) in

def twistZOneIso (hL : L.IsLB) : twist F L ≅ twistZ F L 1 :=
  refineIso F (fun j : (lbZPow L 1).ι => j PUnit.unit) zpow_U_le
    (fun i j => (Units.ext (resG_self _ _)).symm.trans
      ((res_zpow_g i j le_rfl _).trans (zpow_one _)))
    hL (isLB_lbZPow hL 1)

@[simp] theorem zcoord_twistZOneIso_hom_app (hL : L.IsLB) {V : X.Opens} (s : Γ(twist F L, V))
    (i : L.ι) : zcoord ((twistZOneIso F hL).hom.app V s) i = coord s i :=
  (resM_resM _ _ _).trans (resM_self _ _)

theorem twistZZeroIso_hom_mulSecOfEq (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) (h : 0 + m = m) :
    (twistZZeroIso F hL).hom ≫ mulSecOfEq F σ h = secHom F σ :=
  zhom_ext fun V t i => by
    change zcoord ((mulSecOfEq F σ h).app V ((twistZZeroIso F hL).hom.app V t)) i = _
    rw [zcoord_mulSecOfEq_app, zcoord_twistZZeroIso_hom_app, zcoord, coord_secHom_app, resM_smul,
      resM_resM, zfun, resG_resG, resG_resG]

theorem res_div_g (p q : (LB.div N L).ι) {W : X.Opens}
    (h : W ≤ (LB.div N L).U p ⊓ (LB.div N L).U q) (hN : W ≤ N.U p.1 ⊓ N.U q.1)
    (hL : W ≤ L.U p.2 ⊓ L.U q.2) :
    res h ((LB.div N L).g p q) = res hN (N.g p.1 q.1) * (res hL (L.g p.2 q.2))⁻¹ :=
  Semi.LB.res_dg N L p q h

variable (L n m k) in

def zaddGen : LB.Gen (LB.div (LB.div (lbZPow L k) (lbZPow L n)) (lbZPow L m)) where
  s p :=
    res (le_inf ((div_U_le_left p).trans ((div_U_le_left p.1).trans (zpow_U_le p.1.1)))
      ((div_U_le_left p).trans ((div_U_le_right p.1).trans (zpow_U_le p.1.2))))
      (L.g (p.1.1 PUnit.unit) (p.1.2 PUnit.unit)) ^ n *
    res (le_inf ((div_U_le_left p).trans ((div_U_le_left p.1).trans (zpow_U_le p.1.1)))
      ((div_U_le_right p).trans (zpow_U_le p.2)))
      (L.g (p.1.1 PUnit.unit) (p.2 PUnit.unit)) ^ m

theorem zpow_mul_inv_mul_identity_commGroup {A : Type*} [CommGroup A] (a b c d e : A) (n m : ℤ) :
    (a * b⁻¹ * d) ^ n * (a * c⁻¹ * e) ^ m =
      a ^ (n + m) * (b ^ n)⁻¹ * (c ^ m)⁻¹ * (d ^ n * e ^ m) := by
  simp only [mul_zpow, inv_zpow, zpow_add]
  ac_rfl

theorem res_zaddGen (p : (LB.div (LB.div (lbZPow L k) (lbZPow L n)) (lbZPow L m)).ι) {W : X.Opens}
    (h : W ≤ (LB.div (LB.div (lbZPow L k) (lbZPow L n)) (lbZPow L m)).U p)
    (h₁ : W ≤ L.U (p.1.1 PUnit.unit) ⊓ L.U (p.1.2 PUnit.unit))
    (h₂ : W ≤ L.U (p.1.1 PUnit.unit) ⊓ L.U (p.2 PUnit.unit)) :
    res h ((zaddGen L n m k).s p) = res h₁ (L.g (p.1.1 PUnit.unit) (p.1.2 PUnit.unit)) ^ n *
      res h₂ (L.g (p.1.1 PUnit.unit) (p.2 PUnit.unit)) ^ m := by
  change res h (_ * _) = _
  rw [map_mul, map_zpow, map_zpow, Semi.LB.res_res, Semi.LB.res_res]

theorem isGen_zaddGen (hL : L.IsLB) (h : n + m = k) : (zaddGen L n m k).IsGen := fun p q => by
  let D := LB.div (LB.div (lbZPow L k) (lbZPow L n)) (lbZPow L m)
  have hp : D.U p ⊓ D.U q ≤ D.U p := inf_le_left
  have hq : D.U p ⊓ D.U q ≤ D.U q := inf_le_right
  have pa := hp.trans ((div_U_le_left p).trans (div_U_le_left p.1))
  have pb := hp.trans ((div_U_le_left p).trans (div_U_le_right p.1))
  have pc := hp.trans (div_U_le_right p)
  have qa := hq.trans ((div_U_le_left q).trans (div_U_le_left q.1))
  have qb := hq.trans ((div_U_le_left q).trans (div_U_le_right q.1))
  have qc := hq.trans (div_U_le_right q)
  have pa' := pa.trans (zpow_U_le _)
  have pb' := pb.trans (zpow_U_le _)
  have pc' := pc.trans (zpow_U_le _)
  have qa' := qa.trans (zpow_U_le _)
  have qb' := qb.trans (zpow_U_le _)
  have qc' := qc.trans (zpow_U_le _)
  have e : D.g p q = _ := (Units.ext (resG_self _ _)).symm.trans (res_div_g p q le_rfl
    (le_inf (hp.trans (div_U_le_left p)) (hq.trans (div_U_le_left q))) (le_inf pc qc))
  rw [res_div_g p.1 q.1 _ (le_inf pa qa) (le_inf pb qb), res_zpow_g _ _ _ (le_inf pa' qa'),
    res_zpow_g _ _ _ (le_inf pb' qb'), res_zpow_g _ _ _ (le_inf pc' qc')] at e
  have c (a b a' b' : L.ι) (ha : D.U p ⊓ D.U q ≤ L.U a) (hb : D.U p ⊓ D.U q ≤ L.U b)
      (ha' : D.U p ⊓ D.U q ≤ L.U a') (hb' : D.U p ⊓ D.U q ≤ L.U b') :
      res (le_inf ha hb) (L.g a b) = res (le_inf ha ha') (L.g a a') *
        (res (le_inf hb hb') (L.g b b'))⁻¹ * res (le_inf ha' hb') (L.g a' b') := by
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq, Semi.LB.res_cocycle hL _ _ _ _ _ (le_inf ha hb'),
      Semi.LB.res_cocycle hL]
  change res hp _ = D.g p q * res hq _
  rw [e, res_zaddGen p hp (le_inf pa' pb') (le_inf pa' pc'),
    res_zaddGen q hq (le_inf qa' qb') (le_inf qa' qc'), c _ _ _ _ pa' pb' qa' qb',
    c _ _ _ _ pa' pc' qa' qc', ← h]
  exact zpow_mul_inv_mul_identity_commGroup _ _ _ _ _ _ _

variable (F) in

def twistZAddIso (hL : L.IsLB) (h : n + m = k) : twistZ (twistZ F L n) L m ≅ twistZ F L k :=
  twistTwistIso F (isLB_lbZPow hL n) (isLB_lbZPow hL m) (isLB_lbZPow hL k) _ (isGen_zaddGen hL h)

theorem zcoord_twistZAddIso_hom_app (hL : L.IsLB) (h : n + m = k) {V : X.Opens}
    (s : Γ(twistZ (twistZ F L n) L m, V)) (i : L.ι) :
    zcoord ((twistZAddIso F hL h).hom.app V s) i =
      resM F (le_inf le_rfl inf_le_right) (zcoord (zcoord s i) i) := by
  have l (r : ℤ) : V ⊓ L.U i ≤ (lbZPow L r).U (zidx L r i) := inf_le_right.trans (le_zidx_U r i)
  have hu : V ⊓ L.U i ≤ (lbZPow L k).U (zidx L k i) ⊓ (lbZPow L n).U (zidx L n i) ⊓
      (lbZPow L m).U (zidx L m i) := le_inf (le_inf (l k) (l n)) (l m)
  have e : res hu (tripleUnit (zaddGen L n m k) (zidx L k i) (zidx L n i) (zidx L m i)) = 1 := by
    have hii : V ⊓ L.U i ≤ L.U i ⊓ L.U i := le_inf inf_le_right inf_le_right
    have e₁ : _ = res hii (L.g i i) ^ n * res hii (L.g i i) ^ m :=
      res_zaddGen ((zidx L k i, zidx L n i), zidx L m i) hu hii hii
    rw [Semi.LB.res_g_self hL i, one_zpow, one_zpow, one_mul] at e₁
    exact e₁
  refine (coord_twistTwistIso_hom_app _ _ _ _ (isGen_zaddGen hL h) s (zidx L k i) (zidx L n i)
    (zidx L m i) _ (le_inf (le_inf inf_le_left (l m)) (l n)) hu).trans ?_
  rw [← val_res, e, Units.val_one, one_smul, zcoord, zcoord, coord_resM, resM_resM, resM_resM]

@[reassoc] theorem twistZAddIso_naturality (hL : L.IsLB) (h : n + m = k) (φ : F ⟶ G) :
    map (lbZPow L m) (map (lbZPow L n) φ) ≫ (twistZAddIso G hL h).hom =
      (twistZAddIso F hL h).hom ≫ map (lbZPow L k) φ :=
  twistTwistIso_naturality _ _ _ _ _ φ

theorem secHom_twistZAddIso_hom (hL : L.IsLB) (σ : LB.Sec (lbZPow L m)) (h : n + m = k) :
    secHom (twistZ F L n) σ ≫ (twistZAddIso F hL h).hom = mulSecOfEq F σ h :=
  zhom_ext fun V s i => by
    change zcoord ((twistZAddIso F hL h).hom.app V ((secHom (twistZ F L n) σ).app V s)) i = _
    have e : zcoord ((secHom (twistZ F L n) σ).app V s) i =
        resG X (inf_le_right : V ⊓ L.U i ≤ L.U i) (zfun σ i) • resM _ inf_le_left s := by
      rw [zcoord, coord_secHom_app, resM_smul, resM_resM, zfun, resG_resG, resG_resG]
    rw [zcoord_twistZAddIso_hom_app, e, zcoord_smul, zcoord_resM, resM_smul, resM_resM, resG_resG,
      resG_resG, resM_self, zcoord_mulSecOfEq_app]

end Pow

section PowInv

variable (F) in

def twistZNegOneIso (hL : L.IsLB) : twistZ F L (-1) ≅ twist F (LB.div (LB.triv X) L) :=
  refineIso F (fun p : (LB.div (LB.triv X) L).ι => zidx L (-1) p.2)
    (fun p => (div_U_le_right p).trans (le_zidx_U (-1) p.2))
    (fun p q => by
      have h := inf_le_inf (div_U_le_right p) (div_U_le_right q)
      have e : (LB.div (LB.triv X) L).g p q = _ :=
        (Units.ext (resG_self _ _)).symm.trans (res_div_g p q le_rfl (le_inf le_top le_top) h)
      rw [e, res_zpow_g _ _ _ h, zpow_neg_one]
      exact (congrArg (· * _) (map_one _)).trans (one_mul _))
    (isLB_lbZPow hL (-1)) (Semi.LB.isLB_div (LB.isLB_triv X) hL)

variable (F) in

def twistTwistZNegOneIso (hL : L.IsLB) : twistZ (twist F L) L (-1) ≅ F :=
  twistZNegOneIso (twist F L) hL ≪≫ ((twistInvNatIso hL).app F).symm

end PowInv

section PowPushPull

variable {n m k : ℤ} (f : Y ⟶ X)

variable (L) in

def pidx (i : L.ι) : (L.pull f).ι := fun _ => i

theorem pull_zpow_U_le (j : ((lbZPow L n).pull f).ι) :
    ((lbZPow L n).pull f).U j ≤
      (lbZPow (L.pull f) n).U (zidx _ n (pidx L f (j PUnit.unit PUnit.unit))) :=
  ((LB.pull_U_le f j).trans (f.preimage_mono (zpow_U_le _))).trans
    ((LB.pull_U f (pidx L f (j PUnit.unit PUnit.unit))).ge.trans (le_zidx_U n _))

theorem res_pull_g (i j : (L.pull f).ι) {W : Y.Opens} (h : W ≤ (L.pull f).U i ⊓ (L.pull f).U j)
    (h' : W ≤ f ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))) :
    res h ((L.pull f).g i j) = res h' (pullU f _ (L.g (i PUnit.unit) (j PUnit.unit))) :=
  Units.ext (LB.resG_pull_g f i j h)

theorem pull_zpow_g (i j : ((lbZPow L n).pull f).ι) :
    ((lbZPow L n).pull f).g i j = res (inf_le_inf (pull_zpow_U_le f i) (pull_zpow_U_le f j))
      ((lbZPow (L.pull f) n).g (zidx _ n (pidx L f (i PUnit.unit PUnit.unit)))
        (zidx _ n (pidx L f (j PUnit.unit PUnit.unit)))) := by
  have h₁ : ((lbZPow L n).pull f).U i ⊓ ((lbZPow L n).pull f).U j ≤
      f ⁻¹ᵁ ((lbZPow L n).U (i PUnit.unit) ⊓ (lbZPow L n).U (j PUnit.unit)) :=
    inf_le_inf (LB.pull_U_le f i) (LB.pull_U_le f j)
  have h₂ := inf_le_inf (zpow_U_le (i PUnit.unit)) (zpow_U_le (j PUnit.unit))
  have h₃ := (inf_le_inf (pull_zpow_U_le f i) (pull_zpow_U_le f j)).trans
    (inf_le_inf (zpow_U_le _) (zpow_U_le _))
  have e₁ : ((lbZPow L n).pull f).g i j = _ :=
    (Units.ext (resG_self _ _)).symm.trans (res_pull_g f i j le_rfl h₁)
  have e₂ : (lbZPow L n).g (i PUnit.unit) (j PUnit.unit) = _ :=
    (Units.ext (resG_self _ _)).symm.trans (res_zpow_g _ _ le_rfl h₂)
  rw [e₁, e₂, map_zpow, map_zpow, Semi.LB.pullU_res, Semi.LB.res_res, res_zpow_g _ _ _ h₃]
  exact congrArg (· ^ n) (res_pull_g f _ _ h₃ _).symm

def twistZPullIso (hL : L.IsLB) (G : Y.Modules) (n : ℤ) :
    twistZ G (L.pull f) n ≅ twist G ((lbZPow L n).pull f) :=
  refineIso G _ (pull_zpow_U_le f) (pull_zpow_g f) (isLB_lbZPow (Semi.LB.isLB_pull hL f) n)
    (Semi.LB.isLB_pull (isLB_lbZPow hL n) f)

def projZIso (hL : L.IsLB) (G : Y.Modules) (n : ℤ) :
    (Scheme.Modules.pushforward f).obj (twistZ G (L.pull f) n) ≅
      twistZ ((Scheme.Modules.pushforward f).obj G) L n :=
  (Scheme.Modules.pushforward f).mapIso (twistZPullIso f hL G n) ≪≫ projIso (lbZPow L n) f G

theorem le_pidx_inf (V : X.Opens) (i : L.ι) :
    f ⁻¹ᵁ (V ⊓ L.U i) ≤ f ⁻¹ᵁ V ⊓ (L.pull f).U (pidx L f i) := le_pull_inf f V i

theorem zcoord_projZIso_hom_app (hL : L.IsLB) (G : Y.Modules) {V : X.Opens}
    (s : Γ(twistZ G (L.pull f) n, f ⁻¹ᵁ V)) (i : L.ι) :
    (zcoord ((projZIso f hL G n).hom.app V s) i : Γ(G, f ⁻¹ᵁ (V ⊓ L.U i))) =
      resM G (le_pidx_inf f V i) (zcoord s (pidx L f i)) := by
  have h₁ : f ⁻¹ᵁ (V ⊓ L.U i) ≤ f ⁻¹ᵁ (V ⊓ (lbZPow L n).U (zidx L n i)) :=
    f.preimage_mono (inf_le_inf_left V (le_zidx_U n i))
  refine Eq.trans (b := resM G h₁ (resM G (le_pidx_inf f V (zidx L n i))
    (resM G (inf_le_inf_left _ (pull_zpow_U_le f (pidx _ f (zidx L n i))))
      (coord s (zidx _ n (pidx L f i)))))) rfl ?_
  exact ((resM_resM _ _ _).trans (resM_resM _ _ _)).trans (resM_resM _ _ _).symm

@[reassoc] theorem projZIso_naturality (hL : L.IsLB) {G G' : Y.Modules} (φ : G ⟶ G') (n : ℤ) :
    (Scheme.Modules.pushforward f).map (map (lbZPow (L.pull f) n) φ) ≫ (projZIso f hL G' n).hom =
      (projZIso f hL G n).hom ≫ map (lbZPow L n) ((Scheme.Modules.pushforward f).map φ) :=
  zhom_ext fun V (s : Γ(twistZ G (L.pull f) n, f ⁻¹ᵁ V)) i => by
    refine (zcoord_projZIso_hom_app f hL G' ((map (lbZPow (L.pull f) n) φ).app _ s) i).trans ?_
    refine Eq.trans ?_ (zcoord_map_app ((Scheme.Modules.pushforward f).map φ)
      ((projZIso f hL G n).hom.app V s) i).symm
    rw [zcoord_map_app, ← app_resM]
    exact congrArg (φ.app (f ⁻¹ᵁ (V ⊓ L.U i))) (zcoord_projZIso_hom_app f hL G s i).symm

def zpull (σ : LB.Sec (lbZPow L m)) : LB.Sec (lbZPow (L.pull f) m) :=
  zmkGlobal (fun j => (f.appLE _ _ (LB.pull_U_le f j)).hom (zfun σ (j PUnit.unit))) fun i j => by
    have h : (L.pull f).U i ⊓ (L.pull f).U j ≤ f ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.pull_U_le f i) (LB.pull_U_le f j)
    have e₀ : res le_rfl (L.g (i PUnit.unit) (j PUnit.unit)) = L.g (i PUnit.unit) (j PUnit.unit) :=
      Units.ext (resG_self _ _)
    have e := congrArg (f.appLE _ _ h).hom
      (zfun_rel σ (i PUnit.unit) (j PUnit.unit) inf_le_left inf_le_right le_rfl)
    have e₁ : (L.pull f).g i j = _ :=
      (Units.ext (resG_self _ _)).symm.trans (res_pull_g f i j le_rfl h)
    rw [map_mul, LB.appLE_resG, LB.appLE_resG, e₀] at e
    rw [LB.resG_appLE, LB.resG_appLE, e₁, ← map_zpow, ← map_zpow]
    exact e

@[simp] theorem zfun_zpull (σ : LB.Sec (lbZPow L m)) (j : (L.pull f).ι) :
    zfun (zpull f σ) j = (f.appLE _ _ (LB.pull_U_le f j)).hom (zfun σ (j PUnit.unit)) :=
  zfun_zmkGlobal _ _ j

@[reassoc] theorem projZIso_mulSecOfEq (hL : L.IsLB) (G : Y.Modules) (σ : LB.Sec (lbZPow L m))
    (h : n + m = k) :
    (Scheme.Modules.pushforward f).map (mulSecOfEq G (zpull f σ) h) ≫ (projZIso f hL G k).hom =
      (projZIso f hL G n).hom ≫ mulSecOfEq ((Scheme.Modules.pushforward f).obj G) σ h :=
  zhom_ext fun V (s : Γ(twistZ G (L.pull f) n, f ⁻¹ᵁ V)) i => by
    refine (zcoord_projZIso_hom_app f hL G ((mulSecOfEq G (zpull f σ) h).app _ s) i).trans ?_
    refine Eq.trans ?_ (zcoord_mulSecOfEq_app σ h ((projZIso f hL G n).hom.app V s) i).symm
    have e : (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) =
        (f.appLE (L.U i) _ (f.preimage_mono (inf_le_right : V ⊓ L.U i ≤ L.U i))).hom (zfun σ i) := by
      rw [← Scheme.Hom.appLE_eq_app, LB.appLE_resG]
    rw [zcoord_mulSecOfEq_app, resM_smul, resG_resG, zfun_zpull, LB.resG_appLE]
    refine Eq.trans (congrArg (· • resM G (le_pidx_inf f V i) (zcoord s (pidx L f i))) e.symm) ?_
    exact congrArg (fun t : Γ(G, f ⁻¹ᵁ (V ⊓ L.U i)) =>
      (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) • t)
      (zcoord_projZIso_hom_app f hL G s i).symm

variable (F) in

def pullbackZIso (hL : L.IsLB) (n : ℤ) : (Scheme.Modules.pullback f).obj (twistZ F L n) ≅
    twistZ ((Scheme.Modules.pullback f).obj F) (L.pull f) n :=
  pullbackIso F f (isLB_lbZPow hL n) ≪≫ (twistZPullIso f hL _ n).symm

end PowPushPull

example {U₀ U₁ : X.Opens} (u : Γ(X, U₀ ⊓ U₁)ˣ) (V : X.Opens)
    (s : Γ(twist F (LB.twoChart U₀ U₁ u), V)) :
    resM F (inf_le_left : V ⊓ U₀ ⊓ U₁ ≤ V ⊓ U₀) (coord s true) =
      resG X (inf_le_inf_right _ inf_le_right : V ⊓ U₀ ⊓ U₁ ≤ U₀ ⊓ U₁) (u : Γ(X, U₀ ⊓ U₁)) •
        resM F (inf_le_inf_right _ inf_le_left : V ⊓ U₀ ⊓ U₁ ≤ V ⊓ U₁) (coord s false) :=
  coord_mem s true false

example (t : Γ(F, ⊤)) :
    chartEquiv (LB.twoChart_isLB (sup_idem ⊤) (-1)) true (V := ⊤) le_rfl
      ((chartEquiv (LB.twoChart_isLB (sup_idem ⊤) (-1)) false (V := ⊤) le_rfl).symm t) = -t := by
  have e : resG X (le_inf le_rfl le_rfl : (⊤ : X.Opens) ≤ ⊤ ⊓ ⊤) (-1) = -1 :=
    (map_neg (resG X _) 1).trans (congrArg Neg.neg (map_one _))
  refine (chartEquiv_change (LB.twoChart_isLB (sup_idem ⊤) (-1)) true false (V := ⊤) le_rfl
    le_rfl _).trans ?_
  exact (congrArg₂ (fun (a : Γ(X, ⊤)) (s : Γ(F, ⊤)) => a • s) e
    (LinearEquiv.apply_symm_apply _ t)).trans (neg_one_smul _ t)

example (s : Γ(twistZ F (LB.twoChart (X := X) ⊤ ⊤ (-1)) 2, ⊤)) :
    zchartEquiv (LB.twoChart_isLB (sup_idem ⊤) (-1)) 2 true (V := ⊤) le_rfl s =
      zchartEquiv (LB.twoChart_isLB (sup_idem ⊤) (-1)) 2 false (V := ⊤) le_rfl s := by
  have e : res (le_inf le_rfl le_rfl : (⊤ : X.Opens) ≤ ⊤ ⊓ ⊤) (-1) = -1 :=
    Units.ext ((map_neg (resG X _) 1).trans (congrArg Neg.neg (map_one _)))
  have e' : res (le_inf le_rfl le_rfl : (⊤ : X.Opens) ≤ ⊤ ⊓ ⊤) (-1) ^ (2 : ℤ) = 1 := by
    rw [e, zpow_two, neg_mul_neg, one_mul]
  refine (zchartEquiv_change (LB.twoChart_isLB (sup_idem ⊤) (-1)) true false (V := ⊤) le_rfl
    le_rfl s).trans ?_
  exact (congrArg (fun a : Γ(X, ⊤)ˣ => (a : Γ(X, ⊤)) •
    zchartEquiv (LB.twoChart_isLB (sup_idem ⊤) (-1)) 2 false (V := ⊤) le_rfl s) e').trans
    (one_smul _ _)

example [Nontrivial Γ(F, ⊤)] : Nontrivial Γ(twist F (LB.triv X), ⊤) :=
  (ConcreteCategory.bijective_of_isIso ((trivIso F).hom.app ⊤)).1.nontrivial

example {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (u : Γ(X, U₀ ⊓ U₁)ˣ) :
    (twist (toMod (LB.twoChart U₀ U₁ u)) (LB.twoChart U₀ U₁ u)).IsQuasicoherent ∧
      (twist (toMod (LB.twoChart U₀ U₁ u)) (LB.twoChart U₀ U₁ u)).IsFiniteType :=
  ⟨(isQuasicoherent_twist_iff (LB.twoChart_isLB h u)).2
      (LB.isQuasicoherent_toMod (LB.twoChart_isLB h u)),
    (isFiniteType_twist_iff (LB.twoChart_isLB h u)).2
      (LB.isFiniteType_toMod (LB.twoChart_isLB h u))⟩

end Twist

end GlobalTheory
