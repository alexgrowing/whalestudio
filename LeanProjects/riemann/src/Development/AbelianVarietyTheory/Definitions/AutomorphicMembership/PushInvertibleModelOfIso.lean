import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaSqMulSqrtEtaSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.FlagMod (GChart thUnit thRat detChg pushPP detOm detLie de ev)
open GlobalTheory.Reg (MChart)
open GlobalTheory.LB (toMod)

namespace GlobalTheory.LocM

section OneModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Transport

variable (Y : Model Xo c β) {X : Scheme.{0}} (π : X ⟶ Y.X) [IsIso π]

def genInv : pullback Y.s (spMap β) ⟶ pullback (π ≫ Y.s) (spMap β) :=
  pullback.map _ _ _ _ (inv π) (𝟙 _) (𝟙 _) (by simp) (by simp)

instance isIso_genInv : IsIso (genInv Y π) := by unfold genInv; infer_instance

theorem genInv_fst : genInv Y π ≫ pullback.fst _ _ ≫ π = pullback.fst _ _ := by
  rw [genInv, pullback.lift_fst_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem genInv_snd : genInv Y π ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [genInv, pullback.lift_snd, Category.comp_id]

theorem exists_sabMap_genInv {t : SAB H X} (m : SABMap t Y.t π) :
    ∃ n : SABMap Y.oF.t t ((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _), n.φ ≫ m.φ = Y.m.φ := by
  have e : ((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _) ≫ π = Y.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, genInv_fst]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap Y.oF.t Y.t (((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _) ≫ π), n'.φ = Y.m.φ := by
    rw [e]; exact ⟨Y.m, rfl⟩
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n'
  exact ⟨n, hn.symm.trans hn'⟩

@[reducible] def modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π) :
    Model Xo c β where
  X := X
  s := π ≫ Y.s
  normal := hn
  proj := by
    obtain ⟨n, i, hi, e⟩ := Y.proj
    exact ⟨n, π ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  flat := have := Y.flat; inferInstance
  jQ := Y.jQ ≫ genInv Y π
  jQ_over := by rw [Category.assoc, genInv_snd, Y.jQ_over]
  jQ_open := have := Y.jQ_open; inferInstance
  jQ_dense := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (genInv Y π).surjective.denseRange.comp Y.jQ_dense (genInv Y π).continuous
  t := t
  oF := Y.oF
  m0 := Y.m0
  m := (exists_sabMap_genInv Y π m).choose
  ab_gen := by
    ext y
    obtain ⟨y, rfl⟩ := (genInv Y π).surjective y
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne Y.t.semi m.cart.1, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, genInv_fst, ← Set.mem_preimage, Y.ab_gen]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (genInv Y π).homeomorph.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hx)⟩

theorem modelOfIso_j (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π) :
    (modelOfIso Y π hn t m).j ≫ π = Y.j := by
  simp only [Model.j, Category.assoc, genInv_fst]

theorem pushInvertible_modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π)
    (hD : GlobalTheory.Models.IsDedFrac β) (hY : PushInvertible Y.t.G Y.t.PP.L) : PushInvertible t.G t.PP.L := by
  obtain ⟨l₁, l₂, l₃, -, -⟩ := GlobalTheory.firstFiveLaws
  let C := modelOfIso Y π hn t m
  exact GlobalTheory.PushInv.pushInvertible_of_model l₁ l₂ l₃ E H Dw l _ _ _ _ _ _ Y.oF _ β
    ⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, C.m, C.ab_gen⟩ hD
    ((GlobalTheory.AbLocusPull.abLocus_sections_pull _ _ π Y.t.G t.G m.φ Y.t.semi m.cart).2 _ _ Y.t.PP.isLB t.PP.isLB
      (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) fun x => by
        obtain ⟨V, hV, θ, hθ, -, nz⟩ := hY x
        exact ⟨V, hV, θ, hθ, nz⟩)

end Transport

variable {Y : Model Xo c β}

def pushMod {X : Scheme.{0}} (t : SAB H X) : X.Modules := (Scheme.Modules.pushforward t.G.hom).obj (toMod t.PP.L)

def thetaSec (M : GChart Y) : Γ(pushMod Y.t, M.U) := GlobalTheory.LB.mkSec M.θ M.θ_mem

theorem isFrame_thetaSec (M : GChart Y) : GlobalTheory.LB.IsFrame (thetaSec M) := fun V h => by
  rw [Function.bijective_iff_existsUnique]
  intro s
  refine (existsUnique_congr fun a => ?_).1 (M.gen V h _ (GlobalTheory.LB.coord_mem (L := Y.t.PP.L) s))
  exact ⟨fun e => GlobalTheory.LB.sec_ext (L := Y.t.PP.L) fun i => (e i).symm,
    fun e i => (congrArg (fun s => GlobalTheory.LB.coord (L := Y.t.PP.L) s i) e).symm⟩

theorem thetaSec_change (M M' : GChart Y) :
    (pushMod Y.t).presheaf.map (homOfLE (inf_le_right : M.U ⊓ M'.U ≤ M'.U)).op (thetaSec M') =
      thRat M M' • (pushMod Y.t).presheaf.map (homOfLE (inf_le_left : M.U ⊓ M'.U ≤ M.U)).op (thetaSec M) :=
  GlobalTheory.LB.sec_ext (L := Y.t.PP.L) fun i => (M.gen _ inf_le_left _
    (GlobalTheory.ModelChart.res_mem_secOn _ (Y.t.G.hom.preimage_mono inf_le_right) M'.θ_mem)).exists.choose_spec i

theorem ofFrames_thetaSec : GlobalTheory.LB.ofFrames (fun M : GChart Y => isFrame_thetaSec M) = pushPP Y := by
  unfold pushPP GlobalTheory.LB.ofFrames
  congr 1
  funext M M'
  refine Units.ext ?_
  have e := GlobalTheory.LB.resG_ofFrames_g (fun M : GChart Y => isFrame_thetaSec M) M M' le_rfl
  rw [GlobalTheory.LB.resG_self] at e
  exact e.trans ((isFrame_thetaSec M).repr_eq _ (thetaSec_change M M').symm)

theorem nonempty_pushMod_iso (h : (pushPP Y).IsLB) : Nonempty (pushMod Y.t ≅ toMod (pushPP Y)) :=
  ofFrames_thetaSec (Y := Y) ▸ ⟨GlobalTheory.LB.ofFramesIso (fun M : GChart Y => isFrame_thetaSec M) h.cover⟩

theorem isVB_pushMod (h : (pushPP Y).IsLB) : GlobalTheory.VB.IsVB (pushMod Y.t) 1 :=
  (GlobalTheory.VB.isVB_toMod h).of_iso (nonempty_pushMod_iso h).some.symm

def keyUnit (k : ℕ) (M M' : GChart Y) : Γ(Y.X, M.U ⊓ M'.U)ˣ :=
  (thUnit M M')⁻¹ ^ (2 * k) * detChg M.toMChart M'.toMChart ^ k

theorem thRat_pow_mul_keyUnit (k : ℕ) (M M' : GChart Y) :
    thRat M M' ^ (2 * k) * (keyUnit k M M').val = (detChg M.toMChart M'.toMChart).val ^ k := by
  have : thUnit M M' ^ (2 * k) * keyUnit k M M' = detChg M.toMChart M'.toMChart ^ k := by
    simp only [keyUnit, inv_pow, mul_inv_cancel_left]
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, GlobalTheory.FlagMod.thUnit_val] using congrArg Units.val this

def keyLB (Y : Model Xo c β) (k : ℕ) : LB Y.X := ⟨GChart Y, fun M => M.U, keyUnit k⟩

def keyHomLB (Y : Model Xo c β) (k : ℕ) : LB Y.X :=
  LB.div (lbPow (GlobalTheory.CechPic.dual (detOm Y)) k) (lbPow (pushPP Y) (2 * k))

def keyPowLB (Y : Model Xo c β) (k : ℕ) : LB Y.X :=
  lbPow (GlobalTheory.CechPic.tens (lbPow (de Y) 2) (GlobalTheory.CechPic.dual (detOm Y))) k

theorem gm_keyUnit (k : ℕ) (M M' : GChart Y) (y : Y.X) :
    gm (𝟙 Y.X) y _ (keyUnit k M M') =
      (gm (𝟙 Y.X) y _ (thUnit M M'))⁻¹ ^ (2 * k) * gm (𝟙 Y.X) y _ (detChg M.toMChart M'.toMChart) ^ k := by
  rw [keyUnit, map_mul, map_pow, map_pow, map_inv]

section Cover

variable [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L)
include hP

theorem isLB_keyLB (k : ℕ) : (keyLB Y k).IsLB := by
  refine GlobalTheory.LBLimit.isLB_of_germs _ (GlobalTheory.FlagMod.exists_gChart hP) fun a b d y ha hb hd => ?_
  have e₁ : gm (𝟙 Y.X) y _ (thUnit a b) * gm (𝟙 Y.X) y _ (thUnit b d) = gm (𝟙 Y.X) y _ (thUnit a d) :=
    gm_cocycle (GlobalTheory.FlagMod.isLB_pushPP hP) (𝟙 Y.X) y ha hb hd
  have e₂ : gm (𝟙 Y.X) y _ (detChg a.toMChart b.toMChart) * gm (𝟙 Y.X) y _ (detChg b.toMChart d.toMChart) =
      gm (𝟙 Y.X) y _ (detChg a.toMChart d.toMChart) :=
    gm_cocycle (GlobalTheory.FlagMod.isLB_detLie hP) (𝟙 Y.X) y (i := a.toMChart) (j := b.toMChart) (k := d.toMChart) ha hb hd
  refine (congrArg₂ (· * ·) (gm_keyUnit k a b y) (gm_keyUnit k b d y)).trans (Eq.trans ?_ (gm_keyUnit k a d y).symm)
  rw [← e₁, ← e₂, mul_inv, mul_pow, mul_pow, _root_.mul_mul_mul_comm]

end Cover

def KeyAt (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn R) : Prop :=
  ∃ (φ : x.P.A.left ⟶ Y.t.G.left) (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G)
    (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

end OneModel

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

@[reducible] def base : Model (S.Xo ct.Xm.i.l) ct.Xm.i.c (ct.Xm.i.c.V ct.W).subtype :=
  haveI := ct.B.iso none
  modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap

theorem range_base_j : Set.range ct.base.j = ct.Xm.opn := by
  haveI := ct.B.iso none
  have e : ct.base.j ≫ ct.Xm.π = (ct.Y ct.Xm.i).j := modelOfIso_j _ _ _ _ _
  ext x
  rw [Pre.opn, ← e]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, ct.Xm.π.homeomorph.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hy)⟩

instance isNoetherianRing_base : IsNoetherianRing (ct.Xm.i.c.V ct.W) :=
  GlobalTheory.ModelPresentation.isNoetherianRing_place _ _ ct.hp.ne_zero ct.hW

theorem pushInvertible : PushInvertible ct.Xm.t.G ct.Xm.t.PP.L :=
  haveI := ct.B.iso none
  pushInvertible_modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap
    ((GlobalTheory.CoeffRings.coeff_isDedFrac _ A.H _ ct.Xm.i.c).2.2.2 p ct.W ct.hp ct.hW).1
    ((S.sys.clauses p ct.W ct.hp ct.hW).1.1 ct.Xm.i).2.2.1

abbrev KeyChart : Type := GChart ct.base

def keyL (c : ℕ) : LB ct.Xm.X := keyLB ct.base c

theorem isLB_keyL (c : ℕ) : (ct.keyL c).IsLB := isLB_keyLB (Y := ct.base) ct.pushInvertible c

def ofModIso {Z : ct.Mdl} {F : Z.X.Modules} (h : GlobalTheory.VB.IsVB F 1) : (Z.ofMod F).toMod ≅ F :=
  haveI := h.isFiniteQC
  (GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ Z F).some

def piPP : ct.Sh ct.Xm := ct.Xm.ofMod (pushMod ct.Xm.t)

def keySh (c : ℕ) : ct.Sh ct.Xm := ct.Xm.ofMod (toMod (ct.keyL c))

theorem isVB_pushMod : GlobalTheory.VB.IsVB (pushMod ct.Xm.t) 1 :=
  GlobalTheory.LocM.isVB_pushMod (Y := ct.base) (GlobalTheory.FlagMod.isLB_pushPP ct.pushInvertible)

def piIso : ct.piPP.toMod ≅ pushMod ct.Xm.t := ct.ofModIso ct.isVB_pushMod

def keyIso (c : ℕ) : (ct.keySh c).toMod ≅ toMod (ct.keyL c) := ct.ofModIso (GlobalTheory.VB.isVB_toMod (ct.isLB_keyL c))

theorem isInv_piPP : ct.IsInv ct.piPP := ct.isVB_pushMod.of_iso ct.piIso.symm

theorem isInv_keySh (c : ℕ) : ct.IsInv (ct.keySh c) :=
  (GlobalTheory.VB.isVB_toMod (ct.isLB_keyL c)).of_iso (ct.keyIso c).symm

variable {ct}

def piGen (M : ct.KeyChart) : Γ(ct.piPP.toMod, M.U) := ct.piIso.inv.app M.U (thetaSec M)

def keyGen (c : ℕ) (M : ct.KeyChart) : Γ((ct.keySh c).toMod, M.U) :=
  (ct.keyIso c).inv.app M.U (GlobalTheory.LB.chartSec (ct.isLB_keyL c) M)

theorem isFrame_keyGen (c : ℕ) (M : ct.KeyChart) : GlobalTheory.LB.IsFrame (keyGen c M) :=
  (GlobalTheory.LB.isFrame_chartSec (ct.isLB_keyL c) M).app (ct.keyIso c).symm

def keyCoef {c : ℕ} {V : ct.Xm.X.Opens} (s : Γ((ct.keySh c).toMod, V)) (M : ct.KeyChart) : Γ(ct.Xm.X, V ⊓ M.U) :=
  GlobalTheory.LB.coord ((ct.keyIso c).hom.app V s) M

def keyMk (c : ℕ) {V : ct.Xm.X.Opens} (f : ∀ M : ct.KeyChart, Γ(ct.Xm.X, V ⊓ M.U)) (hf : f ∈ secOn (ct.keyL c) V) :
    Γ((ct.keySh c).toMod, V) :=
  (GlobalTheory.LB.appLinearEquiv (ct.keyIso c) V).symm (GlobalTheory.LB.mkSec f hf)

theorem keyCoef_keyMk (c : ℕ) {V : ct.Xm.X.Opens} (f : ∀ M : ct.KeyChart, Γ(ct.Xm.X, V ⊓ M.U))
    (hf : f ∈ secOn (ct.keyL c) V) : keyCoef (keyMk c f hf) = f :=
  congrArg GlobalTheory.LB.coord ((GlobalTheory.LB.appLinearEquiv (ct.keyIso c) V).apply_symm_apply _)

def HasKeyValues {c : ℕ} (val : GlobalTheory.KeyCl.Rule) (s : ct.Sec (ct.keySh c)) : Prop :=
  ∀ (M : ct.KeyChart) (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ ct.Xm.X) (hz : ⊤ ≤ z ⁻¹ᵁ (ct.Xm.genO ⊓ M.U))
    (x : KeyIn K), KeyAt M z (GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz) x → ev z _ hz (keyCoef s M) = val K x

variable (ct)

open Classical in

def pbKF {g c : ℕ} (kf : KF g c) : ct.Sec (ct.keySh c) :=
  if h : ∃ s : ct.Sec (ct.keySh c), HasKeyValues kf.coef s then h.choose else 0

end At

def keyTrue (ct : At S κ p) : KeySt ct where
  piPP := ct.piPP
  keySh := ct.keySh
  keySh_inv _ := ct.isInv_keySh

example (ct : At S κ p) : ∃ s : Γ((ct.keySh 0).toMod, ⊤), ∀ M, At.keyCoef s M = 1 := by
  refine ⟨At.keyMk 0 (fun _ => 1) fun M M' => ?_, fun M => congrFun (At.keyCoef_keyMk _ _ _) M⟩
  change resG _ _ 1 = resG _ _ (keyUnit 0 M M').val * resG _ _ 1
  simp [keyUnit]

example (ct : At S κ p) (M M' : ct.KeyChart) :
    thRat M M' ^ 2 * (keyUnit 1 M M').val = GlobalTheory.FlagMod.rdet (GlobalTheory.FlagMod.chg M.toMChart M'.toMChart) := by
  simpa only [Nat.mul_one, pow_one, GlobalTheory.FlagMod.detChg_val] using thRat_pow_mul_keyUnit 1 M M'

example (ct : At S κ p) (c : ℕ) (M : ct.KeyChart) : At.keyGen c M ≠ 0 := fun h => by
  have := M.dom
  refine one_ne_zero ((At.isFrame_keyGen c M M.U le_rfl).1 ?_)
  simp only [h, map_zero, smul_zero]

end GlobalTheory.LocM
