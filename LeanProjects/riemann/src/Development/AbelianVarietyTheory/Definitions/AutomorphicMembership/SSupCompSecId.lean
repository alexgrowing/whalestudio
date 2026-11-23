import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChtTrueYEta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackPtC
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PairVEqZeroOfMemLieSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces

set_option maxHeartbeats 800000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM.AllPrimesCheck

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def flg0 (ct : At S κ p) : FlgSt ct := ⟨fun _ => Unit, fun _ _ => ct.YY, (), rfl⟩

def frm0 (ct : At S κ p) : FrmSt ct where
  nrmRef l f y := ct.nrm (ct.Lb l) f y
  LieV _ := PUnit
  lieL _ := ⊤
  eig _ _ := ⊤
  Wst _ _ _ := ⊤
  Wst_le _ _ _ := le_rfl
  taut _ _ _ := (⊤ : Submodule _ PUnit).toAddSubgroup ⊓ ⊤
  taut_eq _ _ _ := rfl
  nrmIn l f y _ := ct.nrm (ct.Lb l) f y
  nrmRef_def _ _ _ := rfl
  nrm_Lb_def _ _ _ := rfl

def fj0 (ct : At S κ p) : FJSt ct := ⟨Empty, fun _ => Empty, fun _ _ t => t.elim⟩

def jet0 (ct : At S κ p) (un : UniSt ct) (tg : ThgSt ct un) : JetSt ct un tg where
  Jet _ _ _ _ := PUnit
  intJet _ _ _ _ := ⊤
  jet _ _ _ _ := 0
  FB _ _ _ _ := PUnit
  nB _ := 0
  sgc _ _ _ _ := 0
  trB _ _ _ _ _ := LinearEquiv.refl _ _
  trB_norm _ _ _ _ _ _ := rfl
  jX _ _ _ _ _ := 0
  intJet_free _ _ _ _ := ⟨0, Module.Basis.empty _, fun _ => ⟨fun _ i => i.elim0, fun _ => trivial⟩⟩
  jX_int _ _ _ _ _ _ _ := trivial
  jet_fourier _ _ _ _ _ _ _ := ⟨∅, fun _ _ => ⟨0, trivial, Subsingleton.elim _ _⟩⟩

def evl0 (ct : At S κ p) : EvlSt ct where
  LieGt _ _ := PUnit
  LieB _ _ := PUnit
  LieT _ _ := PUnit
  resB _ _ := 0
  incT _ _ := 0
  kapGt _ _ _ _ := 0
  kapB _ _ _ _ := 0
  Harm _ := Empty
  SecP _ := Empty
  evA _ h := h.elim
  evGt _ h := h.elim

section Ratio

open AlgebraicGeometry CategoryTheory GlobalTheory.VB GlobalTheory.PtNorm
open GlobalTheory.QCoh (IsFiniteQC structureModule)
open GlobalTheory.Twist (resM)

variable (ct : At S κ p) {Z : ct.Mdl} {F₁ F₂ : ct.Sh Z}

def hSh (F₁ F₂ : ct.Sh Z) : ct.Sh Z := Z.ofMod (homMod F₁.toMod F₂.toMod)

def hSec (φ : ct.GIso F₁ F₂) : ct.Sec (hSh ct F₁ F₂) :=
  (ct.ofModIso (isVB_homMod φ.isInv_left φ.isInv_right)).inv.app _ (compSec (𝟙 _) φ.iso.hom)

theorem nrm_hSec (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.nrm (hSh ct F₁ F₂) (hSec ct φ) y = sSup (nrmSet y.z (homMod F₁.toMod F₂.toMod) (compSec (𝟙 _) φ.iso.hom)) :=
  congrArg sSup (nrmSet_iso y.z (ct.ofModIso (isVB_homMod φ.isInv_left φ.isInv_right)).symm _)

theorem nrm_hSec_pos (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) : 0 < ct.nrm (hSh ct F₁ F₂) (hSec ct φ) y ∧
    ct.nrm (hSh ct F₂ F₁) (hSec ct φ.symm) y = (ct.nrm (hSh ct F₁ F₂) (hSec ct φ) y)⁻¹ := by
  have := IsVB.isFiniteQC φ.isInv_left
  have := IsVB.isFiniteQC φ.isInv_right
  rw [nrm_hSec, nrm_hSec]
  exact sSup_compSec_mul y.z ct.hp.ne_zero φ.isInv_left φ.isInv_right _ _ (IsVB.restrict φ.isInv_right _) φ.iso

def vr (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) : ℝ := -Real.logb p (ct.nrm (hSh ct F₁ F₂) (hSec ct φ) y)

theorem nrm_eq_vr (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.nrm (hSh ct F₁ F₂) (hSec ct φ) y = (p : ℝ) ^ (-(vr ct φ y)) := by
  rw [vr, neg_neg, Real.rpow_logb (Nat.cast_pos.2 ct.hp.pos) (by exact_mod_cast ct.hp.one_lt.ne')
    (nrm_hSec_pos ct φ y).1]

theorem sSup_compSec_id {X : Scheme.{0}} {F G : X.Modules} {C : Formalism.MainNotions.DIV.Cons.SCF p}
    (z : Sp (Formalism.MainNotions.DIV.Cons.intO C.S) ⟶ X) (hp : p ≠ 0) (hF : IsVB F 1) [IsFiniteQC G] {u : Γ(F, ⊤)}
    (hu : GlobalTheory.VB.IsFrame fun _ : Fin 1 => u)
    (φ : F.restrict (GlobalTheory.PtNorm.gen X p).ι ≅ G.restrict (GlobalTheory.PtNorm.gen X p).ι) :
    sSup (nrmSet z G (homApp (homOfRestrict φ.hom) le_rfl (resM F le_top u))) =
      sSup (nrmSet z (homMod F G) (compSec (𝟙 _) φ.hom)) :=
  sSup_compSec_eq z hp hF _ hu φ

def oS : ct.Sh ct.Xm := ct.Xm.ofMod (structureModule ct.Xm.X)

def oU : Γ((oS ct).toMod, ⊤) := (ct.ofModIso (isVB_structureModule ct.Xm.X)).inv.app ⊤ (oneSec ⊤)

def shf0 : ShfSt ct where
  vrat := vr ct
  SES _ := Unit
  ExactMod _ _ := True
  homSh := hSh ct
  homSh_inv _ _ h₁ h₂ := (isVB_homMod h₁ h₂).of_iso (ct.ofModIso (isVB_homMod h₁ h₂)).symm
  isoSec := hSec ct
  nrm_isoSec := nrm_eq_vr ct
  isoSymm := At.GIso.symm
  vrat_symm φ y := by rw [vr, vr, (nrm_hSec_pos ct φ y).2, Real.logb_inv]
  oX := oS ct
  oX_inv := (isVB_structureModule _).of_iso (ct.ofModIso (isVB_structureModule ct.Xm.X)).symm
  secOf φ := homApp (homOfRestrict φ.iso.hom) le_rfl (resM _ le_top (oU ct))
  nrm_secOf φ y := by
    have := IsVB.isFiniteQC φ.isInv_right
    rw [← nrm_eq_vr, nrm_hSec]
    exact sSup_compSec_id y.z ct.hp.ne_zero φ.isInv_left
      ((isFrame_one ⊤).map_iso (ct.ofModIso (isVB_structureModule ct.Xm.X)).inv) φ.iso

end Ratio

def htm0 (ct : At S κ p) (hq : HTpSt ct) : HTmSt ct (shf0 ct) hq where
  IsHTBlowup _ _ := False
  eOmP _ _ _ := ⟨0, 0, 0, 0, 0⟩
  htSES _ _ := ()
  BT _ := Unit
  extA _ := False
  compat _ _ := False
  HTn _ := Empty
  htEval h := h.elim
  htIdl h := h.elim
  IsHTBlowup_def _ _ _ := ⟨False.elim, fun ⟨h, _⟩ => h.elim⟩
  wFib h := h.elim
  omSh _ := ⟨0, 0, 0, 0, 0⟩
  omPat _ := ⊥
  omPat_def _ _ _ h := h.elim
  BPt _ := Empty
  bfld y := y.elim
  OmB _ := PUnit
  obMod y := y.elim
  omB y := y.elim
  omPB y := y.elim
  eOmB y := y.elim
  eB y := y.elim

def crd0 (ct : At S κ p) : CrDSt ct where
  nefQ _ := True
  Crv := Empty
  eDeg c := c.elim
  Pm c := c.elim
  Pm_nonneg c := c.elim
  degLie c := c.elim
  degLdR c := c.elim
  CrvQ := Empty
  degGrQ c := c.elim
  nefQ_def _ := ⟨fun _ c => c.elim, fun _ => trivial⟩
  degGrD c := c.elim
  degLdR_def c := c.elim
  degLie_f c := c.elim
  degLie_alt c := c.elim
  eDeg_def _ c := c.elim
  Pm_head c := c.elim
  Pm_tail c := c.elim

def crh0 (ct : At S κ p) : CrHSt ct (flg0 ct) where
  nefHT _ _ := True
  descK _ _ := False
  bdryLoci _ := True
  htFlags _ := ()
  YsP _ := Empty
  ysBd x := x.elim
  FlP := Empty
  hFl x := x.elim
  FlCl := Empty
  flMem x := x.elim
  flDim x := x.elim
  Sum1 := Empty
  locus x := x.elim
  bdryLoci_def _ := ⟨fun _ => ⟨∅, Set.finite_empty, fun x => x.elim, fun x => x.elim⟩, fun _ => trivial⟩
  CrvS _ := Empty
  degGr c := c.elim
  nefHT_def _ _ := ⟨fun _ c => c.elim, fun _ => trivial⟩

def stages0 (ct : At S κ p) : Stages ct where
  lw := SharedLaws.lawSt D A N j S κ p ct
  mo := motTrue ct
  sh := shf0 ct
  fg := flg0 ct
  fr := frm0 ct
  ch := chtTrue ct
  tr := torTrue ct
  fj := fj0 ct
  un := uniTrue ct
  tb := thbTrue ct
  ky := keyTrue ct
  bd := bdyTrue ct
  tg := thgTrue ct
  jt := jet0 ct _ _
  ev := evl0 ct
  hq := htpTrue ct
  hm := htm0 ct _
  cd := crd0 ct
  cr := crh0 ct

def stFam0 (S : Sig A N j) (κ : Lv A) : StFam S κ := ⟨stages0, alpOf D, fun _ => rfl⟩

theorem exists_ats (h : ∀ (p : ℕ), p.Prime → ∀ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits → ∃ ct : At S κ p, ct.W = W)
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (hj : ∀ (p : ℕ) [Fact p.Prime] v, JcPin D p v (jC p v)) :
    ∃ cts : Ats S κ, cts.Over jC := by
  have k : ∀ (p : ℕ) [Fact p.Prime] (v : PlL D p), ∃ ct : At S κ p, ct.W = placeW D p v (jC p v) := fun p hp v =>
    h p hp.out _ (GlobalTheory.ShFam.Pad.placeW_over D p v _ (hj p v)).1
  exact ⟨fun p _ v => (k p v).choose, fun p _ v => (k p v).choose_spec⟩

theorem over_induces {cts : Ats S κ} {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} (h : cts.Over jC)
    (p : ℕ) [Fact p.Prime] (v : PlL D p) (hj : JcPin D p v (jC p v)) (x : D.what₂.LL) :
    ((κ.e x : κ.c.F) : ℂ) ∈ (cts p v).W ↔ v.1.valuation D.what₂.LL x ≤ 1 := by
  rw [h p v, κ.e_emb]
  exact (GlobalTheory.ShFam.Pad.placeW_over D p v _ hj).2 x

theorem isBCAt_bcAt (ct : At S κ p) (Z : CodeAt S κ) : IsBCAt ct Z (bcAt ct Z) := by
  have h := BCEx.exists_isBCAt D A N j S κ p ct Z
  rw [bcAt, dif_pos h]
  exact h.choose_spec

theorem bcAt_eq_blowUp (ct : At S κ p) (Z : CodeAt S κ) (J : ct.Idl ct.Xm)
    (hJ : ∀ Z', IsBCAt ct Z Z' ↔ IsNBlow ct.Xm J Z') : bcAt ct Z = ct.blowUp ct.Xm J := by
  have h := BCEx.exists_isBCAt D A N j S κ p ct Z
  rw [bcAt, dif_pos h]
  exact choose_eq_blowUp ct Z _ J h hJ

variable (F : StFam S κ) (cts : Ats S κ)

theorem bc_eq_blowUp (hp : p.Prime) (Z : CodeAt S κ)
    (h : ∀ v, ∃ d, ∀ Z', IsBCAt (@cts p ⟨hp⟩ v) Z Z' ↔ IsNBlow _ ((F.st (@cts p ⟨hp⟩ v)).tr.jIdl none d) Z') :
    ∃ d : ((locStOf F cts).ex p).IvD none, (globStOf F cts).bc p Z =
      ((locStOf F cts).ex p).blowUp ((locStOf F cts).loc p).Xm (((locStOf F cts).ex p).jIdl none d) := by
  haveI := Fact.mk hp
  change ∃ d : (locAt F cts p).ex.IvD none, (locAt F cts p).bc Z =
      (locAt F cts p).ex.blowUp (locAt F cts p).loc.Xm ((locAt F cts p).ex.jIdl none d)
  rw [locAt_prime]
  choose d hd using h
  exact ⟨d, funext fun v => bcAt_eq_blowUp _ Z _ (hd v)⟩

theorem theta_clauses (hp : p.Prime) :
    (∀ Z (y : ((locStOf F cts).loc p).Pt Z) (a : ((locStOf F cts).loc p).Ylat y),
      ((locStOf F cts).loc p).psiV y a = ((locStOf F cts).loc p).be y a a / 2) ∧
    ((locStOf F cts).loc p).IsInv ((locStOf F cts).loc p).piPP ∧
    ∀ c, ((locStOf F cts).loc p).IsInv (((locStOf F cts).loc p).keySh c) := by
  haveI := Fact.mk hp
  rw [locStOf_loc]
  exact ⟨fun Z y a => motTrue_psiV_half (cts p y.1) y.2 a, fun v => (cts p v).isInv_piPP,
    fun c v => (cts p v).isInv_keySh c⟩

theorem nrm_pbKF_iff (hp : p.Prime) {c : ℕ} (kf : ngTrue.KF (D.R.f * N) c) :
    (∀ y, ((locStOf F cts).loc p).nrm (((locStOf F cts).loc p).keySh c) ((locStOf F cts).pbKF p kf) y = 1) ↔
      ∀ v y, (@cts p ⟨hp⟩ v).nrm ((@cts p ⟨hp⟩ v).keySh c) ((@cts p ⟨hp⟩ v).pbKF kf) y = 1 := by
  haveI := Fact.mk hp
  change (∀ y, (locAt F cts p).loc.nrm ((locAt F cts p).loc.keySh c) ((locAt F cts p).pbKF kf) y = 1) ↔ _
  rw [locAt_prime]
  exact Sigma.forall

theorem alp_eq (hp : p.Prime) : ((locStOf F cts).locB p hp).alp = F.α p := by
  haveI := Fact.mk hp
  change ((locAt F cts p).locB hp).alp = _
  rw [locAt_prime]
  rfl

theorem xn_injective (hp : p.Prime) : Function.Injective ((locStOf F cts).loc p).Xn := by
  haveI := Fact.mk hp
  rw [locStOf_loc]
  intro n m h
  obtain ⟨v⟩ := plL_ne D p
  have h1 := ((cts p v).B.lvl (some n)).2.2.1
  have h2 := ((cts p v).B.lvl (some m)).2.2.1
  have h3 : ((cts p v).B.X (some n)).i.l.A = ((cts p v).B.X (some m)).i.l.A :=
    congrArg (fun Z : (cts p v).Mdl => Z.i.l.A) (congrFun h v)
  rw [h1, h2] at h3
  exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_left κ.l.A_pos h3)

end GlobalTheory.LocM.AllPrimesCheck
