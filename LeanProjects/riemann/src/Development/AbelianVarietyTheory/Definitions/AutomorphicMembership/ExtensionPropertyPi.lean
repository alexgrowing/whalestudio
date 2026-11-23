import Mathlib
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData

noncomputable section

namespace GlobalTheory.LocM

open Formalism.BasicNotions Formalism.MainNotions NumberField

inductive SigmaRel {ι : Type} {α β : ι → Type} (R : ∀ i, α i → β i → Prop) : (Σ i, α i) → (Σ i, β i) → Prop
  | mk {i : ι} {a : α i} {b : β i} : R i a b → SigmaRel R ⟨i, a⟩ ⟨i, b⟩

theorem sigmaRel_mk {ι : Type} {α β : ι → Type} {R : ∀ i, α i → β i → Prop} {i : ι} {a : α i} {b : β i} :
    SigmaRel R ⟨i, a⟩ ⟨i, b⟩ ↔ R i a b :=
  ⟨fun h => by cases h; assumption, SigmaRel.mk⟩

theorem SigmaRel.fst_eq {ι : Type} {α β : ι → Type} {R : ∀ i, α i → β i → Prop} {a : Σ i, α i} {b : Σ i, β i}
    (h : SigmaRel R a b) : a.1 = b.1 := by
  cases h; rfl

variable {D : D7} {r j p : ℕ} {ι : Type}

def Loc.pi (L : ι → ModuliIntegralCharts.Loc D r j p) : ModuliIntegralCharts.Loc D r j p where
  Mdl := ∀ v, (L v).Mdl
  Xm v := (L v).Xm
  YY v := (L v).YY
  Xn n v := (L v).Xn n
  Pt Z := Σ v, (L v).Pt (Z v)
  fld y := (L y.1).fld y.2
  Ylat y := (L y.1).Ylat y.2
  ylAdd y := (L y.1).ylAdd y.2
  ylMod y := (L y.1).ylMod y.2
  ylFree y := (L y.1).ylFree y.2
  ylFin y := (L y.1).ylFin y.2
  be y := (L y.1).be y.2
  be_symm y := (L y.1).be_symm y.2
  be_bal y := (L y.1).be_bal y.2
  be_posDef y := (L y.1).be_posDef y.2
  yl_rank y := (L y.1).yl_rank y.2
  Gen Z := Σ v, (L v).Gen (Z v)
  abAt η := (L η.1).abAt η.2
  Sh Z := ∀ v, (L v).Sh (Z v)
  IsInv F := ∀ v, (L v).IsInv (F v)
  IsLocFree F := ∀ v, (L v).IsLocFree (F v)
  Sec F := ∀ v, (L v).Sec (F v)
  secAdd _ := Pi.addCommGroup
  H0 F := AddSubgroup.pi Set.univ fun v => (L v).H0 (F v)
  nrm F f y := (L y.1).nrm (F y.1) (f y.1) y.2
  nrm_nonneg F f y := (L y.1).nrm_nonneg (F y.1) (f y.1) y.2
  norm_le_one_of_mem_sections F f hf y := (L y.1).norm_le_one_of_mem_sections (F y.1) (f y.1) (hf y.1 (Set.mem_univ _)) y.2
  GIso F₁ F₂ := ∀ v, (L v).GIso (F₁ v) (F₂ v)
  vrat φ y := (L y.1).vrat (φ y.1) y.2
  Lb l v := (L v).Lb l
  Lb_inv l v := (L v).Lb_inv l
  nrmRef l f y := (L y.1).nrmRef l (f y.1) y.2
  DVP := Σ v, (L v).DVP
  dvRho y := (L y.1).dvRho y.2
  Ext y := (L y.1).Ext y.2
  Chart Z y e := (L y.1).Chart (Z y.1) y.2 e
  chAt {_ y _} χ := (L y.1).chAt χ
  chOpen {_ y _} χ := (L y.1).chOpen χ
  chAbExact {_ y _} χ := (L y.1).chAbExact χ
  chModU {_ y _} χ := (L y.1).chModU χ
  chConst {_ y _} χ := (L y.1).chConst χ
  PL := ∀ v, (L v).PL
  phiAt φ _ y := (L y.1).phiAt (φ y.1) y.2
  phiAt_zero φ _ y := (L y.1).phiAt_zero (φ y.1) y.2
  divGe F f i φ := ∀ v, (L v).divGe (F v) (f v) i (φ v)
  FJd := Σ v, (L v).FJd
  Chr t := (L t.1).Chr t.2
  fjN l f t := (L t.1).fjN l (f t.1) t.2
  Unim := ∀ v, (L v).Unim
  LBG La := ∀ v, (L v).LBG (La v)
  LBGq La := ∀ v, (L v).LBGq (La v)
  resQ P v := (L v).resQ (P v)
  PPq La v := (L v).PPq (La v)
  symmG P := ∀ v, (L v).symmG (P v)
  rigG P := ∀ v, (L v).rigG (P v)
  LBGt y La := (L y.1).LBGt y.2 (La y.1)
  LBB y La := (L y.1).LBB y.2 (La y.1)
  resGt P y := (L y.1).resGt (P y.1) y.2
  prPull {y _} M := (L y.1).prPull M
  principal {y _} M := (L y.1).principal M
  psiV y := (L y.1).psiV y.2
  piPP v := (L v).piPP
  keySh c v := (L v).keySh c
  latStd n v := (L v).latStd n
  At y La := (L y.1).At y.2 (La y.1)
  atAdd y La := (L y.1).atAdd y.2 (La y.1)
  atFin y La := (L y.1).atFin y.2 (La y.1)
  at_tors y La := (L y.1).at_tors y.2 (La y.1)
  at_card y := (L y.1).at_card y.2
  Th y La := (L y.1).Th y.2 (La y.1)
  thGrp y La := (L y.1).thGrp y.2 (La y.1)
  ovr y La := (L y.1).ovr y.2 (La y.1)
  ovr_surj y La := (L y.1).ovr_surj y.2 (La y.1)
  scal y La := (L y.1).scal y.2 (La y.1)
  scal_inj y La := (L y.1).scal_inj y.2 (La y.1)
  scal_central y La := (L y.1).scal_central y.2 (La y.1)
  ker_ovr y La := (L y.1).ker_ovr y.2 (La y.1)
  dl y La := (L y.1).dl y.2 (La y.1)
  dl_ovr y La := (L y.1).dl_ovr y.2 (La y.1)
  dl_scal y La := (L y.1).dl_scal y.2 (La y.1)
  dl_dl y La := (L y.1).dl_dl y.2 (La y.1)
  Sn y La := (L y.1).Sn y.2 (La y.1)
  snAdd y La := (L y.1).snAdd y.2 (La y.1)
  snMod y La := (L y.1).snMod y.2 (La y.1)
  act y La := (L y.1).act y.2 (La y.1)
  act_scal y La := (L y.1).act_scal y.2 (La y.1)
  vth y La := (L y.1).vth y.2 (La y.1)
  Jet y La := (L y.1).Jet y.2 (La y.1)
  jAdd y La := (L y.1).jAdd y.2 (La y.1)
  jMod y La := (L y.1).jMod y.2 (La y.1)
  intJet y La := (L y.1).intJet y.2 (La y.1)
  jet y La := (L y.1).jet y.2 (La y.1)
  LieGt y := (L y.1).LieGt y.2
  LieB y := (L y.1).LieB y.2
  LieT y := (L y.1).LieT y.2
  lgAdd y := (L y.1).lgAdd y.2
  lbAdd y := (L y.1).lbAdd y.2
  ltAdd y := (L y.1).ltAdd y.2
  resB y := (L y.1).resB y.2
  incT y := (L y.1).incT y.2
  kapGt y := (L y.1).kapGt y.2
  kapB y := (L y.1).kapB y.2
  Harm y := (L y.1).Harm y.2
  SecP y := (L y.1).SecP y.2
  evA y := (L y.1).evA y.2
  evGt y := (L y.1).evGt y.2
  Tp y := (L y.1).Tp y.2
  tpAdd y := (L y.1).tpAdd y.2
  OmV y := (L y.1).OmV y.2
  omAdd y := (L y.1).omAdd y.2
  omMod y := (L y.1).omMod y.2
  om y := (L y.1).om y.2
  ht y := (L y.1).ht y.2
  IsHTBlowup Z' Z := ∀ v, (L v).IsHTBlowup (Z' v) (Z v)
  eOmP Z s τ v := (L v).eOmP (Z v) s τ
  SES Z := ∀ v, (L v).SES (Z v)
  ExactMod s k := ∀ v, (L v).ExactMod (s v) k
  htSES Z τ v := (L v).htSES (Z v) τ
  nefHT Z l := ∀ v, (L v).nefHT (Z v) l
  nefQ l := ∀ v, (L v).nefQ l
  descK Z l := ∀ v, (L v).descK (Z v) l
  bdryLoci Z := ∀ v, (L v).bdryLoci (Z v)
  BT n := ∀ v, (L v).BT n
  extA b := ∀ v, (L v).extA (b v)
  compat b b' := ∀ v, (L v).compat (b v) (b' v)
  Crv := Σ v, (L v).Crv
  eDeg c := (L c.1).eDeg c.2
  Pm c := (L c.1).Pm c.2
  Pm_nonneg c := (L c.1).Pm_nonneg c.2
  degLie c := (L c.1).degLie c.2
  degLdR c := (L c.1).degLdR c.2

theorem Loc.bs_pi (L : ι → ModuliIntegralCharts.Loc D r j p) (b : Option ℕ) :
    ModuliIntegralCharts.bs (Loc.pi L) b = fun v => ModuliIntegralCharts.bs (L v) b := by
  cases b <;> rfl

def ExtA.pi [Finite ι] [Nonempty ι] {L : ι → ModuliIntegralCharts.Loc D r j p} (G : ∀ v, ModuliIntegralCharts.ExtA D (L v)) :
    ModuliIntegralCharts.ExtA D (Loc.pi L) where
  FlagData Z := ∀ v, (G v).FlagData (Z v)
  flagCl Z s v := (G v).flagCl (Z v) (s v)
  allFlags v := (G v).allFlags
  YY_eq := funext fun v => (G v).YY_eq
  Idl Z := ∀ v, (G v).Idl (Z v)
  blowUp Z I v := (G v).blowUp (Z v) (I v)
  powP I := ∀ v, (G v).powP (I v)
  pbPrinc {_ y _} I χ := (G y.1).pbPrinc (I y.1) χ
  Corr Z₁ Z₂ := ∀ v, (G v).Corr (Z₁ v) (Z₂ v)
  corr_sub Z₁ Z₂ := ⟨fun a b => funext fun v => ((G v).corr_sub (Z₁ v) (Z₂ v)).elim (a v) (b v)⟩
  diagCl Z₁ Z₂ c v := (G v).diagCl (Z₁ v) (Z₂ v) (c v)
  IvD b := ∀ v, (G v).IvD b
  jIdl b d := match b, d with
    | none, d => fun v => (G v).jIdl none (d v)
    | some n, d => fun v => (G v).jIdl (some n) (d v)
  ZP Z := Σ v, (G v).ZP (Z v)
  spz {Z} := SigmaRel fun v (x x' : (G v).ZP (Z v)) => (G v).spz x x'
  abP x := (G x.1).abP x.2
  inQ x := (G x.1).inQ x.2
  isGenP x := (G x.1).isGenP x.2
  isGenP_ab x := (G x.1).isGenP_ab x.2
  gpt η := ⟨η.1, (G η.1).gpt η.2⟩
  abAt_iff η := (G η.1).abAt_iff η.2
  gpt_notQ η := (G η.1).gpt_notQ η.2
  genFin Z := by
    haveI := fun v => (G v).genFin (Z v)
    exact inferInstanceAs (Finite (Σ v, (L v).Gen (Z v)))
  genNe Z := by
    obtain ⟨v⟩ := ‹Nonempty ι›
    obtain ⟨η⟩ := (G v).genNe (Z v)
    exact ⟨⟨v, η⟩⟩
  redK Z y := ⟨y.1, (G y.1).redK (Z y.1) y.2⟩
  dvRho_pos_iff Z y := (G y.1).dvRho_pos_iff (Z y.1) y.2
  genK η := ⟨η.1, (G η.1).genK η.2⟩
  redK_genK η := congrArg (Sigma.mk η.1) ((G η.1).redK_genK η.2)
  imgM {_ y _} χ := ⟨y.1, (G y.1).imgM χ⟩
  imgU {_ y _} χ := ⟨y.1, (G y.1).imgU χ⟩
  img_spz {_ y _} χ := SigmaRel.mk ((G y.1).img_spz χ)
  imgU_inQ {_ y _} χ := (G y.1).imgU_inQ χ
  chAt_imgM {_ y _} χ h := congrArg (Sigma.mk y.1) ((G y.1).chAt_imgM χ h)
  chAbExact_imgU {_ y _} χ := (G y.1).chAbExact_imgU χ
  RFam y := (G y.1).RFam y.2
  chFam {_ y _} χ := (G y.1).chFam χ
  ptK Z y := ⟨y.1, (G y.1).ptK (Z y.1) y.2⟩
  ptK_good Z y := (G y.1).ptK_good (Z y.1) y.2
  vpi {y} e := (G y.1).vpi e
  vpi_pos {y} e := (G y.1).vpi_pos e
  ordGe {_ y _} χ F f := (G y.1).ordGe χ (F y.1) (f y.1)
  yEta η := ⟨η.1, (G η.1).yEta η.2⟩
  yEta_good η := (G η.1).yEta_good η.2
  homSh F₁ F₂ v := (G v).homSh (F₁ v) (F₂ v)
  homSh_inv F₁ F₂ h₁ h₂ v := (G v).homSh_inv (F₁ v) (F₂ v) (h₁ v) (h₂ v)
  isoSec φ v := (G v).isoSec (φ v)
  nrm_isoSec φ y := (G y.1).nrm_isoSec (φ y.1) y.2
  isoSymm φ v := (G v).isoSymm (φ v)
  vrat_symm φ y := (G y.1).vrat_symm (φ y.1) y.2
  LieV y := (G y.1).LieV y.2
  lvAdd y := (G y.1).lvAdd y.2
  lvMod y := (G y.1).lvMod y.2
  lieL y := (G y.1).lieL y.2
  eig y := (G y.1).eig y.2
  Wst y := (G y.1).Wst y.2
  Wst_le y := (G y.1).Wst_le y.2
  taut y := (G y.1).taut y.2
  taut_eq y := (G y.1).taut_eq y.2
  nrmIn l f y := (G y.1).nrmIn l (f y.1) y.2
  nrmRef_def l f y := (G y.1).nrmRef_def l (f y.1) y.2
  nrm_Lb_def l f y := (G y.1).nrm_Lb_def l (f y.1) y.2
  om_smul y := (G y.1).om_smul y.2
  TC y := (G y.1).TC y.2
  tcAdd y := (G y.1).tcAdd y.2
  tcMod y := (G y.1).tcMod y.2
  iT y := (G y.1).iT y.2
  iT_span y := (G y.1).iT_span y.2
  htC y := (G y.1).htC y.2
  htC_iT y := (G y.1).htC_iT y.2
  psiC y := (G y.1).psiC y.2
  lieGt1 y := (G y.1).lieGt1 y.2
  eT y := (G y.1).eT y.2
  HTn n := ∀ v, (G v).HTn n
  htEval h y := (G y.1).htEval (h y.1) y.2
  htIdl h v := (G v).htIdl (h v)
  IsHTBlowup_def n Z' hn := by
    constructor
    · intro H
      choose h h₁ h₂ using fun v => ((G v).IsHTBlowup_def n (Z' v) hn).1 (H v)
      exact ⟨h, fun y => h₁ y.1 y.2, funext h₂⟩
    · rintro ⟨h, h₁, h₂⟩ v
      exact ((G v).IsHTBlowup_def n (Z' v) hn).2 ⟨h v, fun y => h₁ ⟨v, y⟩, congrFun h₂ v⟩
  wFib h y := (G y.1).wFib (h y.1) y.2
  htFlags Z v := (G v).htFlags (Z v)
  omSh Z v := (G v).omSh (Z v)
  omPat y := (G y.1).omPat y.2
  omPat_def n Z' hn H y := (G y.1).omPat_def n (Z' y.1) hn (H y.1) y.2
  BPt Z := Σ v, (G v).BPt (Z v)
  bfld y := (G y.1).bfld y.2
  OmB y := (G y.1).OmB y.2
  obAdd y := (G y.1).obAdd y.2
  obMod y := (G y.1).obMod y.2
  omB y := (G y.1).omB y.2
  omPB y := (G y.1).omPB y.2
  eOmB y := (G y.1).eOmB y.2
  eB y := (G y.1).eB y.2
  YsP Z := Σ v, (G v).YsP (Z v)
  ysBd x := (G x.1).ysBd x.2
  FlP := Σ v, (G v).FlP
  hFl x := ⟨x.1, (G x.1).hFl x.2⟩
  FlCl := Σ v, (G v).FlCl
  flMem := SigmaRel fun v => (G v).flMem
  flDim c := (G c.1).flDim c.2
  Sum1 := Σ v, (G v).Sum1
  locus ℓ := ⟨ℓ.1, (G ℓ.1).locus ℓ.2⟩
  bdryLoci_def Z := by
    constructor
    · intro H
      choose S h₁ h₂ h₃ using fun v => ((G v).bdryLoci_def (Z v)).1 (H v)
      refine ⟨⋃ v, Sigma.mk v '' S v, Set.finite_iUnion fun v => (h₁ v).image _, ?_, ?_⟩
      · rintro ⟨v, x⟩ hx
        obtain ⟨ℓ, hℓ, hm⟩ := h₂ v x hx
        exact ⟨⟨v, ℓ⟩, Set.mem_iUnion.2 ⟨v, ℓ, hℓ, rfl⟩, SigmaRel.mk hm⟩
      · intro ℓ hℓ
        obtain ⟨v, ℓ', hℓ', rfl⟩ := Set.mem_iUnion.1 hℓ
        exact h₃ v ℓ' hℓ'
    · rintro ⟨S, h₁, h₂, h₃⟩ v
      refine ((G v).bdryLoci_def (Z v)).2 ⟨{ℓ | (⟨v, ℓ⟩ : Σ v, (G v).Sum1) ∈ S},
        h₁.preimage (f := Sigma.mk (β := fun v => (G v).Sum1) v) sigma_mk_injective.injOn, fun x hx => ?_, fun ℓ hℓ => h₃ ⟨v, ℓ⟩ hℓ⟩
      obtain ⟨⟨w, ℓ⟩, hℓ, hm⟩ := h₂ ⟨v, x⟩ hx
      obtain rfl : v = w := hm.fst_eq
      exact ⟨ℓ, hℓ, sigmaRel_mk.1 hm⟩
  CrvS Z := Σ v, (G v).CrvS (Z v)
  degGr C := (G C.1).degGr C.2
  nefHT_def Z l :=
    ⟨fun H C => ((G C.1).nefHT_def (Z C.1) l).1 (H C.1) C.2,
      fun H v => ((G v).nefHT_def (Z v) l).2 fun C => H ⟨v, C⟩⟩
  CrvQ := Σ v, (G v).CrvQ
  degGrQ C := (G C.1).degGrQ C.2
  nefQ_def l :=
    ⟨fun H C => ((G C.1).nefQ_def l).1 (H C.1) C.2, fun H v => ((G v).nefQ_def l).2 fun C => H ⟨v, C⟩⟩
  degGrD c := (G c.1).degGrD c.2
  degLdR_def c := (G c.1).degLdR_def c.2
  degLie_f c := (G c.1).degLie_f c.2
  degLie_alt c := (G c.1).degLie_alt c.2
  eDeg_def h c := (G c.1).eDeg_def h c.2
  Pm_head c := (G c.1).Pm_head c.2
  Pm_tail c := (G c.1).Pm_tail c.2

def LocB.pi [Nonempty ι] {L : ι → ModuliIntegralCharts.Loc D r j p} (B : ∀ v, BoundaryLocalData.LocB D (L v)) (α : ℕ → 𝓞 D.host.E)
    (hα : ∀ v, (B v).alp = α) : BoundaryLocalData.LocB D (Loc.pi L) where
  chX y := (B y.1).chX y.2
  xAdd y := (B y.1).xAdd y.2
  xMod y := (B y.1).xMod y.2
  phi y := (B y.1).phi y.2
  phi_conj y := (B y.1).phi_conj y.2
  tau y := (B y.1).tau y.2
  tau_add_left y := (B y.1).tau_add_left y.2
  tau_add_right y := (B y.1).tau_add_right y.2
  tau_symm y := (B y.1).tau_symm y.2
  tau_smul y := (B y.1).tau_smul y.2
  be_tau y := (B y.1).be_tau y.2
  multiplicationLatticeFirst y := (B y.1).multiplicationLatticeFirst y.2
  multiplicationLatticeSecond y := (B y.1).multiplicationLatticeSecond y.2
  mulC y := (B y.1).mulC y.2
  psiV_def y := (B y.1).psiV_def y.2
  StrictHenselianAcyclic La := ∀ v, (B v).StrictHenselianAcyclic (La v)
  squareRootLineBundle La := ∀ v, (B v).squareRootLineBundle (La v)
  res2 P v := (B v).res2 (P v)
  PoiQ La v := (B v).PoiQ (La v)
  biext P := ∀ v, (B v).biext (P v)
  dg P v := (B v).dg (P v)
  dgq P v := (B v).dgq (P v)
  dg_res P := funext fun v => (B v).dg_res (P v)
  PPq_def La := funext fun v => (B v).PPq_def (La v)
  BPt := Σ v, (B v).BPt
  Rl z := (B z.1).Rl z.2
  iRr z := (B z.1).iRr z.2
  iRd z := (B z.1).iRd z.2
  iRl z := (B z.1).iRl z.2
  iRn z := (B z.1).iRn z.2
  iRi z := (B z.1).iRi z.2
  iRc z := (B z.1).iRc z.2
  Yb z := (B z.1).Yb z.2
  iYa z := (B z.1).iYa z.2
  iYm z := (B z.1).iYm z.2
  Xb z := (B z.1).Xb z.2
  iXa z := (B z.1).iXa z.2
  iXm z := (B z.1).iXm z.2
  phib z := (B z.1).phib z.2
  phib_conj z := (B z.1).phib_conj z.2
  taub z := (B z.1).taub z.2
  taub_add_left z := (B z.1).taub_add_left z.2
  taub_add_right z := (B z.1).taub_add_right z.2
  taub_symm z := (B z.1).taub_symm z.2
  taub_smul z := (B z.1).taub_smul z.2
  taub_pos z := (B z.1).taub_pos z.2
  Sg z := (B z.1).Sg z.2
  iSg z := (B z.1).iSg z.2
  iSk z := (B z.1).iSk z.2
  iSm z := (B z.1).iSm z.2
  iSt z := (B z.1).iSt z.2
  Sreg z := (B z.1).Sreg z.2
  fc z := (B z.1).fc z.2
  trU z := (B z.1).trU z.2
  oX v := (B v).oX
  oX_inv v := (B v).oX_inv
  secOf φ v := (B v).secOf (φ v)
  nrm_secOf φ y := (B y.1).nrm_secOf (φ y.1) y.2
  keySh_inv h c v := (B v).keySh_inv (h v) c
  dimB y := (B y.1).dimB y.2
  dimB_add y := (B y.1).dimB_add y.2
  FB y := (B y.1).FB y.2
  fbAdd y := (B y.1).fbAdd y.2
  fbMod y := (B y.1).fbMod y.2
  nB {y _ _ _} σ := (B y.1).nB σ
  sgc y := (B y.1).sgc y.2
  trB y := (B y.1).trB y.2
  trB_norm y := (B y.1).trB_norm y.2
  alp := α
  alp_spec n hn := by
    obtain ⟨v⟩ := ‹Nonempty ι›
    rw [← hα v]
    exact (B v).alp_spec n hn
  th1 y := (B y.1).th1 y.2
  pbAl y := (B y.1).pbAl y.2
  vth_def y := (B y.1).vth_def y.2
  jX y := (B y.1).jX y.2
  intJet_free y := (B y.1).intJet_free y.2
  jX_int y := (B y.1).jX_int y.2
  jet_fourier y := (B y.1).jet_fourier y.2

section Values

variable (L : ι → ModuliIntegralCharts.Loc D r j p)

@[simp] theorem Loc.pi_Xm (v : ι) :
    (Loc.pi L).Xm v = (L v).Xm := rfl

@[simp] theorem Loc.pi_YY (v : ι) :
    (Loc.pi L).YY v = (L v).YY := rfl

@[simp] theorem Loc.pi_Xn (n : ℕ) (v : ι) :
    (Loc.pi L).Xn n v = (L v).Xn n := rfl

@[simp] theorem Loc.pi_fld {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).fld (Z := Z) ⟨v, y⟩ = (L v).fld y := rfl

@[simp] theorem Loc.pi_be {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).be (Z := Z) ⟨v, y⟩ = (L v).be y := rfl

@[simp] theorem Loc.pi_good {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).good (Z := Z) ⟨v, y⟩ ↔ (L v).good y := Iff.rfl

@[simp] theorem Loc.pi_phiCy {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).phiCy (Z := Z) ⟨v, y⟩ = (L v).phiCy y := rfl

@[simp] theorem Loc.pi_dP {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).dP (Z := Z) ⟨v, y⟩ = (L v).dP y := rfl

@[simp] theorem Loc.pi_cJ {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) (n DF : ℕ) :
    (Loc.pi L).cJ (Z := Z) ⟨v, y⟩ n DF = (L v).cJ y n DF := rfl

@[simp] theorem Loc.pi_isCp {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    ModuliIntegralCharts.isCp (Loc.pi L) (Z := Z) ⟨v, y⟩ ↔ ModuliIntegralCharts.isCp (L v) y := Iff.rfl

@[simp] theorem Loc.pi_psiV {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).psiV (Z := Z) ⟨v, y⟩ = (L v).psiV y := rfl

@[simp] theorem Loc.pi_ht {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).ht (Z := Z) ⟨v, y⟩ = (L v).ht y := rfl

@[simp] theorem Loc.pi_om {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).om (Z := Z) ⟨v, y⟩ = (L v).om y := rfl

@[simp] theorem Loc.pi_abAt {Z : (Loc.pi L).Mdl} (v : ι) (η : (L v).Gen (Z v)) :
    (Loc.pi L).abAt (Z := Z) ⟨v, η⟩ ↔ (L v).abAt η := Iff.rfl

@[simp] theorem Loc.pi_isInv {Z : (Loc.pi L).Mdl} (F : (Loc.pi L).Sh Z) :
    (Loc.pi L).IsInv F ↔ ∀ v, (L v).IsInv (F v) := Iff.rfl

@[simp] theorem Loc.pi_isLocFree {Z : (Loc.pi L).Mdl} (F : (Loc.pi L).Sh Z) :
    (Loc.pi L).IsLocFree F ↔ ∀ v, (L v).IsLocFree (F v) := Iff.rfl

@[simp] theorem Loc.pi_nrm {Z : (Loc.pi L).Mdl} (F : (Loc.pi L).Sh Z) (f : (Loc.pi L).Sec F) (v : ι)
    (y : (L v).Pt (Z v)) :
    (Loc.pi L).nrm F f ⟨v, y⟩ = (L v).nrm (F v) (f v) y := rfl

@[simp] theorem Loc.pi_vrat {Z : (Loc.pi L).Mdl} {F₁ F₂ : (Loc.pi L).Sh Z} (φ : (Loc.pi L).GIso F₁ F₂) (v : ι)
    (y : (L v).Pt (Z v)) :
    (Loc.pi L).vrat φ ⟨v, y⟩ = (L v).vrat (φ v) y := rfl

@[simp] theorem Loc.pi_Lb (l : ModuliIntegralCharts.PsiT D → ℕ → ℤ) (v : ι) :
    (Loc.pi L).Lb l v = (L v).Lb l := rfl

@[simp] theorem Loc.pi_nrmRef (l : ModuliIntegralCharts.PsiT D → ℕ → ℤ) (f : (Loc.pi L).Sec ((Loc.pi L).Lb l)) (v : ι)
    (y : (L v).Pt (L v).YY) :
    (Loc.pi L).nrmRef l f ⟨v, y⟩ = (L v).nrmRef l (f v) y := rfl

@[simp] theorem Loc.pi_dvRho (v : ι) (y : (L v).DVP) :
    (Loc.pi L).dvRho ⟨v, y⟩ = (L v).dvRho y := rfl

@[simp] theorem Loc.pi_isChart {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).DVP) (e : (L v).Ext y)
    (χ : (L v).Chart (Z v) y e) :
    ModuliIntegralCharts.IsChart (Loc.pi L) (Z := Z) (y := ⟨v, y⟩) (e := e) χ ↔ ModuliIntegralCharts.IsChart (L v) χ := Iff.rfl

@[simp] theorem Loc.pi_phiAt (φ : (Loc.pi L).PL) {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (Loc.pi L).phiAt φ (Z := Z) ⟨v, y⟩ = (L v).phiAt (φ v) y := rfl

@[simp] theorem Loc.pi_fjN (l : ModuliIntegralCharts.PsiT D → ℕ → ℤ) (f : (Loc.pi L).Sec ((Loc.pi L).Lb l)) (v : ι)
    (t : (L v).FJd) (χ : (L v).Chr t) :
    (Loc.pi L).fjN l f ⟨v, t⟩ χ = (L v).fjN l (f v) t χ := rfl

@[simp] theorem Loc.pi_piPP (v : ι) :
    (Loc.pi L).piPP v = (L v).piPP := rfl

@[simp] theorem Loc.pi_keySh (c : ℕ) (v : ι) :
    (Loc.pi L).keySh c v = (L v).keySh c := rfl

@[simp] theorem Loc.pi_latStd (n : ℕ) (v : ι) :
    (Loc.pi L).latStd n v = (L v).latStd n := rfl

@[simp] theorem Loc.pi_symLift (v : ι) (y : (L v).Pt (L v).Xm) (La : (Loc.pi L).Unim) (n : ℕ)
    (sg : (L v).At y (La v) n → (L v).Th y (La v) n) :
    (Loc.pi L).SymLift ⟨v, y⟩ La n sg ↔ (L v).SymLift y (La v) n sg := Iff.rfl

@[simp] theorem Loc.pi_secJet (v : ι) (y : (L v).Pt (L v).Xm) (La : (Loc.pi L).Unim) (n DF : ℕ)
    (sg : (L v).At y (La v) n → (L v).Th y (La v) n) :
    (Loc.pi L).secJet ⟨v, y⟩ La n DF sg = (L v).secJet y (La v) n DF sg := rfl

@[simp] theorem Loc.pi_intJet (v : ι) (y : (L v).Pt (L v).Xm) (La : (Loc.pi L).Unim) (n DF : ℕ) :
    (Loc.pi L).intJet ⟨v, y⟩ La n DF = (L v).intJet y (La v) n DF := rfl

@[simp] theorem Loc.pi_isHTBlowup (Z' Z : (Loc.pi L).Mdl) :
    (Loc.pi L).IsHTBlowup Z' Z ↔ ∀ v, (L v).IsHTBlowup (Z' v) (Z v) := Iff.rfl

@[simp] theorem Loc.pi_degLdR (v : ι) (c : (L v).Crv) :
    (Loc.pi L).degLdR ⟨v, c⟩ = (L v).degLdR c := rfl

@[simp] theorem Loc.mem_sections_pi_iff {Z : (Loc.pi L).Mdl} (F : (Loc.pi L).Sh Z) (f : (Loc.pi L).Sec F) :
    f ∈ (Loc.pi L).H0 F ↔ ∀ v, f v ∈ (L v).H0 (F v) :=
  ⟨fun h v => h v (Set.mem_univ _), fun h v _ => h v⟩

theorem Loc.exists_pi_mdl (v : ι) (Z : (L v).Mdl) : ∃ Z' : (Loc.pi L).Mdl, Z' v = Z := by
  classical
  exact ⟨Function.update (β := fun w => (L w).Mdl) (fun w => (L w).Xm) v Z, Function.update_self ..⟩

theorem Loc.exists_pi_unim (v : ι) (La : (L v).Unim) : ∃ La' : (Loc.pi L).Unim, La' v = La := by
  classical
  exact ⟨Function.update (β := fun w => (L w).Unim) (fun w => (L w).latStd 0) v La, Function.update_self ..⟩

variable {L} in

theorem Loc.exists_pi_sec {Z : (Loc.pi L).Mdl} (F : (Loc.pi L).Sh Z) (v : ι) (f : (L v).Sec (F v)) :
    ∃ f' : (Loc.pi L).Sec F, f' v = f ∧ ∀ w, w ≠ v → f' w = 0 := by
  classical
  exact ⟨Function.update (β := fun w => (L w).Sec (F w)) (fun _ => 0) v f, Function.update_self ..,
    fun _ h => Function.update_of_ne h _ _⟩

theorem Loc.thetaExt_pi (La : (Loc.pi L).Unim)
    (H : ∀ v, ∃ P : (L v).LBG (La v), (L v).resQ P = (L v).PPq (La v) ∧ (L v).symmG P ∧ (L v).rigG P ∧
      ∀ y, ∃ M : (L v).LBB y (La v), (L v).principal M ∧ (L v).resGt P y = (L v).prPull M) :
    ∃ P : (Loc.pi L).LBG La, (Loc.pi L).resQ P = (Loc.pi L).PPq La ∧ (Loc.pi L).symmG P ∧ (Loc.pi L).rigG P ∧
      ∀ y, ∃ M : (Loc.pi L).LBB y La, (Loc.pi L).principal M ∧ (Loc.pi L).resGt P y = (Loc.pi L).prPull M := by
  choose P h₁ h₂ h₃ h₄ using H
  exact ⟨P, funext h₁, h₂, h₃, fun y => h₄ y.1 y.2⟩

end Values

section Transfer

variable [Finite ι] [Nonempty ι] {L : ι → ModuliIntegralCharts.Loc D r j p} (G : ∀ v, ModuliIntegralCharts.ExtA D (L v))

@[simp] theorem ExtA.pi_flagCl (Z : (Loc.pi L).Mdl) (s : (ExtA.pi G).FlagData Z) (v : ι) :
    (ExtA.pi G).flagCl Z s v = (G v).flagCl (Z v) (s v) := rfl

@[simp] theorem ExtA.pi_blowUp (Z : (Loc.pi L).Mdl) (I : (ExtA.pi G).Idl Z) (v : ι) :
    (ExtA.pi G).blowUp Z I v = (G v).blowUp (Z v) (I v) := rfl

@[simp] theorem ExtA.pi_diagCl (Z₁ Z₂ : (Loc.pi L).Mdl) (c : (ExtA.pi G).Corr Z₁ Z₂) (v : ι) :
    (ExtA.pi G).diagCl Z₁ Z₂ c v = (G v).diagCl (Z₁ v) (Z₂ v) (c v) := rfl

@[simp] theorem ExtA.pi_jIdl_none (d : (ExtA.pi G).IvD none) (v : ι) :
    (ExtA.pi G).jIdl none d v = (G v).jIdl none (d v) := rfl

@[simp] theorem ExtA.pi_jIdl_some (n : ℕ) (d : (ExtA.pi G).IvD (some n)) (v : ι) :
    (ExtA.pi G).jIdl (some n) d v = (G v).jIdl (some n) (d v) := rfl

@[simp] theorem ExtA.pi_ptK (Z : (Loc.pi L).Mdl) (v : ι) (y : (L v).DVP) :
    (ExtA.pi G).ptK Z ⟨v, y⟩ = ⟨v, (G v).ptK (Z v) y⟩ := rfl

@[simp] theorem ExtA.pi_yEta {Z : (Loc.pi L).Mdl} (v : ι) (η : (L v).Gen (Z v)) :
    (ExtA.pi G).yEta (Z := Z) ⟨v, η⟩ = ⟨v, (G v).yEta η⟩ := rfl

@[simp] theorem ExtA.pi_omP {n : ℕ} (h : (ExtA.pi G).HTn n) (v : ι) (y : (L v).Pt ((L v).Xn n)) :
    (ExtA.pi G).omP h ⟨v, y⟩ = (G v).omP (h v) y := rfl

@[simp] theorem ExtA.pi_spz {Z : (Loc.pi L).Mdl} (v : ι) (x x' : (G v).ZP (Z v)) :
    (ExtA.pi G).spz (Z := Z) ⟨v, x⟩ ⟨v, x'⟩ ↔ (G v).spz x x' := sigmaRel_mk

theorem ExtA.pi_isHT {n : ℕ} (h : (ExtA.pi G).HTn n) : (ExtA.pi G).IsHT h ↔ ∀ v, (G v).IsHT (h v) :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem ExtA.pi_blowUp_jIdl (b : Option ℕ) (d : (ExtA.pi G).IvD b) (v : ι) :
    (ExtA.pi G).blowUp (ModuliIntegralCharts.bs (Loc.pi L) b) ((ExtA.pi G).jIdl b d) v =
      (G v).blowUp (ModuliIntegralCharts.bs (L v) b) ((G v).jIdl b (d v)) := by
  cases b <;> rfl

theorem ExtA.zz_of_pi {N : ℕ} {Z : (Loc.pi L).Mdl} (h : (ExtA.pi G).ZZ N Z) (v : ι) : (G v).ZZ N (Z v) := by
  induction h with
  | base b hb => rw [Loc.bs_pi]; exact .base b hb
  | flag s _ ih => exact .flag (s v) ih
  | blow I _ hp hc ih => exact .blow (I v) ih (hp v) fun y e χ => hc ⟨v, y⟩ e χ
  | diag c _ _ ih₁ ih₂ => exact .diag (c v) ih₁ ih₂
  | jblow b d hb => rw [ExtA.pi_blowUp_jIdl]; exact .jblow b (d v) hb

theorem ExtA.aHT_pi_iff : (ExtA.pi G).aHT ↔ ∀ v, (G v).aHT := by
  refine ⟨fun H v Z y => ?_, fun H Z y => H y.1 (Z y.1) y.2⟩
  obtain ⟨Z, rfl⟩ := Loc.exists_pi_mdl L v Z
  exact H Z ⟨v, y⟩

theorem ExtA.aKrull_pi_iff : (ExtA.pi G).aKrull ↔ ∀ v, (G v).aKrull := by
  constructor
  · intro H v Z η x hx
    obtain ⟨Z, rfl⟩ := Loc.exists_pi_mdl L v Z
    exact (H Z ⟨v, η⟩ ⟨v, x⟩ (SigmaRel.mk hx)).imp
      (fun h => sigma_mk_injective (β := fun w => (G w).ZP (Z w)) h) id
  · rintro H Z ⟨v, η⟩ ⟨w, x⟩ hx
    obtain rfl : w = v := SigmaRel.fst_eq hx
    exact (H w (Z w) η x ((ExtA.pi_spz G w _ _).1 hx)).imp
      (congrArg (Sigma.mk (β := fun w => (G w).ZP (Z w)) w)) id

theorem ExtA.aNorm_pi (H : ∀ v, (G v).aNorm) : (ExtA.pi G).aNorm := fun Z F hF f =>
  ⟨fun h v _ => (H v (Z v) (F v) (hF v) (f v)).1 fun η => h ⟨v, η⟩,
    fun B h y => (H y.1 (Z y.1) (F y.1) (hF y.1) (f y.1)).2 B (fun η => h ⟨y.1, η⟩) y.2⟩

theorem ExtA.aTube_pi (H : ∀ v, (G v).aTube) : (ExtA.pi G).aTube := by
  rintro Z ⟨v, η⟩ hη F hF f
  obtain ⟨y, hy⟩ := H v (Z v) η hη (F v) (hF v) (f v)
  exact ⟨⟨v, y⟩, hy⟩

theorem ExtA.aOrd1_pi (H : ∀ v, (G v).aOrd1) : (ExtA.pi G).aOrd1 := fun Z y e χ hχ F hF et i φ h =>
  H y.1 (Z y.1) y.2 e χ hχ (F y.1) (hF y.1) (et y.1) i (φ y.1) (h y.1)

theorem ExtA.aOrd2_pi (H : ∀ v, (G v).aOrd2) : (ExtA.pi G).aOrd2 := fun Z y e χ hχ F hF et het a h =>
  H y.1 (Z y.1) y.2 e χ hχ (F y.1) (hF y.1) (et y.1) (het y.1 (Set.mem_univ _)) a h

theorem ExtA.aOrd3_pi (H : ∀ v, (G v).aOrd3) : (ExtA.pi G).aOrd3 := fun Z F hF et i φ h y =>
  H y.1 (Z y.1) (F y.1) (hF y.1) (et y.1) i (φ y.1) (fun y' => h ⟨y.1, y'⟩) y.2

theorem ExtA.aSub_pi (H : ∀ v, (G v).aSub) : (ExtA.pi G).aSub := fun n Z' hn hZ h C =>
  H C.1 n (Z' C.1) hn (hZ C.1) (fun τ => h τ C.1) C.2

theorem ExtA.aClose_pi (H : ∀ v, (G v).aClose) : (ExtA.pi G).aClose := by
  rintro n Z' hn hZ ⟨v, CQ⟩
  obtain ⟨c, s, m, hc, h⟩ := H v n (Z' v) hn (hZ v) CQ
  have hi : Function.Injective (Sigma.mk (β := fun w => (G w).CrvS (Z' w)) v) := sigma_mk_injective
  refine ⟨c, s.map ⟨_, hi⟩, Function.extend (Sigma.mk v) m 0, hc, fun τ i h₁ h₂ => ?_⟩
  refine (h τ i h₁ h₂).trans (Eq.trans ?_ (Finset.sum_map s ⟨_, hi⟩ _).symm)
  refine Finset.sum_congr rfl fun C _ => ?_
  exact congrArg (fun k : ℕ => (k : ℤ) * (G v).degGr C τ i) (hi.extend_apply m 0 C).symm

theorem ExtA.baseCharts_pi (H : ∀ v, (G v).ChartLiftsThroughSteps) : (ExtA.pi G).ChartLiftsThroughSteps := by
  rintro ⟨v, y⟩ hy N
  obtain ⟨e, φ, h⟩ := H v y hy N
  refine ⟨e, φ, fun b hb => ?_⟩
  cases b with
  | none => exact h none hb
  | some n => exact h (some n) hb

theorem ExtA.aCl_pi (H : ∀ v, (G v).aCl) : (ExtA.pi G).aCl := by
  refine ⟨fun Z s y e χ => (H y.1).1 (Z y.1) (s y.1) y.2 e χ,
    fun Z I y e χ hχ hp => (H y.1).2.1 (Z y.1) (I y.1) y.2 e χ hχ (hp y.1),
    fun Z₁ Z₂ c y e => (H y.1).2.2.1 (Z₁ y.1) (Z₂ y.1) (c y.1) y.2 e, fun b d y e => ?_⟩
  cases b with
  | none => exact (H y.1).2.2.2 none (d y.1) y.2 e
  | some n => exact (H y.1).2.2.2 (some n) (d y.1) y.2 e

theorem ExtA.aHTI_pi (H : ∀ v, (G v).aHTI) : (ExtA.pi G).aHTI := fun n hn h hh =>
  ⟨fun v => (H v n hn (h v) fun y => hh ⟨v, y⟩).1,
    fun y e => (H y.1 n hn (h y.1) fun y' => hh ⟨y.1, y'⟩).2 y.2 e⟩

theorem ExtA.extensionProperty_pi (H : ∀ v, (G v).p0) : (ExtA.pi G).p0 := fun l =>
  ⟨fun f y => (H y.1 l).1 (f y.1) y.2, Set.ext fun f =>
    ⟨fun h y => ((Set.ext_iff.1 (H y.1 l).2 (f y.1)).1 (h y.1 (Set.mem_univ _))) y.2,
      fun h v _ => (Set.ext_iff.1 (H v l).2 (f v)).2 fun y => h ⟨v, y⟩⟩⟩

theorem ExtA.pC_pi (H : ∀ v, (G v).pC) : (ExtA.pi G).pC := by
  rintro ⟨v, y⟩ hy N
  obtain ⟨⟨e, h₁⟩, h₂⟩ := H v y hy N
  refine ⟨⟨e, fun Z hZ => h₁ (Z v) (ExtA.zz_of_pi G hZ v)⟩, fun b hb => ?_⟩
  cases b with
  | none => exact fun e χ hχ d => h₂ none hb e χ hχ (d v)
  | some n => exact fun e χ hχ d => h₂ (some n) hb e χ hχ (d v)

theorem ExtA.pNV_pi (H : ∀ v, (G v).pNV) : (ExtA.pi G).pNV := fun N Z hZ η =>
  H η.1 N (Z η.1) (ExtA.zz_of_pi G hZ η.1) η.2

theorem ExtA.pTR_pi (H : ∀ v, (G v).pTR) : (ExtA.pi G).pTR := by
  intro N Z hZ
  refine ⟨fun F hF f => ?_, fun F₁ F₂ h₁ h₂ φ a b h y =>
    (H y.1 N (Z y.1) (ExtA.zz_of_pi G hZ y.1)).2 (F₁ y.1) (F₂ y.1) (h₁ y.1) (h₂ y.1) (φ y.1) a b
      (fun y' => h ⟨y.1, y'⟩) y.2⟩
  choose y₀ hg hle using fun v => (H v N (Z v) (ExtA.zz_of_pi G hZ v)).1 (F v) (hF v) (f v)
  obtain ⟨v, hv⟩ := Finite.exists_max fun v => (L v).nrm (F v) (f v) (y₀ v)
  exact ⟨⟨v, y₀ v⟩, hg v, fun y => (hle y.1 y.2).trans (hv y.1)⟩

theorem ExtA.pORD_pi (H : ∀ v, (G v).pORD) : (ExtA.pi G).pORD := fun N Z hZ F hF et het i φ h y =>
  H y.1 N (Z y.1) (ExtA.zz_of_pi G hZ y.1) (F y.1) (hF y.1) (et y.1) (het y.1 (Set.mem_univ _)) i (φ y.1) (h y.1) y.2

theorem ExtA.pFJ_pi (H : ∀ v, (G v).pFJ) : (ExtA.pi G).pFJ := fun l f h t =>
  H t.1 l (f t.1) (fun y => h ⟨t.1, y⟩) t.2

theorem ExtA.pHTa_pi_iff : (ExtA.pi G).pHTa ↔ ∀ v, (G v).pHTa := by
  constructor
  · intro H v n hn
    obtain ⟨⟨h, hh⟩, h₂⟩ := H n hn
    exact ⟨⟨h v, fun y => hh ⟨v, y⟩⟩, fun y => h₂ ⟨v, y⟩⟩
  · intro H n hn
    choose h hh using fun v => (H v n hn).1
    exact ⟨⟨h, fun y => hh y.1 y.2⟩, fun y => (H y.1 n hn).2 y.2⟩

theorem ExtA.zz_of_isHTBlowup (HI : ∀ v, (G v).aHTI) {n : ℕ} (hn : 3 ≤ n) {Z' : (Loc.pi L).Mdl}
    (hZ : (Loc.pi L).IsHTBlowup Z' ((Loc.pi L).Xn n)) : (ExtA.pi G).ZZ n Z' := by
  obtain ⟨h, hh, rfl⟩ := ((ExtA.pi G).IsHTBlowup_def n Z' hn).1 hZ
  obtain ⟨h₁, h₂⟩ := ExtA.aHTI_pi G HI n hn h hh
  exact .blow _ (.base (some n) ⟨hn, le_rfl⟩) h₁ h₂

theorem ExtA.pHTb_pi (HI : ∀ v, (G v).aHTI) (H : ∀ v, (G v).pHTb) : (ExtA.pi G).pHTb := fun n hn =>
  ⟨fun h hh y => (H y.1 n hn).1 (h y.1) (fun y' => hh ⟨y.1, y'⟩) y.2, fun Z' hZ =>
    ⟨ExtA.zz_of_isHTBlowup G HI hn hZ, .flag _ (ExtA.zz_of_isHTBlowup G HI hn hZ),
      fun y => ((H y.1 n hn).2 (Z' y.1) (hZ y.1)).2.2.1 y.2,
      fun v => ((H v n hn).2 (Z' v) (hZ v)).2.2.2.1,
      fun s τ v => ((H v n hn).2 (Z' v) (hZ v)).2.2.2.2.1 s τ,
      fun τ v => ((H v n hn).2 (Z' v) (hZ v)).2.2.2.2.2 τ⟩⟩

theorem ExtA.pHTc_pi (H : ∀ v, (G v).pHTc) : (ExtA.pi G).pHTc := fun n hn Z' hZ =>
  ⟨fun l hl => ⟨fun v => ((H v n hn (Z' v) (hZ v)).1 l hl).1, fun v => ((H v n hn (Z' v) (hZ v)).1 l hl).2⟩,
    fun y => (H y.1 n hn (Z' y.1) (hZ y.1)).2.1 y.2, fun v => (H v n hn (Z' v) (hZ v)).2.2⟩

theorem ExtA.pHTd_pi (H : ∀ v, (G v).pHTd) : (ExtA.pi G).pHTd := fun n hn Z' hZ l v =>
  H v n hn (Z' v) (hZ v) l

theorem ExtA.pGG_pi_iff : (ExtA.pi G).pGG ↔ ∀ v, (G v).pGG := by
  constructor
  · rintro ⟨B, h₁, h₂⟩ v
    exact ⟨fun n hn => B n hn v, fun n hn => h₁ n hn v, fun n hn => h₂ n hn v⟩
  · intro H
    choose B h₁ h₂ using H
    exact ⟨fun n hn v => B v n hn, fun n hn v => h₁ v n hn, fun n hn v => h₂ v n hn⟩

theorem ExtA.pDR_pi_iff : (ExtA.pi G).pDR ↔ ∀ v, (G v).pDR :=
  ⟨fun H v => ⟨fun c => H.1 ⟨v, c⟩, fun μ h₁ h₂ c => H.2 μ h₁ h₂ ⟨v, c⟩⟩,
    fun H => ⟨fun c => (H c.1).1 c.2, fun μ h₁ h₂ c => (H c.1).2 μ h₁ h₂ c.2⟩⟩

end Transfer

section TransferB

variable [Nonempty ι] {L : ι → ModuliIntegralCharts.Loc D r j p} (B : ∀ v, BoundaryLocalData.LocB D (L v)) (α : ℕ → 𝓞 D.host.E)
  (hα : ∀ v, (B v).alp = α)

@[simp] theorem LocB.pi_alp :
    (LocB.pi B α hα).alp = α := rfl

@[simp] theorem LocB.pi_phi {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (LocB.pi B α hα).phi (Z := Z) ⟨v, y⟩ = (B v).phi y := rfl

@[simp] theorem LocB.pi_tau {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (LocB.pi B α hα).tau (Z := Z) ⟨v, y⟩ = (B v).tau y := rfl

@[simp] theorem LocB.pi_shiftA {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (LocB.pi B α hα).shiftA (Z := Z) ⟨v, y⟩ = (B v).shiftA y := rfl

@[simp] theorem LocB.pi_psiA {Z : (Loc.pi L).Mdl} (v : ι) (y : (L v).Pt (Z v)) :
    (LocB.pi B α hα).psiA (Z := Z) ⟨v, y⟩ = (B v).psiA y := rfl

@[simp] theorem LocB.pi_oX (v : ι) :
    (LocB.pi B α hα).oX v = (B v).oX := rfl

@[simp] theorem LocB.pi_secOf {F : (Loc.pi L).Sh (Loc.pi L).Xm} (φ : (Loc.pi L).GIso (LocB.pi B α hα).oX F)
    (v : ι) :
    (LocB.pi B α hα).secOf φ v = (B v).secOf (φ v) := rfl

@[simp] theorem LocB.pi_dimB (v : ι) (y : (L v).Pt (L v).Xm) :
    (LocB.pi B α hα).dimB ⟨v, y⟩ = (B v).dimB y := rfl

@[simp] theorem LocB.pi_nfc (v : ι) (y : (L v).Pt (L v).Xm) (nW n : ℕ) :
    (LocB.pi B α hα).nfc ⟨v, y⟩ nW n = (B v).nfc y nW n := rfl

@[simp] theorem LocB.pi_NN (v : ι) (y : (L v).Pt (L v).Xm) (nW n : ℕ) :
    (LocB.pi B α hα).NN ⟨v, y⟩ nW n = (B v).NN y nW n := rfl

theorem LocB.exists_secOf_pi_iff {F : (Loc.pi L).Sh (Loc.pi L).Xm} (s : (Loc.pi L).Sec F) :
    (∃ φ : (Loc.pi L).GIso (LocB.pi B α hα).oX F, (LocB.pi B α hα).secOf φ = s) ↔
      ∀ v, ∃ φ : (L v).GIso (B v).oX (F v), (B v).secOf φ = s v :=
  ⟨fun ⟨φ, h⟩ v => ⟨φ v, congrFun h v⟩, fun H => ⟨fun v => (H v).choose, funext fun v => (H v).choose_spec⟩⟩

theorem LocB.poincareExt_pi (La : (Loc.pi L).Unim)
    (H : ∀ v, ∃ P : (B v).StrictHenselianAcyclic (La v), (B v).res2 P = (B v).PoiQ (La v) ∧ (B v).biext P ∧
      (L v).symmG ((B v).dg P) ∧ (L v).rigG ((B v).dg P) ∧
      ∀ y, ∃ M : (L v).LBB y (La v), (L v).principal M ∧ (L v).resGt ((B v).dg P) y = (L v).prPull M) :
    ∃ P : (LocB.pi B α hα).StrictHenselianAcyclic La, (LocB.pi B α hα).res2 P = (LocB.pi B α hα).PoiQ La ∧ (LocB.pi B α hα).biext P ∧
      (Loc.pi L).symmG ((LocB.pi B α hα).dg P) ∧ (Loc.pi L).rigG ((LocB.pi B α hα).dg P) ∧
      ∀ y, ∃ M : (Loc.pi L).LBB y La, (Loc.pi L).principal M ∧
        (Loc.pi L).resGt ((LocB.pi B α hα).dg P) y = (Loc.pi L).prPull M := by
  choose P h₁ h₂ h₃ h₄ h₅ using H
  exact ⟨P, funext h₁, h₂, h₃, h₄, fun y => h₅ y.1 y.2⟩

theorem LocB.mul_pi_iff : (LocB.pi B α hα).Mul ↔ ∀ v, (B v).Mul := by
  refine ⟨fun H v Z y => ?_, fun H Z y => H y.1 y.2⟩
  obtain ⟨Z, rfl⟩ := Loc.exists_pi_mdl L v Z
  exact H (Z := Z) ⟨v, y⟩

theorem LocB.fer_pi_iff : (LocB.pi B α hα).FER ↔ ∀ v, (B v).FER :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem LocB.regR_pi_iff : (LocB.pi B α hα).RegR ↔ ∀ v, (B v).RegR :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem LocB.locFree_pi_iff : (LocB.pi B α hα).LocFree ↔ ∀ v, (B v).LocFree :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem LocB.fou_pi_iff : (LocB.pi B α hα).Fou ↔ ∀ v, (B v).Fou :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem LocB.freeB_pi_iff : (LocB.pi B α hα).FreeB ↔ ∀ v, (B v).FreeB :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem LocB.actF_pi_iff : (LocB.pi B α hα).ActF ↔ ∀ v, (B v).ActF :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem LocB.jetB_pi_iff : (LocB.pi B α hα).JetB ↔ ∀ v, (B v).JetB :=
  ⟨fun H v y => H ⟨v, y⟩, fun H y => H y.1 y.2⟩

theorem LocB.vthF_pi_iff : (LocB.pi B α hα).VthF ↔ ∀ v, (B v).VthF := by
  constructor
  · intro H v y
    obtain rfl := hα v
    exact H ⟨v, y⟩
  · rintro H ⟨v, y⟩
    obtain rfl := hα v
    exact H v y

theorem LocB.desc_pi (H : ∀ v, (B v).Desc) : (LocB.pi B α hα).Desc := fun h v => H v fun z => h ⟨v, z⟩

omit [Nonempty ι] in

theorem Loc.perf_pi_iff : BoundaryLocalData.LocB.Perf (Loc.pi L) ↔ ∀ v, BoundaryLocalData.LocB.Perf (L v) := by
  refine ⟨fun H v y La => ?_, fun H y La => H y.1 y.2 (La y.1)⟩
  obtain ⟨La, rfl⟩ := Loc.exists_pi_unim L v La
  exact H ⟨v, y⟩ La

end TransferB

example [Fintype ι] [Nonempty ι] {L : ι → ModuliIntegralCharts.Loc D r j p} (G : ∀ v, ModuliIntegralCharts.ExtA D (L v)) (Z : (Loc.pi L).Mdl) :
    Nat.card ((Loc.pi L).Gen Z) = ∑ v, Nat.card ((L v).Gen (Z v)) := by
  haveI := fun v => (G v).genFin (Z v)
  exact Nat.card_sigma

example [Finite ι] [Nonempty ι] {L : ι → ModuliIntegralCharts.Loc D r j p} (G : ∀ v, ModuliIntegralCharts.ExtA D (L v)) (Z : (Loc.pi L).Mdl)
    {v w : ι} (h : v ≠ w) (x : (G v).ZP (Z v)) (x' : (G w).ZP (Z w)) :
    ¬ (ExtA.pi G).spz (Z := Z) ⟨v, x⟩ ⟨w, x'⟩ := fun hs => h (SigmaRel.fst_eq hs)

example (L : ModuliIntegralCharts.Loc D r j p) : (Loc.pi fun _ : Unit => L).Pt (Loc.pi fun _ : Unit => L).Xm ≃ L.Pt L.Xm :=
  Equiv.uniqueSigma fun _ : Unit => L.Pt L.Xm

example (L : ι → ModuliIntegralCharts.Loc D r j p) {Z : (Loc.pi L).Mdl} (F : (Loc.pi L).Sh Z) (f : (Loc.pi L).Sec F) :
    (∀ y, (Loc.pi L).nrm F f y ≤ 1) ↔ ∀ v y, (L v).nrm (F v) (f v) y ≤ 1 := Sigma.forall

end GlobalTheory.LocM

end
