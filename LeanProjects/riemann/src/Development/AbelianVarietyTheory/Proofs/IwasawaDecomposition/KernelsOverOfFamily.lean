import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelAtPointPenultimateStepFirstCoupledKernel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsAtFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep GlobalTheory.GO
open GlobalTheory.LvT.Built (kAt)

namespace GlobalTheory.Mem.Col2.KerRat

section General

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  (A : Amb X) {G : ChGlob X R.m} {m2 : ℕ} (u : Pr.Word)

theorem lam_root (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (b : L.β j) (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)})
    (g : (L.levQ j b P).H) : ∃ k : ℕ, 0 < k ∧ (L.levQ j b P).lam g ^ k = 1 := by
  classical
  by_cases hP : P.1 ∈ Pr.vGs
  · exact LevFin.lam_root_G hL b P hP g
  by_cases hj : j ≤ m2 + 1
  · exact ChRoot.lam_root hL hj b P hP g
  obtain ⟨r, hr, hrg⟩ := Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)
  have hχ := hL.chrQ j b P g r hr hrg
  have h0 : Loc.n1Arg r = 0 := by
    unfold Loc.n1Arg
    rw [show cOf R j - 1 = 0 by have := hL.hm; unfold cOf; omega, Finset.sum_range_zero]
  simp only [chiInv, lamRow, hP, if_false, LocE.lamQB, h0, hL.cst_ok.psi_int _ 0 ChRoot.intAt_zero', inv_one, one_mul] at hχ
  have hne := ((L.levQ j b P).lam g).ne_zero
  rw [hχ] at hne
  obtain ⟨k, hk, h2⟩ := ChRoot.unitV_root _ _ (fun h0 => hne (inv_eq_zero.2 h0))
  refine ⟨k, hk, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hχ, inv_pow, h2, inv_one, Units.val_one]

theorem chF_ok (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2) (j : ℕ) : (chF W sel mu L u j).Ok := fun b =>
  FramedForms.main hX (W.lamTrue u j) (L.levG j b) (L.levQ j b) (LevFin.lev_finiteIndex hL j b) fun g => by
    rw [← isOfFinOrder_iff_pow_eq_one, levQ_chr_apply]
    exact Finset.prod_induction _ IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one fun P _ =>
      isOfFinOrder_iff_pow_eq_one.2 (lam_root hL b P _)

theorem ybHyp (hm : R.m = m2 + 2) (b : L.β (m2 + 1)) : YbHyp (R := R) sel mu cst L u m2 b :=
  ⟨fun p => ysAt_ys_of_eq sel mu cst hm.symm _ ▸ (CosetFin.ysAt_finite_nonempty R sel mu cst (m2 + 1) _ p.deco.2.lat).1⟩

theorem kerEquivC (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (hs : cst.sharp = true) (hT : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2)) (b : L.β (m2 + 1))
    (hY : YbHyp (R := R) sel mu cst L u m2 b) : KerEquivC W Ch sel mu cst L A u m2 b hY (rPsymF Ch) :=
  ⟨MatLaw.matEquiv hX hPr hsel hS hL hT, cp1Equiv_of_on W Ch sel mu cst L _ b hY (CoupledLaw.cp1EquivOn b hY hX hPr hsel hS hL hT),
    (TopLaw.topEquiv b hY default hX hPr hsel hS hL (Or.inr ⟨hs, rfl⟩) hT).cp2Equiv hX hPr hL.hm hL.cst_ok
      (tilOk_of_avoid hPr hsel u hS) (tameFr_chTh W Ch sel mu cst A u m2)⟩

theorem chTh_ok_of_thHyp (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (h : ThHyp W Ch sel mu cst A u m2) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2) := by
  have hm := hL.hm
  have hq := muqTie_of_ok Ch sel mu cst L hL
  exact ⟨fun i hi => ChainTheta.stepC_ok_deg W Ch sel mu cst A u i (by omega) (i + 1) (hPr.T_prime u).pos hq (h.1 i hi).1 (h.1 i hi).2.1
      (fun N N' c x hx m _ => (h.1 i hi).2.2 N N' c x hx m) (h.2.2.1 i hi),
    ChainTheta.stepC_ok_deg W Ch sel mu cst A u (m2 + 1) (by omega) R.m (hPr.T_prime u).pos hq h.2.1.1 h.2.1.2.1
      (fun N N' c x hx m _ => h.2.1.2.2 N N' c x hx m) h.2.2.2⟩

theorem anaStep_of_thHyp (hm : R.m = m2 + 2) (h : ThHyp W Ch sel mu cst A u m2) {i : ℕ} (hi : i < R.m) :
    A.AnaStep (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) := by
  by_cases h1 : i ≤ m2
  · exact h.1 i h1
  · obtain rfl : i = m2 + 1 := by omega
    rw [show m2 + 1 + 1 = R.m from hm.symm]
    exact h.2.1

theorem kAt_top_heq (hL : L.Ok Ch sel mu cst G m2) (b : Idx sel mu L (m2 + 1)) (b' : Idx sel mu L (m2 + 1 + 1))
    (p : PtAt R sel mu cst u (m2 + 1)) (p' : PtAt R sel mu cst u (m2 + 1 + 1)) (q : ChPt (R := R) sel mu u R.m) (e : HEq p'.1.1 q)
    (x : VV X.K (W.lamTrue u (m2 + 1))) :
    HEq (kAt W Ch sel mu cst L A u (m2 + 1) b b' p p' x) (topDegreeKTwo W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p.1.1 p.1.2 q x) := by
  have key : ∀ (j : ℕ) (h : j = R.m) (q' : ChPt (R := R) sel mu u j), HEq q' q →
      HEq (KerT.ker W Ch sel mu cst A u (m2 + 1) j p.1.1.deco.1.N (frsF sel mu p.1.1) q'.deco.1.N (frsF sel mu q')
        (xiOver Ch sel mu cst m2 h p.1.1 p.1.2 q') x) (topDegreeKTwo W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p.1.1 p.1.2 q x) := by
    rintro _ rfl q' e
    obtain rfl := eq_of_heq e
    rw [ker_top W Ch A u hL]
    exact HEq.rfl
  unfold kAt
  rw [xiAt_last Ch sel mu cst L hL.hm.symm]
  exact key _ _ _ e

variable {u} {r : Reps sel mu cst L u (topLev Ch sel mu cst (rPsymF Ch))} {rho : ∀ i, (r.step i).Cl → ℂ}
  {rho' : ∀ i, (r.step (i + 1)).Cl → ℂ}
  {jet : ∀ i, (r.step i).Cl → (r.step (i + 1)).Cl → (Pol ℂ X.Tau (R.N i) →ₗ[ℂ] Pol ℂ X.Tau (R.N (i + 1)))} {DG : ℕ}

theorem eqTarget (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) (hs : cst.sharp = true) (hT : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (i : ℕ) (hi : i < R.m) : EqTarget X.emb (kPt W Ch A r rho rho' jet DG) i := by
  intro b b' g' d d'
  have key : kAt W Ch sel mu cst L A u i b b' ((1 : (r.step i).G b) • (d : (r.step i).D b)) (g' • d') =
      (r.step (i + 1)).rho X.emb (W.lamTrue u (i + 1)) b' g' ∘ₗ kAt W Ch sel mu cst L A u i b b' d d' ∘ₗ
        (r.step i).rho X.emb (W.lamTrue u i) b 1⁻¹ := by
    rcases lt_trichotomy (i + 2) R.m with h | h | h
    · exact MatLaw.kAt_equiv X Pr R W Ch sel S mu cst L G m2 u i A hX hPr hCh hsel hS.1 hS.2 hL hs hT h b b' 1 g' d d'
    · exact CoupledLaw.kAt_equiv X Pr R W Ch sel S mu cst L G m2 u i A hX hPr hCh hsel hS.1 hS.2 hL hs hT h b b' 1 g' d d'
    · exact LvT.Built.TopEq.kAt_top_equiv X Pr R W Ch sel S mu cst L G m2 u i A hX hPr hCh hsel hS.1 hS.2 hL hs hT (by omega)
        b b' 1 g' d d'
  rw [one_smul, inv_one, map_one] at key
  exact key

end General

section True

open GlobalTheory.Mem GlobalTheory.Mem.Chr Formalism.MainNotions

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

def reps (u : B.Word) (a : I.ι) : Reps (Pr := B.primes X) I.sel (I.tup a) (I.cst a) (I.idx a) u (I.Tp a) :=
  ⟨fun j => (I.stp u a j).rp, fun j => (I.stp u a j).rp_spec⟩

abbrev kTrue (u : B.Word) (a : I.ι) : PtKer (I.chIn u a) (B.hcW u) :=
  fun i => kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i

abbrev thTrue (u : B.Word) (a : I.ι) (m2 : ℕ) : ChTh (Pr := B.primes X) B.wts I.sel (I.tup a) u m2 :=
  chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u m2

abbrev evT (B : GlobalTheory.Mem.Base) (u : B.Word) (i : ℕ) :
    VV B.fields.K (lamT (B.hcW u) i) →ₛₗ[B.embLL] (Fr B.fields.emb B.embLL (B.R.N i) → ℂ) :=
  evV B.fields.emb 1 (lamT (B.hcW u) i) B.embLL

variable {I}

theorem readsAt (h : I.Ok) (hJ : I.JetsIn) (u : B.Word) (a : I.ι) (hI : (I.chIn u a).Ok) {i : ℕ} (hi : i < B.R.m)
    (hLa : I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (I.Sb a u)) (hE : I.A.ESmooth (B.R.N i) (B.R.N (i + 1))) :
    ReadsAt B.fields.emb B.embLL hI (kTrue I u a) i := by
  intro c c' F
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have h0 : I.A.AA ≠ ⊥ := by
    rw [I.A_AA, Ne, FractionalIdeal.coeToSubmodule_eq_bot]
    refine inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 fun h0 => ?_)
    have h1 := B.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact (differentIdeal_ne_bot : differentIdeal (𝓞 B.host.K) (𝓞 B.host.E) ≠ ⊥) h1
  refine LvT.Built.KMap.kmap_of_jet (X := B.fields) _ B.embLL hI (B.hcW u) hi c c' F _ ?_
  have hV := ChSrc.jetInVV_trueWt (X := B.fields) (B.hcW u) hi
  have e := ChSrc.nuEnd_eq (Pr := B.primes X) B.wts u hi
  have key := fun (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1)) =>
    LvT.Built.KMap.map_kerOf I.A (I.Sb a u) (rowSG (B.primes X) I.sel (I.tup a))
      (pow_pos (Finset.prod_pos fun P _ => ChRoot.qOf_pos P.1) _ : 0 < cAof I.sel (I.tup a) (I.cst a))
      (MoveCompare.cBof_pos hPr I.sel (I.tup a) (I.cst a) u) I.sel (mUof (R := B.R) I.Ch (I.tup a) i)
      (muAtT (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i) (B.wts.lamTrue u i) (B.wts.lamTrue u (i + 1))
      (nuLast (Pr := B.primes X) B.wts u i) (e ▸ hV) hLa h0 hE (frsF I.sel (I.tup a) p.1.1) (frsF I.sel (I.tup a) p'.1.1)
      ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
      ((MoveCompare.jetsIn_iff _ _ _ _ _ _ _ (MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi) _ _).2
        (MoveCompare.jetsAll_of_deg _ _ _ _ _ (hJ a u i hi) (MoveCompare.cBof_pos hPr _ _ _ u)
          ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩ ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩))
      (LvT.Built.Box.inBox_xiAt _ _ _ I.Ch I.sel _ _ _ _ _ _ u i hX hPr h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) hi
        ⟨_, _, _, _, h.ch_tied⟩ c.1 c'.1 p p') F
  refine (key (GStep.rep _ c) (GStep.rep _ c')).trans ?_
  rw [← LvT.Built.KMap.rhoIs I h a u hi c.1 (GStep.rep _ c) c'.1 (GStep.rep _ c'), ← e]
  rfl

variable (I) (l : I.Laws)

def colForm (h : I.Ok) (u : B.Word) (a : I.ι) (φ : MfV (Pr := B.primes X) B.wts I.Ch u) : ((I.fm l u a).lat 0).V :=
  ⟨fun c => φ.1 ((I.stp u a 0).rep c).1.1.deco, fun c g =>
    (StepZero.form_smul ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (StepZero.levGAt_zero (I.Tp a) (h.idx_ok a))
      (StepZero.levQAt_zero (I.Tp a) (h.idx_ok a)) φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩

theorem tilOk (h : I.Ok) (u : B.Word) (a : I.ι) : TilOk (B.primes X) I.sel (I.tup a) u :=
  tilOk_of_avoid (base_fields_primes_ok B X).2.1 h.sel_ok u ⟨h.T_mem u, h.g_mem⟩

def rowForm (h : I.Ok) (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) : (I.per l u a).Mt :=
  PeriodOnStep.rowEmb (Pr := B.primes X) (I := I.chIn u a) B.wts I.Ch I.sel (I.tup a) I.Ps (I.perIn u a).b0 (I.perIn u a).til
    (I.perIn u a).ext (I.perIn u a).tz (I.perIn u a).H (tilOk I h u a).2.2 B.embLL z

structure KernelsOver (h : I.Ok) (u : B.Word) (a : I.ι) : Prop where

  mat : ∀ i (hi : i + 2 < B.R.m) c c' x, (I.chain l u a).Kmap i c c' (evT B u i x) = evT B u (i + 1)
    (matK (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (thTrue I u a (B.R.m - 2)) i (Idx.get c.1 (by omega))
      (Idx.get c'.1 (by omega)) ((I.stp u a i).rep c).1.1 ((I.stp u a (i + 1)).rep c').1.1 x)

  cp1 : ∀ c c' x, (I.chain l u a).Kmap (B.R.m - 2) c c' (evT B u _ x) = evT B u _
    (cp1K (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (thTrue I u a (B.R.m - 2))
      (Idx.get c.1 (by have := h.hm; omega)) ((I.stp u a _).rep c).1.1 ((I.stp u a _).rep c').1.1 ((I.stp u a _).rep c').1.2 x)

  top : ∀ c c' x q, HEq ((I.stp u a (B.R.m - 2 + 1 + 1)).rep c').1.1 q → ∃ y,
    (I.chain l u a).Kmap (B.R.m - 2 + 1) c c' (evT B u _ x) = evT B u _ y ∧
      HEq y (topDegreeKTwo (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (thTrue I u a (B.R.m - 2))
        ((I.stp u a _).rep c).1.1 ((I.stp u a _).rep c).1.2 q x)

  cp2 : ∀ c c' x d, ((I.stp u a (B.R.m - 2 + 1 + 1)).rep c').1.1 = tilAt I.sel (I.tup a) u h.hm.symm d → ∃ y,
    (I.chain l u a).Kmap (B.R.m - 2 + 1) c c' (evT B u _ x) = evT B u _ y ∧
      HEq y (cp2K (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (thTrue I u a (B.R.m - 2))
        ((I.stp u a _).rep c).1.1 ((I.stp u a _).rep c).1.2 (toRow I.sel (I.tup a) d) x)

  krat : ∀ i, i < B.R.m → (I.fm l u a).KRat i

  prat : (I.fm l u a).PRat

  period : Nonempty ((I.idx a).β (B.R.m - 2 + 1)) ∧ ∀ b : (I.idx a).β (B.R.m - 2 + 1),
    ∃ (hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) b)
      (hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY I.Ps)
      (hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok)
      (hM : (mtildeGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps).Ok), ∀ φ z,
        (I.per l u a).PtilCol ((I.fm l u a).emb 0 (colForm I l h u a φ)) (rowForm I l h u a z) =
          B.embLL (PtilFF (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps hM u
            (colMu (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY I.Ps hK hF
              (h.idx_ok a) φ).1 z.1)

section Parts

variable {I} {u : B.Word} {a : I.ι}

theorem eqTarget_true (h : I.Ok) (hT : ChTh.Ok (Ch := I.Ch) (I.cst a) (thTrue I u a (B.R.m - 2))) (i : ℕ) (hi : i < B.R.m) :
    EqTarget B.fields.emb (kTrue I u a) i :=
  eqTarget (Pr := B.primes X) (r := reps I u a) (rho := (I.chIn u a).rho) (rho' := (I.chIn u a).rho') (jet := (I.chIn u a).jet)
    (DG := (I.chIn u a).DG) B.wts I.A (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 h.ch_ok h.sel_ok
    ⟨h.T_mem u, h.g_mem⟩ (h.idx_ok a) (h.sharp a) hT i hi

theorem kRat_true {i : ℕ} (hR : ReadsAt B.fields.emb B.embLL (l.ch u a) (kTrue I u a) i) (hE : EqTarget B.fields.emb (kTrue I u a) i) :
    (I.fm l u a).KRat i :=
  fun x => exists_K_embF hR hE ((l.fmL u a).fam i) ((l.fmL u a).fam (i + 1)) x

variable (u a) in

theorem pRat_true : (I.fm l u a).PRat := by
  have hw := LvT.BuiltChain.weights_ok (I.perIn u a) (B.hcW u) B.fields.emb
    fun τ => congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  exact fun x => exists_lower_embF (I.perIn u a) (l.per u a) (fun τ => (hw τ).1) (fun τ => (hw τ).2) ((l.fmL u a).fam _)
    (l.fmL u a).famP x

theorem period_true (h : I.Ok) (hR : ∀ i, i < B.R.m → ReadsAt B.fields.emb B.embLL (l.ch u a) (kTrue I u a) i)
    (hE : ∀ i, i < B.R.m → EqTarget B.fields.emb (kTrue I u a) i) {b : (I.idx a).β (B.R.m - 2 + 1)}
    (hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) b)
    (hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY I.Ps)
    (hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok)
    (hM : (mtildeGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps).Ok) (φ : MfV (Pr := B.primes X) B.wts I.Ch u)
    (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) :
    (I.per l u a).PtilCol ((I.fm l u a).emb 0 (colForm I l h u a φ)) (rowForm I l h u a z) =
      B.embLL (PtilFF (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps hM u
        (colMu (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY I.Ps hK hF
          (h.idx_ok a) φ).1 z.1) :=
  ptilCol_eq (Pr := B.primes X) B.wts I.Ch I.A (reps I u a) (I.chIn u a).rho (I.chIn u a).rho' (I.chIn u a).jet (I.chIn u a).DG
    (l.ch u a) hK hF (h.idx_ok a) φ (base_fields_primes_ok B X).1 l.pr B.wts_isOk h.sel_ok (tilOk I h u a) B.embLL hR hE
    (I.perIn u a).b0 (I.perIn u a).ext (I.perIn u a).H (l.per u a) hM z

end Parts

theorem kernelsOver_of_ok (h : I.Ok) (hJ : I.JetsIn) (u : B.Word) (a : I.ι)
    (hT : ChTh.Ok (Ch := I.Ch) (I.cst a) (thTrue I u a (B.R.m - 2)))
    (hA : ∀ i, i < B.R.m → I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (I.Sb a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N (i + 1))) :
    KernelsOver I l h u a := by
  have hX := (base_fields_primes_ok B X).1
  have hm := h.hm
  have hL := h.idx_ok a
  have hR : ∀ i, i < B.R.m → ReadsAt B.fields.emb B.embLL (l.ch u a) (kTrue I u a) i := fun i hi =>
    readsAt h hJ u a (l.ch u a) hi (hA i hi).1 (hA i hi).2
  have hE := eqTarget_true h hT
  refine ⟨fun i hi c c' x => ?_, fun c c' x => ?_, fun c c' x q e => ?_, fun c c' x d e => ?_,
    fun i hi => kRat_true l (hR i hi) (hE i hi), pRat_true l u a, ⟨hL.last_uniq.choose⟩, fun b => ?_⟩
  · rw [← kAt_mat (Pr := B.primes X) B.wts I.Ch I.A u hL hi, Idx.of_get, Idx.of_get]
    exact hR i (by omega) c c' x
  · rw [← kernelAtPoint_penultimateStep_firstCoupledKernel (Pr := B.primes X) B.wts I.Ch I.A u hL _ c'.1, Idx.of_get]
    exact hR _ (by omega) c c' x
  · exact ⟨_, hR (B.R.m - 2 + 1) (by omega) c c' x, kAt_top_heq (Pr := B.primes X) B.wts I.A u hL c.1 c'.1 _ _ q e x⟩
  · rw [← k2top_tilF hX l.pr h.sel_ok hm hL.cst_ok (tilOk I h u a)
      (tameFr_chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u _)]
    exact ⟨_, hR (B.R.m - 2 + 1) (by omega) c c' x,
      kAt_top_heq (Pr := B.primes X) B.wts I.A u hL c.1 c'.1 _ _ _ ((eq_tilAt_iff I.sel (I.tup a) _ _ d).1 e) x⟩
  · have hY := ybHyp (Pr := B.primes X) (cst := I.cst a) u hm b
    have hK := kerEquivC (Pr := B.primes X) B.wts I.A u hX l.pr h.sel_ok ⟨h.T_mem u, h.g_mem⟩ hL (h.sharp a) hT b hY
    have hF := chF_ok (Pr := B.primes X) B.wts u hX hL
    have hM := mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps
    exact ⟨hY, hK, hF, hM, period_true l h hR hE hY hK hF hM⟩

variable (Z : TC.Later B (I.cols l))

abbrev ThHypAt (u : B.Word) (a : I.ι) : Prop :=
  ThHypN (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.glob (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD u (B.R.m - 2)

abbrev FamilyLaws : Prop :=
  (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).EqP I.chi ∧ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi

theorem kernelsOver_of_thHyp (h : I.Ok) (hJ : I.JetsIn) (u : B.Word) (a : I.ι) (hT : ThHypAt I l Z u a) : KernelsOver I l h u a := by
  have h1 : ThHyp (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2) := by
    rw [ColIn.A, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact hT.2.2
  exact kernelsOver_of_ok I l h hJ u a (chTh_ok_of_thHyp (Pr := B.primes X) B.wts I.A u l.pr (h.idx_ok a) h1) fun i hi =>
    ⟨(anaStep_of_thHyp (Pr := B.primes X) B.wts I.A u h.hm h1 hi).1, (anaStep_of_thHyp (Pr := B.primes X) B.wts I.A u h.hm h1 hi).2.1⟩

theorem kernelsOver_of_family (h : I.Ok) (hJ : I.JetsIn) (hT : FamilyLaws I l Z) (u : B.Word) (a : I.ι) : KernelsOver I l h u a :=
  kernelsOver_of_ok I l h hJ u a (ChainTheta.chTh_ok_of_colIn' B _ Z.W Z.V Z.S Z.N Z.G I h hJ hT.1 hT.2 a u) fun i _ =>
    LvT.Built.KMap.laHyp_of_vecP I _ Z.W Z.V Z.S Z.N Z.G h hT.2 a u i (i + 1)

theorem kernels_rational (h : I.Ok) (hJ : I.JetsIn) (hT : (∀ u a, ThHypAt I l Z u a) ∨ FamilyLaws I l Z) :
    (∀ u a, KernelsOver I l h u a) ∧
      (∀ u, (∀ i, i < (I.rec7 l Z).R.m → ((I.rec7 l Z).fm u).KRat i) ∧ ((I.rec7 l Z).fm u).PRat) ∧
      ∀ (l0 : I.Law0 l) u μ, (∀ i, i < (I.rec7 l Z).R.m → ((I.tw l l0 Z).fm u μ).KRat i) ∧ ((I.tw l l0 Z).fm u μ).PRat := by
  have key : ∀ u a, KernelsOver I l h u a := fun u a =>
    hT.elim (fun hT => kernelsOver_of_thHyp I l Z h hJ u a (hT u a)) fun hT => kernelsOver_of_family I l Z h hJ hT u a
  exact ⟨key, fun u => ⟨(key u I.mu0).krat, (key u I.mu0).prat⟩, fun _ u μ => ⟨(key u μ).krat, (key u μ).prat⟩⟩

end True

end GlobalTheory.Mem.Col2.KerRat
