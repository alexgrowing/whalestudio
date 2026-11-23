import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.StepZero

open GlobalTheory.LvT.StartTie

section Deco

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

def redEq {N N' : Submodule (𝓞 X.E) (Fin n → X.E)} (h : N = N') (P : HeightOneSpectrum (𝓞 X.E)) : TDat.Red N P ≃+ TDat.Red N' P :=
  (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq N N' h) (by rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).toAddEquiv

theorem redEq_rfl {N : Submodule (𝓞 X.E) (Fin n → X.E)} (P : HeightOneSpectrum (𝓞 X.E)) (x : TDat.Red N P) : redEq rfl P x = x := by
  induction x using Submodule.Quotient.induction_on
  rfl

def redN {d' d : DecoSet X.E n ST SG} (h : d' = d) (P : ST) : TDat.Red d'.1.N P.1 ≃+ TDat.Red d.1.N P.1 :=
  redEq (congrArg (fun e : DecoSet X.E n ST SG => e.1.N) h) P.1

def redK {d' d : DecoSet X.E n ST SG} (h : d' = d) (P : ST) :
    TDat.Red (d'.1.dnN P) P.1 ≃+ TDat.Red (d.1.dnN P) P.1 :=
  redEq (congrArg (fun e : DecoSet X.E n ST SG => e.1.dnN P) h) P.1

theorem redN_rfl (d : DecoSet X.E n ST SG) (P : ST) (x : TDat.Red d.1.N P.1) : redN (rfl : d = d) P x = x := redEq_rfl _ x

theorem redK_rfl (d : DecoSet X.E n ST SG) (P : ST) (x : TDat.Red (d.1.dnN P) P.1) : redK (rfl : d = d) P x = x := redEq_rfl _ x

open Classical in

def fvD (d : DecoSet X.E n ST SG) (P : ST) : Module.Dual (Res P.1) (TDat.Red d.1.N P.1) :=
  if h : ∃ φ : Module.Dual (Res P.1) (TDat.Red d.1.N P.1), ∀ x : d.1.N, φ (Submodule.Quotient.mk x) = d.1.f P x then h.choose else 0

open Classical in

def teD (d : DecoSet X.E n ST SG) (T : ℕ) (P : ST) : TDat.Red (d.1.dnN P) P.1 :=
  if h : ∃ t : d.1.dnN P, ∃ e ∈ d.1.N, d.1.f P e = 1 ∧ (t : Fin n → X.E) = (T : 𝓞 X.E) • e
  then Submodule.Quotient.mk h.choose else 0

theorem fvD_cast {d' d : DecoSet X.E n ST SG} (h : d' = d) (P : ST) (x : TDat.Red d'.1.N P.1) :
    fvD d' P x = fvD d P (redN h P x) := by subst h; rw [redN_rfl]

theorem teD_cast {d' d : DecoSet X.E n ST SG} (h : d' = d) (T : ℕ) (P : ST) :
    redK h P (teD d' T P) = teD d T P := by subst h; rw [redK_rfl]

theorem redN_smul {d' d : DecoSet X.E n ST SG} (h : d' = d) (P : ST) (r : Res P.1) (x : TDat.Red d'.1.N P.1) :
    redN h P (r • x) = r • redN h P x := by subst h; rw [redN_rfl, redN_rfl]

theorem redK_smul {d' d : DecoSet X.E n ST SG} (h : d' = d) (P : ST) (r : Res P.1) (x : TDat.Red (d'.1.dnN P) P.1) :
    redK h P (r • x) = r • redK h P x := by subst h; rw [redK_rfl, redK_rfl]

theorem up_cast {d' d : DecoSet X.E n ST SG} (h : d' = d) (P : ST) (q : 𝓞 X.E) (x : TDat.Red d'.1.N P.1) :
    d'.up P q ((Quotient.out x : d'.1.N) : Fin n → X.E) = d.up P q ((Quotient.out (redN h P x) : d.1.N) : Fin n → X.E) := by
  subst h; rw [redN_rfl]

theorem dn_cast {d' d : DecoSet X.E n ST SG} (h : d' = d) (P : ST) (g : Module.Dual (Res P.1) (TDat.Red (d'.1.dnN P) P.1))
    (g' : Module.Dual (Res P.1) (TDat.Red (d.1.dnN P) P.1)) (hg : ∀ x, g x = g' (redK h P x)) :
    d'.dn P (TDat.extF _ P.1 g) = d.dn P (TDat.extF _ P.1 g') := by
  subst h
  obtain rfl : g = g' := LinearMap.ext fun x => (hg x).trans (by rw [redK_rfl])
  rfl

end Deco

section Pts2

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

theorem up_deco_of (p : PtY ST SG Q y) (P : ST) (q : 𝓞 X.E) (x : Sp X.E n)
    (hN : (p.1.1.deco.1.up P q x).Ok → (p.mv (p.1.1.deco.up P q x)).1.1.deco.1.N = (p.1.1.deco.1.up P q x).N) :
    (p.mv (p.1.1.deco.up P q x)).1.1.deco = p.1.1.deco.up P q x := by
  by_cases hc : (p.1.1.deco.1.up P q x).Ok
  · apply mv_deco
    refine (hN hc).trans ?_
    unfold DecoSet.up
    rw [dif_pos hc]
  · have h1 : p.1.1.deco.up P q x = p.1.1.deco := dif_neg hc
    rw [h1]
    exact congrArg (fun q : PtY ST SG Q y => q.1.1.deco) (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv p.1.1.deco = _)

theorem dn_deco_of (p : PtY ST SG Q y) (P : ST) (g : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal)
    (hN : (p.1.1.deco.1.dn P g).Ok → (p.mv (p.1.1.deco.dn P g)).1.1.deco.1.N = (p.1.1.deco.1.dn P g).N) :
    (p.mv (p.1.1.deco.dn P g)).1.1.deco = p.1.1.deco.dn P g := by
  by_cases hc : (p.1.1.deco.1.dn P g).Ok
  · apply mv_deco
    refine (hN hc).trans ?_
    unfold DecoSet.dn
    rw [dif_pos hc]
  · have h1 : p.1.1.deco.dn P g = p.1.1.deco := dif_neg hc
    rw [h1]
    exact congrArg (fun q : PtY ST SG Q y => q.1.1.deco) (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv p.1.1.deco = _)

theorem ok_forget {d : Deco X.E n ST SG} (hc : d.Ok) : (Deco.mk (SG := ∅) d.N d.f (fun w => absurd w.2 (Finset.notMem_empty _))).Ok :=
  { lat := hc.lat, uni := hc.uni, f_add := hc.f_add, f_smul := hc.f_smul, f_off := hc.f_off, f_ne := hc.f_ne,
    be_add := fun w => absurd w.2 (Finset.notMem_empty _)
    be_smul := fun w => absurd w.2 (Finset.notMem_empty _)
    be_off := fun w => absurd w.2 (Finset.notMem_empty _)
    be_surj := fun w => absurd w.2 (Finset.notMem_empty _)
    be_ker := fun w => absurd w.2 (Finset.notMem_empty _) }

end Pts2

attribute [local instance] starE

section Top

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem mv_unique {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} (S : GStep E K n) (hf : S.Free) (b : S.β) (d : S.D b) (g : S.G b)
    (h : g • S.rep (S.cl b d) = d) : S.mv b d = g := by
  have := hf b (g⁻¹ * S.mv b d) (S.rep (S.cl b d)) (by rw [mul_smul, S.mv_smul, inv_smul_eq_iff, h])
  exact (inv_mul_eq_one.1 this).symm

theorem cl_of_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b0 : Idx I.sel (I.tup a) (I.idx a) 0) (b : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) 0)
    (b' : Idx I.sel (I.tup a) (I.idx a) 0) (q : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0)
    (e : q'.1.1.deco = q.1.1.deco) :
    (I.stp u a 0).cl b' q' = I.cl0 u a b0 ((I.stp u I.mu0 0).cl b q) := by
  refine (ClsZero.cl_eq_iff h u a b' b0 q' _).2 ?_
  have e2 := (ClsZero.cl_eq_iff h u I.mu0 _ _ _ _).1 (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl b q))
  rw [e]
  exact e2.symm

theorem tr_of_deco (h : I.Ok) (u : B.Word) (a : I.ι) (hf : (I.stp u I.mu0 0).Free) (b : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) 0)
    (b' : Idx I.sel (I.tup a) (I.idx a) 0) (q : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0) (q' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0)
    (e : q'.1.1.deco = q.1.1.deco) (σ : B.fields.K →+* ℂ) :
    (I.stp u a 0).trTo B.fields.emb σ b' q' = (I.stp u I.mu0 0).trTo B.fields.emb σ b q := by
  have hcl := cl_of_deco h u a b' b b' q q' e
  have h0 : (show PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0 from (I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl b q)).1.1.deco =
      (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from (I.stp u a 0).rep ((I.stp u a 0).cl b' q')).1.1.deco := by
    have := ClsZero.stepZero_corresponding_representatives_same_deco h u a b' ((I.stp u I.mu0 0).cl b q)
    rw [← hcl] at this
    exact this.symm
  have hm := (I.stp u a 0).mv_smul b' q'
  obtain ⟨g, g1, g2, g3⟩ := exists_lift (fun N => ClsZero.ys0 I.mu0 ▸ rfl)
    ((ClsZero.levelTypePrimes_stepZero_eq_colLev h I.mu0 b).trans (ClsZero.levelTypePrimes_stepZero_eq_colLev h a b').symm) (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top h I.mu0 b) (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top h a b')
    ((I.stp u a 0).mv b' q') ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl b q)) q ((I.stp u a 0).rep ((I.stp u a 0).cl b' q')) h0
    (e.symm.trans (congrArg (fun r : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => r.1.1.deco) hm).symm)
  have hg : (I.stp u I.mu0 0).mv b q = g := mv_unique _ hf b q g g1
  show (I.stp u a 0).tr B.fields.emb σ b' _ = (I.stp u I.mu0 0).tr B.fields.emb σ b _
  rw [hg]
  exact congrArg₂ (trFr B.fields.emb σ) (congrArg (ufGL B.fields.E (B.R.N 0)) g2.symm) g3.symm

end Top

section Lv
variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem upPt_deco' (u : B.Word) (a : I.ι) (hA : ((I.atIn u a).A 0).Ok (I.atIn u a).T) (hT : ((I.atIn u a).A 0).Tied (I.atIn u a).T)
    (c : (I.stp u a 0).Cl) (P : (I.atIn u a).ST) (x : ((I.atIn u a).A 0).lv P c) (h1 : ((I.atIn u a).A 0).fv P c x = 1) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from ((I.atIn u a).A 0).upPt P c x).1.1.deco =
      (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from (I.stp u a 0).rep c).1.1.deco.up P ((B.T u : ℕ) : 𝓞 B.fields.E)
        ((Quotient.out x : ((I.atIn u a).A 0).N c.1 ((I.stp u a 0).rep c)) : Fin (B.R.N 0) → B.fields.E) := by
  have hx0 : (Submodule.Quotient.mk (Quotient.out x) : ((I.atIn u a).A 0).lv P c) = x := Quotient.out_eq x
  have h2 := DilFv.fv_mk _ hA P c (Quotient.out x)
  rw [hx0, h1] at h2
  exact up_deco_of _ P _ _ fun _ => by
    have h3 := congrArg Deco.N (hT.up_deco c.1 _ P _ (Quotient.out x).2 h2.symm)
    exact h3

theorem dnPt_deco' (u : B.Word) (a : I.ι) (hT : ((I.atIn u a).A 0).Tied (I.atIn u a).T)
    (c : (I.stp u a 0).Cl) (P : (I.atIn u a).ST) (g : Module.Dual (Res P.1) (((I.atIn u a).A 0).lk P c)) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from ((I.atIn u a).A 0).dnPt P c g).1.1.deco =
      (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from (I.stp u a 0).rep c).1.1.deco.dn P (TDat.extF _ P.1 g) :=
  dn_deco_of _ P _ fun hc => by
    have h3 := congrArg Deco.N (hT.dn_deco c.1 _ P _ (ok_forget hc))
    exact h3

theorem diaPt_deco' (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (P : (I.atIn u a).ST) (q : (Res P.1)ˣ) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from ((I.atIn u a).A 0).diaPt P q c).1.1.deco =
      DecoSet.dia1 P q (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from (I.stp u a 0).rep c).1.1.deco :=
  dia_deco _ P q
end Lv

section Fields
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)

include hOk in
theorem rep_eCls0 (c : (I.stp u I.mu0 0).Cl) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from (I.stp u a 0).rep (I.eCls0 l u a c)).1.1.deco =
      (show PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0 from (I.stp u I.mu0 0).rep c).1.1.deco :=
  ClsZero.stepZero_corresponding_representatives_same_deco hOk u a _ c

def eLvA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) : ((I.atIn u a).A 0).lv v (I.eCls0 l u a c) ≃+ ((I.atIn u I.mu0).A 0).lv v c :=
  redN (rep_eCls0 I hOk l u a c) v

def eLkA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) : ((I.atIn u a).A 0).lk v (I.eCls0 l u a c) ≃+ ((I.atIn u I.mu0).A 0).lk v c :=
  redK (rep_eCls0 I hOk l u a c) v

theorem eLvA_smul (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (r : Res v.1) (x : ((I.atIn u a).A 0).lv v (I.eCls0 l u a c)) :
    eLvA I hOk l u a v c (r • x) = r • eLvA I hOk l u a v c x :=
  redN_smul (rep_eCls0 I hOk l u a c) v r x

theorem eLkA_smul (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (r : Res v.1) (x : ((I.atIn u a).A 0).lk v (I.eCls0 l u a c)) :
    eLkA I hOk l u a v c (r • x) = r • eLkA I hOk l u a v c x :=
  redK_smul (rep_eCls0 I hOk l u a c) v r x

theorem fvA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (x : ((I.atIn u a).A 0).lv v (I.eCls0 l u a c)) :
    ((I.atIn u a).A 0).fv v (I.eCls0 l u a c) x = ((I.atIn u I.mu0).A 0).fv v c (eLvA I hOk l u a v c x) :=
  fvD_cast (rep_eCls0 I hOk l u a c) v x

theorem teA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) :
    eLkA I hOk l u a v c (((I.atIn u a).A 0).te (B.T u) v (I.eCls0 l u a c)) = ((I.atIn u I.mu0).A 0).te (B.T u) v c :=
  teD_cast (rep_eCls0 I hOk l u a c) _ v

theorem upA_deco (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (x : ((I.atIn u a).A 0).lv v (I.eCls0 l u a c))
    (h1 : ((I.atIn u a).A 0).fv v (I.eCls0 l u a c) x = 1) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from ((I.atIn u a).A 0).upPt v (I.eCls0 l u a c) x).1.1.deco =
      (show PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0 from ((I.atIn u I.mu0).A 0).upPt v c (eLvA I hOk l u a v c x)).1.1.deco := by
  have h1' : ((I.atIn u I.mu0).A 0).fv v c (eLvA I hOk l u a v c x) = 1 := (fvA I hOk l u a v c x).symm.trans h1
  exact (upPt_deco' I u a ((l.lev u a).lev 0) ((l.lev u a).tied 0) _ v x h1).trans ((up_cast (rep_eCls0 I hOk l u a c) v _ x).trans
    (upPt_deco' I u I.mu0 ((l.lev u I.mu0).lev 0) ((l.lev u I.mu0).tied 0) c v _ h1').symm)

theorem dnA_deco (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (g : Module.Dual (Res v.1) (((I.atIn u a).A 0).lk v (I.eCls0 l u a c)))
    (g' : Module.Dual (Res v.1) (((I.atIn u I.mu0).A 0).lk v c)) (hg : ∀ x, g x = g' (eLkA I hOk l u a v c x)) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from ((I.atIn u a).A 0).dnPt v (I.eCls0 l u a c) g).1.1.deco =
      (show PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0 from ((I.atIn u I.mu0).A 0).dnPt v c g').1.1.deco :=
  (dnPt_deco' I u a ((l.lev u a).tied 0) _ v g).trans ((dn_cast (rep_eCls0 I hOk l u a c) v g g' hg).trans
    (dnPt_deco' I u I.mu0 ((l.lev u I.mu0).tied 0) c v g').symm)

include hOk in
theorem diaA_deco (v : (I.atIn u a).ST) (q : (Res v.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (show PtAt B.R I.sel (I.tup a) (I.cst a) u 0 from ((I.atIn u a).A 0).diaPt v q (I.eCls0 l u a c)).1.1.deco =
      (show PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u 0 from ((I.atIn u I.mu0).A 0).diaPt v q c).1.1.deco :=
  (diaPt_deco' I u a _ v q).trans ((congrArg (DecoSet.dia1 v q) (rep_eCls0 I hOk l u a c)).trans (diaPt_deco' I u I.mu0 c v q).symm)

end Fields

section Cls
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)

theorem upA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (x : ((I.atIn u a).A 0).lv v (I.eCls0 l u a c))
    (h1 : ((I.atIn u a).A 0).fv v (I.eCls0 l u a c) x = 1) :
    (I.stp u a 0).cl (I.eCls0 l u a c).1 (((I.atIn u a).A 0).upPt v (I.eCls0 l u a c) x) =
      I.eCls0 l u a ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).upPt v c (eLvA I hOk l u a v c x))) :=
  cl_of_deco hOk u a _ _ _ _ _ (upA_deco I hOk l u a v c x h1)

theorem upTA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (x : ((I.atIn u a).A 0).lv v (I.eCls0 l u a c))
    (h1 : ((I.atIn u a).A 0).fv v (I.eCls0 l u a c) x = 1) :
    (I.stp u a 0).trTo B.fields.emb B.embLL (I.eCls0 l u a c).1 (((I.atIn u a).A 0).upPt v (I.eCls0 l u a c) x) =
      (I.stp u I.mu0 0).trTo B.fields.emb B.embLL c.1 (((I.atIn u I.mu0).A 0).upPt v c (eLvA I hOk l u a v c x)) :=
  tr_of_deco hOk u a (l.lev u I.mu0).free0 _ _ _ _ (upA_deco I hOk l u a v c x h1) B.embLL

theorem dnA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (g : Module.Dual (Res v.1) (((I.atIn u a).A 0).lk v (I.eCls0 l u a c)))
    (g' : Module.Dual (Res v.1) (((I.atIn u I.mu0).A 0).lk v c)) (hg : ∀ x, g x = g' (eLkA I hOk l u a v c x)) :
    (I.stp u a 0).cl (I.eCls0 l u a c).1 (((I.atIn u a).A 0).dnPt v (I.eCls0 l u a c) g) =
      I.eCls0 l u a ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).dnPt v c g')) :=
  cl_of_deco hOk u a _ _ _ _ _ (dnA_deco I hOk l u a v c g g' hg)

theorem dnTA (v : (I.atIn u a).ST) (c : (I.stp u I.mu0 0).Cl) (g : Module.Dual (Res v.1) (((I.atIn u a).A 0).lk v (I.eCls0 l u a c)))
    (g' : Module.Dual (Res v.1) (((I.atIn u I.mu0).A 0).lk v c)) (hg : ∀ x, g x = g' (eLkA I hOk l u a v c x)) :
    (I.stp u a 0).trTo B.fields.emb B.embLL (I.eCls0 l u a c).1 (((I.atIn u a).A 0).dnPt v (I.eCls0 l u a c) g) =
      (I.stp u I.mu0 0).trTo B.fields.emb B.embLL c.1 (((I.atIn u I.mu0).A 0).dnPt v c g') :=
  tr_of_deco hOk u a (l.lev u I.mu0).free0 _ _ _ _ (dnA_deco I hOk l u a v c g g' hg) B.embLL

include hOk in
theorem dilA (v : (I.atIn u a).ST) (q : (Res v.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.stp u a 0).cl (I.eCls0 l u a c).1 (((I.atIn u a).A 0).diaPt v q (I.eCls0 l u a c)) =
      I.eCls0 l u a ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt v q c)) :=
  cl_of_deco hOk u a _ _ _ _ _ (diaA_deco I hOk l u a v q c)

include hOk in
theorem dilTA (v : (I.atIn u a).ST) (q : (Res v.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.stp u a 0).trTo B.fields.emb B.embLL (I.eCls0 l u a c).1 (((I.atIn u a).A 0).diaPt v q (I.eCls0 l u a c)) =
      (I.stp u I.mu0 0).trTo B.fields.emb B.embLL c.1 (((I.atIn u I.mu0).A 0).diaPt v q c) :=
  tr_of_deco hOk u a (l.lev u I.mu0).free0 _ _ _ _ (diaA_deco I hOk l u a v q c) B.embLL

end Cls

section Bw

theorem locW_of_map {LL : Type} [Field LL] [NumberField LL] (Pl : Rows.Places LL) (w : Pl.Pl) {V V' : Type} [AddCommGroup V] [Module LL V]
    [Module (𝓞 LL) V] [IsScalarTower (𝓞 LL) LL V] [AddCommGroup V'] [Module LL V'] [Module (𝓞 LL) V'] [IsScalarTower (𝓞 LL) LL V']
    (g : V ≃ₗ[LL] V') (M : Submodule (𝓞 LL) V) (M' : Submodule (𝓞 LL) V') (hg : ∀ x ∈ M, g x ∈ M') :
    ∀ x ∈ locW Pl w M, g x ∈ locW Pl w M' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (hg z hz)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [Subring.smul_def, map_smul]
    exact Submodule.smul_mem _ r ha

theorem locW_iff {LL : Type} [Field LL] [NumberField LL] (Pl : Rows.Places LL) (w : Pl.Pl) {V V' : Type} [AddCommGroup V] [Module LL V]
    [Module (𝓞 LL) V] [IsScalarTower (𝓞 LL) LL V] [AddCommGroup V'] [Module LL V'] [Module (𝓞 LL) V'] [IsScalarTower (𝓞 LL) LL V']
    (g : V ≃ₗ[LL] V') (M : Submodule (𝓞 LL) V) (M' : Submodule (𝓞 LL) V') (hg : ∀ x, g x ∈ M' ↔ x ∈ M) (x : V) :
    g x ∈ locW Pl w M' ↔ x ∈ locW Pl w M := by
  constructor
  · intro h
    have := locW_of_map Pl w g.symm M' M (fun y hy => (hg _).1 (by rwa [LinearEquiv.apply_symm_apply])) _ h
    rwa [LinearEquiv.symm_apply_apply] at this
  · exact locW_of_map Pl w g M M' (fun y hy => (hg y).2 hy) x

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)

include hOk in
theorem bwA (e : ((I.fm l u I.mu0).lat 0).V ≃ₗ[B.LL] ((I.fm l u a).lat 0).V)
    (he : ∀ x, (I.fm l u a).emb 0 (e x) = (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 x)) (w : B.places.Pl) (v : (I.atIn u a).ST)
    (x : ((I.fm l u I.mu0).lat 0).V) : e x ∈ (I.fm l u a).Bw 0 w v ↔ x ∈ (I.fm l u I.mu0).Bw 0 w v := by
  have hval : ∀ x c, (e x).1 (I.eCls0 l u a c) = x.1 c := by
    intro x c
    have h1 := congrFun (he x) (I.eCls0 l u a c)
    apply evV_injective B.fields.emb 1 (lamT (B.hcW u) 0) B.embLL (fr0 B.fields.emb B.embLL (B.R.N 0))
    refine h1.trans ?_
    show (I.fm l u I.mu0).emb 0 x ((I.eCls0 l u a).symm (I.eCls0 l u a c)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hker : ∀ c, ((I.atIn u a).A 0).ker (I.eCls0 l u a c).1 (((I.chIn u a).S 0).rep (I.eCls0 l u a c)) v =
      ((I.atIn u I.mu0).A 0).ker c.1 (((I.chIn u I.mu0).S 0).rep c) v :=
    fun c => congrArg (fun d : DecoSet B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs => d.1.LshKer v) (rep_eCls0 I hOk l u a c)
  refine locW_iff _ w e _ _ (fun y => ?_) x
  constructor
  · intro h c
    have := h (I.eCls0 l u a c)
    beta_reduce at this ⊢
    rw [hval, hker c] at this
    exact this
  · intro h c'
    obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
    show (e y).1 (I.eCls0 l u a c) ∈ _
    beta_reduce
    rw [hval, hker c]
    exact h c

end Bw

theorem lvSame_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (A : TwAtT (I.tw l l0 Z) u a), A.eVT = Equiv.refl _ → (∀ v r, (A.eFv v).symm (I.resT l u I.mu0 (A.eVT v) r) = I.resT l u a v r) → Nonempty (LvSame A 0 (I.eCls0 l u a) (Equiv.refl _) ((I.tw l l0 Z).e0 u a)) := by
  intro B X I hOk _ l Z l0 u a A hV hR
  obtain ⟨eVT, eFv, psiT, rhoT, Mu0, duStar, Dstar, GamP, tauOf, seenP⟩ := A
  dsimp only at hV hR
  subst hV
  have hE : ∀ v x, eFv v x = x := by
    intro v x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (congrArg (eFv v) (hR v r)).symm.trans ((eFv v).apply_symm_apply _)
  exact ⟨
    { eLv := fun v c => eLvA I hOk l u a v c
      eLv_smul := fun v c r x => by rw [hE]; exact eLvA_smul I hOk l u a v c r x
      fv := fun v c x => by rw [hE]; exact fvA I hOk l u a v c x
      up := fun v c x h1 => upA I hOk l u a v c x h1
      upT := fun v c x h1 h y => congrFun (DFunLike.congr_fun (upTA I hOk l u a v c x h1) h) y
      eLk := fun v c => eLkA I hOk l u a v c
      eLk_smul := fun v c r x => by rw [hE]; exact eLkA_smul I hOk l u a v c r x
      te := fun v c => teA I hOk l u a v c
      dn := fun v c g g' hg _ => dnA I hOk l u a v c g g' fun x => (hE v _).symm.trans (hg x)
      dnT := fun v c g g' hg _ h y => congrFun (DFunLike.congr_fun (dnTA I hOk l u a v c g g' fun x => (hE v _).symm.trans (hg x)) h) y
      dil := fun v r c => by
        have key : ∀ q r' : (Res v.1)ˣ, (q : Res v.1) = r' →
            (I.stp u a 0).cl (I.eCls0 l u a c).1 (((I.atIn u a).A 0).diaPt v r' (I.eCls0 l u a c)) =
              I.eCls0 l u a ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt v q c)) := by
          intro q r' hq
          obtain rfl : q = r' := Units.ext hq
          exact dilA I hOk l u a v q c
        exact key _ r (hE v _)
      dilT := fun v r c h y => by
        have key : ∀ q r' : (Res v.1)ˣ, (q : Res v.1) = r' →
            (I.stp u a 0).trTo B.fields.emb B.embLL (I.eCls0 l u a c).1 (((I.atIn u a).A 0).diaPt v r' (I.eCls0 l u a c)) =
              (I.stp u I.mu0 0).trTo B.fields.emb B.embLL c.1 (((I.atIn u I.mu0).A 0).diaPt v q c) := by
          intro q r' hq
          obtain rfl : q = r' := Units.ext hq
          exact dilTA I hOk l u a v q c
        exact congrFun (DFunLike.congr_fun (key _ r (hE v _)) h) y
      bw := fun w _ _ v x => bwA I hOk l u a ((I.tw l l0 Z).e0 u a) (l0 u a).choose_spec.2 w v x }⟩

end GlobalTheory.Mem.Col2.TC.StepZero

end
