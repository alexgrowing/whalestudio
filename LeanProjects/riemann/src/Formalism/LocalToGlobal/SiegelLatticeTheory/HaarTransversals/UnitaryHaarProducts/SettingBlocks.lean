import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.WuDecay
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

namespace Formalism.L2.SG.SplitPrimeNormLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev gD : ℕ := D.host.g 0 * D.host.g 1

structure UnitaryGroupInstance where
  I : AutInst
  ιE : I.E ≃+* D.host.E
  ιE_conj : ∀ x : I.E, ιE (star x) = D.host.conj (ιE x)
  ιE_F : ∀ y : D.host.E, y ∈ D.host.F ↔ ∃ a : I.F, ιE (algebraMap I.F I.E a) = y
  bas : Module.Basis (Fin I.n) D.host.E (VS D).V
  J_eq : ∀ i j, ιE (I.J i j) = (VS D).hT (bas i) (bas j)
  L_eq : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0
  pl : InfinitePlace I.F ≃ D.what₂.Tau
  φ_eq : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)
  n_eq : I.n = D.R.r
  eps_eq : ∀ v (i : Fin I.n), I.ε v i = epsS D.R (Fin.cast n_eq i)

structure UnitaryLatticeData where
  eX : Fin D.R.rS → (VS D).V
  fY : Fin D.R.rS → (VS D).V
  ee : ∀ a b, (VS D).hT (eX a) (eX b) = 0
  ff : ∀ a b, (VS D).hT (fY a) (fY b) = 0
  ef : ∀ a b, (VS D).hT (eX a) (fY b) = if a = b then 1 else 0
  Lb : Submodule (𝓞 D.host.E) (VS D).V
  Lb_perp : ∀ x ∈ Lb, ∀ a, (VS D).hT (eX a) x = 0 ∧ (VS D).hT (fY a) x = 0
  Lam_split : (VS D).L0 = latSpanS (fun a => aaD D a) eX ⊔ Lb ⊔ latSpanS (fun a => (aaD D a)⁻¹) fY
  zu : D.what₂.Word → (VS D).V
  zu_norm : ∀ u, (VS D).hT (zu u) (zu u) = -(((D.mem u).A.T : ℕ) : D.host.E)
  zu_orth : ∀ u a, (VS D).hT (eX a) (zu u) = 0 ∧ (VS D).hT (fY a) (zu u) = 0
  zu_Lb : ∀ u, zu u ∈ Lb
  Fu : ∀ u, FlagS D u
  Fu_e : ∀ u, (Fu u).e = eX
  flagZVector : ∀ u, (Fu u).z = zu u
  Fu_fixed : ∀ u, Formalism.MainNotions.S.Lat.FixedHyp D (VS D).L0
    (⟨Fu u, zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (VS D) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))

variable {D}

structure AdditiveCharacterData (A : UnitaryGroupInstance D) where
  psiEf : A.I.E ⊗[A.I.F] Af A.I.F → ℂ
  psiEf_add : ∀ x y, psiEf (x + y) = psiEf x * psiEf y
  psiEf_int : ∀ x ∈ IntAf A.I.F A.I.E, psiEf x = 1
  psiEf_rat : ∀ x : A.I.E, psiEf (Formalism.UG.inclE (F := A.I.F) (Af A.I.F) x) * psiEinf A.I x = 1

structure ReferenceFrame (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) where
  e0 : Fin D.R.rS → VA A.I
  f0 : Fin D.R.rS → VA A.I
  z0 : VA A.I
  bw : Fin D.R.k → VA A.I
  bwd : Fin D.R.k → VA A.I
  ew : A.I.E ⊗[A.I.F] Af A.I.F
  vectorsInLattice : (∀ a, e0 a ∈ A.I.Lf ∧ f0 a ∈ A.I.Lf) ∧ z0 ∈ A.I.Lf ∧ ∀ i, bw i ∈ A.I.Lf ∧ bwd i ∈ A.I.Lf
  basisApprox : ∀ a, InAt A.I (gD D) (gD D) (e0 a - incl A.I (crdOf A.I A.ιE A.bas (L.eX a))) ∧
    InAt A.I (gD D) (gD D) (f0 a - incl A.I (crdOf A.I A.ιE A.bas (L.fY a)))
  gramIntegral : ∀ a b, ZMod' A.I (gD D) (hA A.I (e0 a) (e0 b)) ∧ ZMod' A.I (gD D) (hA A.I (f0 a) (f0 b)) ∧
    ZMod' A.I (gD D) (hA A.I (e0 a) (f0 b) - if a = b then 1 else 0)
  formsAtZero : ZMod' A.I (gD D) (hA A.I z0 z0 + 1) ∧
    ∀ a, ZMod' A.I (gD D) (hA A.I (e0 a) z0) ∧ ZMod' A.I (gD D) (hA A.I (f0 a) z0)
  weightVectorsIntegral : ∀ i, ZMod' A.I (gD D) (hA A.I z0 (bw i)) ∧ ZMod' A.I (gD D) (hA A.I z0 (bwd i)) ∧
    ∀ a, ZMod' A.I (gD D) (hA A.I (e0 a) (bw i)) ∧ ZMod' A.I (gD D) (hA A.I (f0 a) (bw i)) ∧
      ZMod' A.I (gD D) (hA A.I (e0 a) (bwd i)) ∧ ZMod' A.I (gD D) (hA A.I (f0 a) (bwd i))
  ew_idem : ew * ew = ew
  ew_orth : ew * sigA A.I ew = 0
  ew_int : ew ∈ IntAf A.I.F A.I.E
  ew_full : ∀ y ∈ A.I.Lf, (1 - ew - sigA A.I ew) • y ∈ mL A.I (gD D)
  bw_w : ∀ i, bw i = ew • bw i
  bwd_w : ∀ i, bwd i = sigA A.I ew • bwd i
  bw_dual : ∀ i j, ZMod' A.I (gD D) (hA A.I (bwd i) (bw j) - if i = j then ew else 0)
  latticeSpan : ∀ y ∈ A.I.Lf,
    InMod A.I (gD D) (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

structure TransportData (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (Rf : ReferenceFrame A L) where
  xu : D.what₂.Word → A.I.Gf
  xu_fix : ∀ u a, A.I.fmat (xu u) *ᵥ incl A.I (crdOf A.I A.ιE A.bas (L.eX a)) =
      incl A.I (crdOf A.I A.ιE A.bas (L.eX a)) ∧
    A.I.fmat (xu u) *ᵥ incl A.I (crdOf A.I A.ιE A.bas (L.fY a)) = incl A.I (crdOf A.I A.ιE A.bas (L.fY a))
  xu_z : ∀ u, InAt A.I (gD D) (gD D) (A.I.fmat (xu u)⁻¹ *ᵥ incl A.I (crdOf A.I A.ιE A.bas (L.zu u)) - Rf.z0)
  xu_one : ∀ u, OneOff A.I (gD D) (xu u)
  xu_K : ∀ u, xu u ∈ A.I.Kset

def eOf (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (μf : Measure A.I.Gf) : A.I.Gf → ℂ :=
  fun x => if x ∈ K2set A.I (gD D) Rf.e0 Rf.z0 Rf.bw then
    star (chi2f A.I P.psiEf (gD D) Rf.e0 Rf.f0 Rf.z0 Rf.bw Rf.bwd x) /
      ((μf (K2set A.I (gD D) Rf.e0 Rf.z0 Rf.bw)).toReal : ℂ) else 0

def lamOf (A : UnitaryGroupInstance D) : InfinitePlace A.I.F → Fin A.I.n → ℝ :=
  fun v i => lamS D.R (D.hc (A.pl v)) (Fin.cast A.n_eq i)

structure AutomorphicBundle (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) where
  μf : Measure A.I.Gf
  [haar : μf.IsHaarMeasure]
  [sf : SigmaFinite μf]
  fund : Set A.I.GA
  fund_spec : A.I.IsFundDom (A.I.muA μf) fund
  H : InfinitePlace A.I.F → Type
  [hN : ∀ v, NormedAddCommGroup (H v)]
  [hI : ∀ v, InnerProductSpace ℂ (H v)]
  [hC : ∀ v, CompleteSpace (H v)]
  σ : ∀ v, Matrix (Fin A.I.n) (Fin A.I.n) ℂ → (H v →L[ℂ] H v)
  w : ∀ v, H v
  Hs : Type
  [sN : NormedAddCommGroup Hs]
  [sI : InnerProductSpace ℂ Hs]
  [sC : CompleteSpace Hs]
  σs : A.I.Ginf → (Hs →L[ℂ] Hs)
  tens : (∀ v, H v) → Hs
  tens_spec : A.I.IsHilbTensor σ σs tens
  R : A.I.GA → (A.I.L2 μf fund →L[ℂ] A.I.L2 μf fund)
  R_spec : A.I.IsRightReg μf fund R
  e_adm : A.I.IsAdmIdem μf (gD D) (D.host.g 0) (eOf A P Rf μf)
  Re : A.I.L2 μf fund →L[ℂ] A.I.L2 μf fund
  Re_spec : A.I.IsRConvF μf fund R (eOf A P Rf μf) Re
  ds : ∀ v, IsDS (A.I.ε v) (lamOf A v) (σ v)
  low : ∀ v, IsLowUnit (A.I.ε v) (lamOf A v) (σ v) (w v)
  Rph : A.I.L2 μf fund →L[ℂ] A.I.L2 μf fund
  Rph_spec : Formalism.L2.SG.ProjRows.IsOpInt (Formalism.L2.SG.ProjRows.muInf A.I) (fun y => R (y, 1))
    (Formalism.L2.SG.ProjRows.phInf A.I σ w fun v => fdegOf (Formalism.REAL.muG (A.I.ε v)) (σ v) (w v)) Rph
  ph_int : Integrable (Formalism.L2.SG.ProjRows.phInf A.I σ w fun v => fdegOf (Formalism.REAL.muG (A.I.ε v)) (σ v) (w v))
    (Formalism.L2.SG.ProjRows.muInf A.I)

attribute [instance] AutomorphicBundle.haar AutomorphicBundle.sf AutomorphicBundle.hN AutomorphicBundle.hI AutomorphicBundle.hC AutomorphicBundle.sN AutomorphicBundle.sI AutomorphicBundle.sC

def mkB (A : UnitaryGroupInstance D) {L : UnitaryLatticeData D} {P : AdditiveCharacterData A} {Rf : ReferenceFrame A L} (Bu : AutomorphicBundle A P Rf) : RowsAut where
  I := A.I
  μf := Bu.μf
  fund := Bu.fund
  fund_spec := Bu.fund_spec
  lam := lamOf A
  H := Bu.H
  σ := Bu.σ
  w := Bu.w
  Hs := Bu.Hs
  σs := Bu.σs
  tens := Bu.tens
  tens_spec := Bu.tens_spec
  R := Bu.R
  R_spec := Bu.R_spec
  g := gD D
  g₀ := D.host.g 0
  e := eOf A P Rf Bu.μf
  e_adm := Bu.e_adm
  Re := Bu.Re
  Re_spec := Bu.Re_spec

abbrev eC (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) : Fin D.R.rS → Fin A.I.n → A.I.E := fun a => crdOf A.I A.ιE A.bas (L.eX a)
abbrev fC (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) : Fin D.R.rS → Fin A.I.n → A.I.E := fun a => crdOf A.I A.ιE A.bas (L.fY a)
abbrev zC (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (u : D.what₂.Word) : Fin A.I.n → A.I.E := crdOf A.I A.ιE A.bas (L.zu u)

structure RepresentationData (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) where
  Vpi : D.what₂.Word → Type
  [vN : ∀ u, NormedAddCommGroup (Vpi u)]
  [vI : ∀ u, InnerProductSpace ℂ (Vpi u)]
  [vF : ∀ u, FiniteDimensional ℂ (Vpi u)]
  piU : ∀ u, A.I.Ginf → (Vpi u →L[ℂ] Vpi u)
  piU_rep : ∀ u, IsRepS A.I (Sinf A.I (eC A L) (zC A L u)) (Ninf A.I (eC A L) (zC A L u)) (piU u)
  Vloc : D.what₂.Word → InfinitePlace A.I.F → Type
  [lN : ∀ u v, NormedAddCommGroup (Vloc u v)]
  [lI : ∀ u v, InnerProductSpace ℂ (Vloc u v)]
  [lF : ∀ u v, FiniteDimensional ℂ (Vloc u v)]
  piLoc : ∀ u v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ → (Vloc u v →L[ℂ] Vloc u v)
  piLoc_type : ∀ u v, IsHCTypeU D.R.k (fun i => ((D.hcW u (A.pl v)).u i : ℝ)) (piLoc u v)
  wfr : D.what₂.Word → InfinitePlace A.I.F → Fin D.R.k → Fin A.I.n → ℂ
  wfr_on : ∀ u v a b, hJ (A.I.ε v) (wfr u v a) (wfr u v b) = if a = b then 1 else 0
  wfr_perp : ∀ u v a, (∀ c, hJ (A.I.ε v) (rv A.I v (eC A L c)) (wfr u v a) = 0 ∧
      hJ (A.I.ε v) (rv A.I v (fC A L c)) (wfr u v a) = 0) ∧
    hJ (A.I.ε v) (rv A.I v (zC A L u)) (wfr u v a) = 0
  tensU : ∀ u, (∀ v, Vloc u v) → Vpi u
  tensU_inner : ∀ u x y, ⟪tensU u x, tensU u y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ
  tensU_span : ∀ u, Submodule.span ℂ (Set.range (tensU u)) = ⊤
  tensU_equiv : ∀ u, ∀ s ∈ Hset A.I (Set.range (eC A L) ∪ Set.range (fC A L) ∪ {zC A L u}), ∀ x,
    piU u s (tensU u x) = tensU u (fun v => piLoc u v (matW A.I (wfr u v) v s) (x v))

attribute [instance] RepresentationData.vN RepresentationData.vI RepresentationData.vF RepresentationData.lN RepresentationData.lI RepresentationData.lF

structure MuBlocks (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) where
  muN : D.what₂.Word → Measure A.I.Ginf
  muH : D.what₂.Word → Measure A.I.Ginf
  muN_haar : ∀ u, IsHaarOnSet A.I (Ninf A.I (eC A L) (zC A L u)) (muN u)
  muH_haar : ∀ u, IsHaarOnSet A.I (Hset A.I (Set.range (eC A L) ∪ Set.range (fC A L) ∪ {zC A L u})) (muH u)
  nuQ : D.what₂.Word → Measure A.I.Ginf
  nuQ_weil : ∀ u, IsQuotMeasS A.I (((muN u).prod (muH u)).map (fun p => p.1 * p.2)) (nuQ u)

structure WBlk (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) {P : AdditiveCharacterData A} {Rf : ReferenceFrame A L} (Bu : AutomorphicBundle A P Rf)
    (Pi : RepresentationData A L) (Mu : MuBlocks A L) where
  Wu : ∀ u, A.I.Ginf → Pi.Vpi u
  Wu_spec : ∀ u, IsWu A.I
    (Formalism.L2.SG.ProjRows.phInf A.I Bu.σ Bu.w fun v => fdegOf (Formalism.REAL.muG (A.I.ε v)) (Bu.σ v) (Bu.w v))
    (Sinf A.I (eC A L) (zC A L u)) (psiInf A.I (gD D) (eC A L) (fC A L) (zC A L u)) (Pi.piU u) (Mu.nuQ u) (Wu u)
  Wloc : ∀ u v, Formalism.REAL.UJ (A.I.ε v) → Pi.Vloc u v
  Wloc_cont : ∀ u v, Continuous (Wloc u v)
  Wu_tens : ∀ u x, Wu u x = Pi.tensU u (fun v => Wloc u v (x v))

structure MBlk (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) where
  measG : Formalism.L2.SG.Measures.MeasG A.I.cm.sig A.I.J D.R.rS
  measG_norm : measG.IsTextNorm
  measW : ∀ u, Formalism.L2.SG.Measures.MeasW A.I.cm.sig A.I.J
    (⟨eC A L, fC A L, zC A L u⟩ : Formalism.L2.SG.Sub.Frame A.I.E A.I.n D.R.rS)
  measW_norm : ∀ u, (measW u).IsTextNorm

def mk (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (Xu : TransportData A L Rf)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L) (Wb : WBlk A L Bu Pi Mu) (Mb : MBlk A L) :
    HidaSetting D where
  B := mkB A Bu
  ιE := A.ιE
  ιE_conj := A.ιE_conj
  ιE_F := A.ιE_F
  bas := A.bas
  J_eq := A.J_eq
  L_eq := A.L_eq
  pl := A.pl
  φ_eq := A.φ_eq
  n_eq := A.n_eq
  eps_eq := A.eps_eq
  lam_eq := fun _ _ => rfl
  ds := Bu.ds
  low := Bu.low
  g_eq := rfl
  g0_eq := rfl
  Rph := Bu.Rph
  Rph_spec := Bu.Rph_spec
  eX := L.eX
  fY := L.fY
  ee := L.ee
  ff := L.ff
  ef := L.ef
  Lb := L.Lb
  Lb_perp := L.Lb_perp
  Lam_split := L.Lam_split
  zu := L.zu
  zu_norm := L.zu_norm
  zu_orth := L.zu_orth
  zu_Lb := L.zu_Lb
  Fu := L.Fu
  Fu_e := L.Fu_e
  flagZVector := L.flagZVector
  Fu_fixed := L.Fu_fixed
  psiEf := P.psiEf
  psiEf_add := P.psiEf_add
  psiEf_int := P.psiEf_int
  psiEf_rat := P.psiEf_rat
  e0 := Rf.e0
  f0 := Rf.f0
  z0 := Rf.z0
  bw := Rf.bw
  bwd := Rf.bwd
  ew := Rf.ew
  vectorsInLattice := Rf.vectorsInLattice
  basisApprox := Rf.basisApprox
  gramIntegral := Rf.gramIntegral
  formsAtZero := Rf.formsAtZero
  weightVectorsIntegral := Rf.weightVectorsIntegral
  ew_idem := Rf.ew_idem
  ew_orth := Rf.ew_orth
  ew_int := Rf.ew_int
  ew_full := Rf.ew_full
  bw_w := Rf.bw_w
  bwd_w := Rf.bwd_w
  bw_dual := Rf.bw_dual
  latticeSpan := Rf.latticeSpan
  e_eq := fun _ => rfl
  xu := Xu.xu
  xu_fix := Xu.xu_fix
  xu_z := Xu.xu_z
  xu_one := Xu.xu_one
  xu_K := Xu.xu_K
  Vpi := Pi.Vpi
  vN := Pi.vN
  vI := Pi.vI
  vF := Pi.vF
  piU := Pi.piU
  piU_rep := Pi.piU_rep
  Vloc := Pi.Vloc
  lN := Pi.lN
  lI := Pi.lI
  lF := Pi.lF
  piLoc := Pi.piLoc
  piLoc_type := Pi.piLoc_type
  wfr := Pi.wfr
  wfr_on := Pi.wfr_on
  wfr_perp := Pi.wfr_perp
  tensU := Pi.tensU
  tensU_inner := Pi.tensU_inner
  tensU_span := Pi.tensU_span
  tensU_equiv := Pi.tensU_equiv
  muN := Mu.muN
  muH := Mu.muH
  muN_haar := Mu.muN_haar
  muH_haar := Mu.muH_haar
  nuQ := Mu.nuQ
  nuQ_weil := Mu.nuQ_weil
  Wu := Wb.Wu
  Wu_spec := Wb.Wu_spec
  Wloc := Wb.Wloc
  Wloc_cont := Wb.Wloc_cont
  Wu_tens := Wb.Wu_tens
  measG := Mb.measG
  measG_norm := Mb.measG_norm
  measW := Mb.measW
  measW_norm := Mb.measW_norm

end Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.SplitPrimeNormLemmas

open Formalism.L2.SG.ConcreteSettingExists

def CoefWeightedLoc : Prop :=
  ∀ (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ),
    Formalism.QuantumDeterminants.IsHCParam (Formalism.MainNotions.CayleySignature.lam48 k r v b) → Formalism.MainNotions.CayleySignature.GapBig k r b →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
      Formalism.MainNotions.S.IsDS (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ →
      ∀ w : H, Formalism.MainNotions.S.IsLowUnit (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) σ w →
        ∫⁻ g, ‖⟪w, σ (Formalism.MainNotions.S.uMat g) w⟫_ℂ‖ₑ *
            ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Formalism.MainNotions.S.uMat g)‖ ^
              (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))))
          ∂(Formalism.REAL.muG (Formalism.MainNotions.CayleySignature.eps48 k r)) < ⊤

variable (D : D7)

def InstExists : Prop := Nonempty (UnitaryGroupInstance D)

def LatExists : Prop := Nonempty (UnitaryLatticeData D)

def PsiExists : Prop := ∀ A : UnitaryGroupInstance D, Nonempty (AdditiveCharacterData A)

def RefExists : Prop := ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D), Nonempty (ReferenceFrame A L)

def XuExists : Prop := ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (Rf : ReferenceFrame A L), Nonempty (TransportData A L Rf)

def BunExists : Prop :=
  CoefWeightedLoc → GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L), Nonempty (AutomorphicBundle A P Rf)

def PiExists : Prop := ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D), Nonempty (RepresentationData A L)

def MuExists : Prop := ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D), Nonempty (MuBlocks A L)

def WExists : Prop :=
  GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (Xu : TransportData A L Rf)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L),
    ∃ Wb : WBlk A L Bu Pi Mu, ∀ Mb : MBlk A L, Formalism.L2.SG.WuDecay.WuDecay (mk A L P Rf Xu Bu Pi Mu Wb Mb)

def MExists : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L) (Xu : TransportData A L Rf)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L) (Wb : WBlk A L Bu Pi Mu),
    ∃ Mb : MBlk A L, ∃ hb : Formalism.L2.SG.AdBridge.AdBridgeIso A.I,
      (mk A L P Rf Xu Bu Pi Mu Wb Mb).MeasTie hb

theorem settingExists_of_steps (hC : CoefWeightedLoc) (h1 : InstExists D) (h2 : LatExists D) (h3 : PsiExists D)
    (h4 : RefExists D) (h5 : XuExists D) (h6 : BunExists D) (h7 : PiExists D) (h8 : MuExists D)
    (h9 : WExists D) (h10 : MExists D) : ConcreteSettingExists D := by
  intro hG
  obtain ⟨A⟩ := h1
  obtain ⟨L⟩ := h2
  obtain ⟨P⟩ := h3 A
  obtain ⟨Rf⟩ := h4 A L
  obtain ⟨Xu⟩ := h5 A L Rf
  obtain ⟨Bu⟩ := h6 hC hG A L P Rf
  obtain ⟨Pi⟩ := h7 A L
  obtain ⟨Mu⟩ := h8 A L
  obtain ⟨Wb, hW⟩ := h9 hG A L P Rf Xu Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := h10 A L P Rf Xu Bu Pi Mu Wb
  exact ⟨mk A L P Rf Xu Bu Pi Mu Wb Mb, hb, hM, hW Mb, Bu.ph_int⟩

end Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.SplitPrimeNormLemmas

def StrongApproxSU : Prop :=
  ∀ I : AutInst, 2 ≤ I.n → (∃ v i j, I.ε v i = true ∧ I.ε v j = false) →
    ∀ U : Set I.Gf, IsOpen U → ∀ x ∈ U, (I.fmat x).det = 1 →
      ∃ γ : Formalism.UG.UJ (I.cm.sig : I.E →+* I.E) I.J,
        ((γ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).det = 1 ∧
          Formalism.L2.SG.ColsDim.ratHom I.cm.sig I.J (Af I.F) γ ∈ U

def HCReprodDS : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ w ∈ lowKSub ε lam σ, ∀ U ∈ nhds (1 : Formalism.REAL.UJ ε),
      ∃ α : Formalism.REAL.UJ ε → ℂ, Continuous α ∧ HasCompactSupport α ∧ Function.support α ⊆ U ∧
        Integrable (fun g => α g • σ (uMat g) w) (Formalism.REAL.muG ε) ∧
        ∫ g, α g • σ (uMat g) w ∂(Formalism.REAL.muG ε) = w

end Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.SplitPrimeNormLemmas

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

def BesselNVGap : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ),
    2 ≤ k → Even k → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
    Formalism.QuantumDeterminants.IsHCParam u → Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) → InterlacingCondition k r u v b →
    HalfIntegralDifference k r u v b → GapBig k r b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μW μN : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r), IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
  ∃ x x₀ : Mat k r, x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN) ≠ 0

def nuH (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : ℝ :=
  ⨅ t : Formalism.QuantumDeterminants.Sset k r z, Formalism.L2.SG.WuDecay.opn ((t : Mat k r) * x)

def N1H (k r : ℕ) : ℝ := 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))

def WlocExists : Prop :=
  BesselNVGap → CoefWeightedLoc → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ W : Mat k r → Vp, ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ∧ IsSPsiEquiv z (psiGen k r z c) π W ∧
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ ∂ν < ⊤ ∧ l2SG ν W = 1 ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ * ENNReal.ofReal (nuH k r z (Matrix.of x) ^ N1H k r) ∂ν < ⊤ ∧
    ∃ (α : Mat k r → ℂ) (Ω : Set (Mat k r)) (a : ℝ), IsCompact Ω ∧ (1 : Mat k r) ∈ Ω ∧
      Ω ⊆ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Measurable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g)) ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g) • W (x * Matrix.of g)) μG ∧
        rconv μG α W x = W x

def GapBigOfGapHyp (D : D7) : Prop :=
  ∀ hm : D.R.m = 2 * D.R.rS + 2, Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ τ : D.what₂.Tau,
    GapBig D.R.k D.R.rS (fun j => ((D.hc τ).b (Fin.cast hm.symm j) : ℝ))

def WFromLoc (D : D7) : Prop := BesselNVGap → CoefWeightedLoc → WlocExists → GapBigOfGapHyp D → WExists D

theorem wExists_of_loc (D : D7) (hF : WFromLoc D) (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hG : GapBigOfGapHyp D) : WExists D :=
  hF hB hC hW hG

theorem settingExists_of_inputs (D : D7) (hB : BesselNVGap) (hC : CoefWeightedLoc) (hW : WlocExists)
    (hG : GapBigOfGapHyp D) (hF : WFromLoc D) (h1 : InstExists D) (h2 : LatExists D) (h3 : PsiExists D)
    (h4 : RefExists D) (h5 : XuExists D) (h6 : BunExists D) (h7 : PiExists D) (h8 : MuExists D)
    (h10 : MExists D) : Formalism.L2.SG.ConcreteSettingExists.ConcreteSettingExists D :=
  settingExists_of_steps D hC h1 h2 h3 h4 h5 h6 h7 h8 (wExists_of_loc D hF hB hC hW hG) h10

end Formalism.L2.SG.SplitPrimeNormLemmas
