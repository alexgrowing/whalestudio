import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.DivMv

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

open DivX (md) in

def divBack (X : DivX (GlobalTheory.EX.OB.setDiv D N h)) : DivX D := { X with md := fun S κ p _ la z => { md X S κ p la z with } }

theorem idxDefs_fwd {X : DivX (GlobalTheory.EX.OB.setDiv D N h)} (H : IdxDefs D (divBack N h X)) : IdxDefs (GlobalTheory.EX.OB.setDiv D N h) X :=
  ⟨(by with_unfolding_all exact (H.Ij_def :)), (by with_unfolding_all exact (H.jw_def :))⟩

end Gen

section Amb

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {X : RowSide D EE}

abbrev JAT (A : FamIn D.what₂.LL G Pl0 T D.R.m) (X : RowSide D EE) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) (μ : D.what₂.Tup) :
    Type := (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb μ

def AmbW (A : FamIn D.what₂.LL G Pl0 T D.R.m) (X : RowSide D EE) (a : AmbForm D X) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (tup : T → D.what₂.Tup) (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) : Prop :=
  ∃ J, AmbTie D A X a P ψ tup jA J

theorem AmbW.congr {a : AmbForm D X} {P : Subgroup G} {ψ : P →* D.what₂.LLˣ} {tup : T → D.what₂.Tup}
    {jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)} (H : AmbW A X a P ψ tup jA)
    (tup' : T → D.what₂.Tup) (e : tup' = tup)
    (jA' : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup' t)) (ej : HEq jA' jA) : AmbW A X a P ψ tup' jA' := by
  subst e
  obtain rfl := eq_of_heq ej
  exact H

theorem sameOn_congr {K τ ι : Type} {n : τ → ℕ} {m : ι → ℕ} {V : τ → Type} (j : ∀ μ, (Fin (n μ) → K) → V μ) {tup tup' : ι → τ}
    (e : tup' = tup) {k : ∀ s, (Fin (m s) → K) → V (tup s)} {k' : ∀ s, (Fin (m s) → K) → V (tup' s)} (ek : HEq k' k)
    (H : ∀ s, SameOn (j (tup s)) (k s)) (s : ι) : SameOn (j (tup' s)) (k' s) := by
  subst e
  obtain rfl := eq_of_heq ek
  exact H s

theorem heq_map {τ ι : Type} {P Q : ι → τ → Type} (φ : ∀ s μ, P s μ → Q s μ) {tup tup' : ι → τ} (e : tup' = tup)
    {k : ∀ s, P s (tup s)} {k' : ∀ s, P s (tup' s)} (ek : HEq k' k) :
    HEq (fun s => φ s (tup' s) (k' s)) fun s => φ s (tup s) (k s) := by
  subst e
  obtain rfl := eq_of_heq ek
  exact HEq.rfl

end Amb

section Mj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

abbrev JwT (F : Face3 D A3) (X : Cx.CxData A3.fam3.amb3) : Type :=
  ∀ i : Fin D.R.m, (Fin ((X.data F.cr false).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)

def MjW (F : Face3 D A3) (Xd : DivX D) (X : Cx.CxData A3.fam3.amb3) (jW : JwT F X) : Prop :=
  ∃ J : MjHIds D A3.A Xd (A3.indefDown (P := F.P0) (ψ := F.ψ0) (Zs := X.zs) (X.data F.cr false)),
    MjHTie D A3.A Xd (A3.indefDown (P := F.P0) (ψ := F.ψ0) (Zs := X.zs) (X.data F.cr false)) jW J

theorem MjW.congr {F : Face3 D A3} {Xd : DivX D} {X X' : Cx.CxData A3.fam3.amb3} (e : X = X') {jW : JwT F X} {jW' : JwT F X'}
    (ej : HEq jW' jW) : MjW F Xd X jW ↔ MjW F Xd X' jW' := by
  subst e
  obtain rfl := eq_of_heq ej
  exact Iff.rfl

end Mj

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

def sameG : SameGrp (B := B) (C := w.C) Z (Db.setDivZ Z N h) :=
  SameGrp.ofN Z.N Z.V (Db.setDivZ Z N h).V Z.S Z.S Z.G Z.G

def datMv {hX : B.fields.Ok} (z : Dat (w.st Z) w.I hX T Wt) : Dat (w.st (Db.setDivZ Z N h)) w.I hX T Wt :=
  (by with_unfolding_all exact ((Mv.cpDat (a := Z) (Db.setDivZ Z N h) (sameG N h) z) :))

def p0Mv (p0 : BaseLevelRowSide (w.D Z)) : BaseLevelRowSide (w.D (Db.setDivZ Z N h)) := (by with_unfolding_all exact ((⟨GlobalTheory.EX.OB.sideTr N h p0.s⟩ : BaseLevelRowSide (GlobalTheory.EX.OB.setDiv (w.D Z) N h)) :))

theorem datMv_cG {hX : B.fields.Ok} (z : Dat (w.st Z) w.I hX T Wt) : HEq (datMv N h z).cG z.cG := (by with_unfolding_all exact ((HEq.refl z.cG) :))

section Ties

variable {hX : B.fields.Ok} (z : Dat (w.st Z) w.I hX T Wt)

def cxMv : Cx.CxData (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.amb3 :=
  (by with_unfolding_all exact (((datMv N h z).R.toCx3 (datMv N h z).F) :))

theorem cxMv_eq : z.R.toCx3 z.F = cxMv N h z := (by with_unfolding_all exact ((toCx3_eq (a := Z) (Db.setDivZ Z N h) (iK := z.alg) z.R z.F) :))

set_option maxHeartbeats 2000000 in

theorem mjW_fwd {X : DivX (w.D Z)} {jW : JwT z.F (cxMv N h z)} (H : MjW z.F X (cxMv N h z) jW) :
    MjW (datMv N h z).F ((@EX.OB.divTr (@ColW.D B f T w Z) N h X)) ((datMv N h z).R.toCx3 (datMv N h z).F) ((jW)) := by
  obtain ⟨J, HJ⟩ := H
  exact ⟨⟨(by with_unfolding_all exact (J.eW :))⟩, ⟨(by with_unfolding_all exact (HJ.j_eq :)), (by with_unfolding_all exact (HJ.hlat :))⟩⟩

set_option maxHeartbeats 2000000 in

theorem mjW_back {X : DivX (w.D (Db.setDivZ Z N h))} {jW : JwT (datMv N h z).F ((datMv N h z).R.toCx3 (datMv N h z).F)}
    (H : MjW (datMv N h z).F X ((datMv N h z).R.toCx3 (datMv N h z).F) jW) :
    MjW z.F ((@divBack (@ColW.D B f T w Z) N h X)) (cxMv N h z) ((jW)) := by
  obtain ⟨J, HJ⟩ := H
  exact ⟨⟨(by with_unfolding_all exact (J.eW :))⟩, ⟨(by with_unfolding_all exact (HJ.j_eq :)), (by with_unfolding_all exact (HJ.hlat :))⟩⟩

end Ties

section Rows

variable {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0)

structure ReadSame (Y : Read (datMv N h t.r.z).R.toRealDat (datMv N h t.r.z).F.lv2 ((by exact p0Mv N h p0)))
    (L : ReadL (datMv N h t.r.z).R (datMv N h t.r.z).F ((by exact p0Mv N h p0)) Y) : Prop where
  tup : HEq Y.tup t.r.Y.tup
  tupT : HEq Y.tupT t.r.Y.tupT
  PY : HEq Y.PY.ψ t.r.Y.PY.ψ
  PW : HEq (fun i => (Y.PW i).ψ) fun i => (t.r.Y.PW i).ψ
  rep : HEq (fun π => principalLevelFrame.rowRepR (datMv N h t.r.z).R.θ (Y.eFT π)) fun π => principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT π)
  jE : HEq (fun x => (Y.Ish.jE x).1) fun x => (t.r.Y.Ish.jE x).1
  heq_eigen_embedding_zero : HEq (fun x => (Y.Iz.jE x).1) fun x => (t.r.Y.Iz.jE x).1
  eE : HEq Y.eE t.r.Y.eE
  jA : HEq Y.jA t.r.Y.jA
  jA0 : HEq Y.jA0 t.r.Y.jA0
  eMt : HEq Y.eMt t.r.Y.eMt
  eW : HEq Y.mj.eW t.r.Y.mj.eW
  jW : HEq L.jW t.r.Z.jW
  eRR : HEq L.eRR t.r.Z.eRR
  eRR0 : HEq L.eRR0 t.r.Z.eRR0

variable {N h t} {Y : Read (datMv N h t.r.z).R.toRealDat (datMv N h t.r.z).F.lv2 ((by with_unfolding_all exact ((p0Mv N h p0) :)))}
    {L : ReadL (datMv N h t.r.z).R (datMv N h t.r.z).F ((by with_unfolding_all exact ((p0Mv N h p0) :))) Y}

theorem ReadSame.tup_eq (s : ReadSame N h t Y L) : ((by exact Y.tup) : type_of% t.r.Y.tup) = t.r.Y.tup := eq_of_heq ((by exact s.tup))

set_option maxHeartbeats 2000000 in

theorem ReadSame.mj_back (s : ReadSame N h t Y L) {X : DivX (w.D (Db.setDivZ Z N h))} (H : MjAre L ((X))) :
    MjAre t.r.Z ((@divBack (@ColW.D B f T w Z) N h X)) :=
  (by with_unfolding_all exact (((MjW.congr (F := t.r.z.F) (Xd := ((divBack (D := w.D Z) N h ((by with_unfolding_all exact (X :)))))) (cxMv_eq N h t.r.z) (jW := (t.r.Z.jW))
    (jW' := (L.jW)) ((s.jW))).2
    (((mjW_back N h t.r.z (X := X) (jW := (by with_unfolding_all exact (L.jW :))) ((by with_unfolding_all exact (H :))))))) : _))

set_option maxHeartbeats 2000000 in

theorem ReadSame.mj_fwd (s : ReadSame N h t Y L) {X : DivX (w.D Z)} (H : MjAre t.r.Z ((X))) :
    MjAre L ((@EX.OB.divTr (@ColW.D B f T w Z) N h X)) :=
  (by with_unfolding_all exact ((mjW_fwd N h t.r.z (X := X) (jW := (L.jW))
    ((MjW.congr (cxMv_eq N h t.r.z) (jW := (t.r.Z.jW)) (jW' := (L.jW)) ((s.jW))).1 ((H)))) : _))

set_option maxHeartbeats 2000000 in

def ReadSame.rowsAre (s : ReadSame N h t Y L) :
    R3.RowsAre (w.st (Db.setDivZ Z N h)) w.I t.hX T Wt (Equiv.refl _) (p0Mv N h p0) where
  z := datMv N h t.r.z
  intersectionNumber_baseChange := (by with_unfolding_all exact ((Mv.cp_holds (a := Z) (Db.setDivZ Z N h) (sameG N h) t.r.z t.r.intersectionNumber_baseChange) :))
  Y := (by with_unfolding_all exact (Y :))
  Z := (by with_unfolding_all exact (L :))
  tup_ix u := (by with_unfolding_all exact (((congrFun s.tup_eq u).trans (t.r.tup_ix u)) :))

set_option maxHeartbeats 2000000 in

def ReadSame.what₂ (s : ReadSame N h t Y L) : RowsT K w (Db.setDivZ Z N h) Wt (p0Mv N h p0) where
  hX := t.hX
  r := s.rowsAre
  exAt := (by with_unfolding_all exact ((Mv.cp_exAt (a := Z) (Db.setDivZ Z N h) (sameG N h) t.r.z t.exAt) :))
  inGeo := (by with_unfolding_all exact ((Mv.cp_inGeo (a := Z) (Db.setDivZ Z N h) (sameG N h) t.r.z t.inGeo) :))
  grpAt := ⟨(by with_unfolding_all exact (t.grpAt.pl :)), (by with_unfolding_all exact (t.grpAt.idem :)), (by with_unfolding_all exact (t.grpAt.cen :))⟩
  grp := t.grp
  mu := ⟨t.mu.inj, t.mu.range, t.mu.mu0, t.mu.star, t.mu.star', t.mu.tw, t.mu.on, t.mu.off, t.mu.sub, t.mu.supp⟩
  exact := (by with_unfolding_all exact ((t.exact.trans (Mv.forcedContentPlaces_eq_transport_sameFiniteGroup (a := Z) (Db.setDivZ Z N h) (sameG N h) t.r.z (((F0K K.s (w.D Z))))).symm) : _))
  untw := (by with_unfolding_all exact (t.untw :))
  emt0 := (by with_unfolding_all exact (t.emt0 :))
  emt := (by with_unfolding_all exact (t.emt :))
  etaF := (by with_unfolding_all exact (t.etaF :))
  rowInt := ⟨(by with_unfolding_all exact (t.rowInt.ref :)), (by with_unfolding_all exact (t.rowInt.tw :))⟩
  idx X H := (by with_unfolding_all exact ((idxDefs_fwd (D := w.D Z) N h (X := (X)) (((t.idx _ (s.mj_back (X := (by with_unfolding_all exact (X :))) ((by with_unfolding_all exact (H :)))))))) : _))

set_option maxHeartbeats 2000000 in

theorem ReadSame.rowsSame (s : ReadSame N h t Y L) : RowsSame t s.what₂ where
  Xg := rfl
  tr := rfl
  core := (by with_unfolding_all exact ((HEq.refl (datMv N h t.r.z).core) :))
  R := (by with_unfolding_all exact ((HEq.refl (datMv N h t.r.z).R) :))
  cG := (by with_unfolding_all exact ((datMv_cG N h t.r.z) :))
  tup := (by with_unfolding_all exact (s.tup :))
  tupT := (by with_unfolding_all exact (s.tupT :))
  PY := (by with_unfolding_all exact (s.PY :))
  PW := (by with_unfolding_all exact (s.PW :))
  rep := (by with_unfolding_all exact (s.rep :))
  jE := (by with_unfolding_all exact (s.jE :))
  heq_eigen_embedding_zero := (by with_unfolding_all exact (s.heq_eigen_embedding_zero :))
  eE := (by with_unfolding_all exact (s.eE :))
  jA := (by with_unfolding_all exact (s.jA :))
  jA0 := (by with_unfolding_all exact (s.jA0 :))
  eMt := (by with_unfolding_all exact (s.eMt :))
  eW := (by with_unfolding_all exact (s.eW :))
  jW := (by with_unfolding_all exact (s.jW :))
  eRR := (by with_unfolding_all exact (s.eRR :))
  eRR0 := (by with_unfolding_all exact (s.eRR0 :))

set_option maxHeartbeats 2000000 in

theorem ReadSame.pk (s : ReadSame N h t Y L) : HEq (SRe.pkOf s.what₂) ((SRe.pkOf t).up Z Z.S N h) := by
  have e : ((by with_unfolding_all exact (Y.eE :)) : type_of% t.r.Y.eE) = t.r.Y.eE := eq_of_heq ((by with_unfolding_all exact (s.eE :)))
  exact (by with_unfolding_all exact ((heq_of_eq (congrArg (fun E : type_of% t.r.Y.eE =>
    SRe.RowPk.up Z Z.S N h { SRe.pkOf t with eE := E }) e)) :))

set_option maxHeartbeats 2000000 in

theorem ReadSame.amb1 (s : ReadSame N h t Y L) {a : AmbForm (w.D Z) (RowSide.sharp (w.D Z))}
    (a' : AmbForm (w.D (Db.setDivZ Z N h)) (RowSide.sharp (w.D (Db.setDivZ Z N h)))) (e1 : a'.MtH = (a.MtH))
    (e2 : HEq a'.jAmb a.jAmb)
    (H : AmbW (D := (w.st Z).toD7) (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A _ a t.r.z.F.P1 t.r.z.F.ψ1
      t.r.Y.tup t.r.Y.jA) :
    AmbW (D := (w.st (Db.setDivZ Z N h)).toD7) (famR (w.st (Db.setDivZ Z N h)) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A _ a'
      ((by exact t.r.z.F.P1)) ((by exact t.r.z.F.ψ1)) ((by exact Y.tup)) ((by exact Y.jA)) := by
  obtain ⟨M, j, a1, a2, a3, a4, a5⟩ := a'
  dsimp only at e1 e2
  subst e1
  have e : ((by with_unfolding_all exact (a.jAmb :))) = j := eq_of_heq ((by with_unfolding_all exact (e2.symm :)))
  subst e
  obtain ⟨J, HJ⟩ := AmbW.congr H ((by with_unfolding_all exact (Y.tup :))) ((by with_unfolding_all exact (s.tup_eq :))) ((by with_unfolding_all exact (Y.jA :))) ((by with_unfolding_all exact (s.jA :)))
  exact ⟨⟨(by with_unfolding_all exact (J.eA :))⟩, ⟨(by with_unfolding_all exact (HJ.j_eq :)), (by with_unfolding_all exact (HJ.lat :)), (by with_unfolding_all exact (HJ.metric :))⟩⟩

set_option maxHeartbeats 2000000 in

theorem ReadSame.amb0 (s : ReadSame N h t Y L) {a : AmbForm (w.D Z) p0.s}
    (a' : AmbForm (w.D (Db.setDivZ Z N h)) (p0Mv N h p0).s) (e1 : a'.MtH = (a.MtH))
    (e2 : HEq a'.jAmb a.jAmb)
    (H : AmbW (D := (w.st Z).toD7) (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A _ a t.r.z.F.P0 t.r.z.F.ψ0
      t.r.Y.tup t.r.Y.jA0) :
    AmbW (D := (w.st (Db.setDivZ Z N h)).toD7) (famR (w.st (Db.setDivZ Z N h)) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A _ a'
      ((by exact t.r.z.F.P0)) ((by exact t.r.z.F.ψ0)) ((by exact Y.tup)) ((by exact Y.jA0)) := by
  obtain ⟨M, j, a1, a2, a3, a4, a5⟩ := a'
  dsimp only at e1 e2
  subst e1
  have e : ((by with_unfolding_all exact (a.jAmb :))) = j := eq_of_heq ((by with_unfolding_all exact (e2.symm :)))
  subst e
  obtain ⟨J, HJ⟩ := AmbW.congr H ((by with_unfolding_all exact (Y.tup :))) ((by with_unfolding_all exact (s.tup_eq :))) ((by with_unfolding_all exact (Y.jA0 :))) ((by with_unfolding_all exact (s.jA0 :)))
  exact ⟨⟨(by with_unfolding_all exact (J.eA :))⟩, ⟨(by with_unfolding_all exact (HJ.j_eq :)), (by with_unfolding_all exact (HJ.lat :)), (by with_unfolding_all exact (HJ.metric :))⟩⟩

variable (N h t) in
set_option maxHeartbeats 2000000 in

def allMv (x : RXs t) :
    AllT (w.st (Db.setDivZ Z N h)).toD7 (famR (w.st (Db.setDivZ Z N h)) w.I t.hX Set.univ t.r.z.Xg t.r.z.tr).A (lev0 w.I) (chr0 w.I)
      (lev1 w.I) (chr1 w.I) (p0Mv N h p0) (tAll w.I) (((datMv N h t.r.z).R.eG.trans (datMv N h t.r.z).cG)) where
  jA := (by with_unfolding_all exact (x.all.jA :))
  jA0 := (by with_unfolding_all exact (x.all.jA0 :))
  eMt := (by with_unfolding_all exact (x.all.eMt :))
  formsA := (by with_unfolding_all exact (x.all.formsA :))
  latA := (by with_unfolding_all exact (x.all.latA :))
  formsAtBottomLevel := (by with_unfolding_all exact (x.all.formsAtBottomLevel :))
  latA0 := (by with_unfolding_all exact (x.all.latA0 :))
  formsL := (by with_unfolding_all exact (x.all.formsL :))
  latL := (by with_unfolding_all exact (x.all.latL :))
  cen := (by with_unfolding_all exact (x.all.cen :))

set_option maxHeartbeats 2000000 in

theorem ReadSame.jA_use (s : ReadSame N h t Y L) (x : RXs t) (u) :
    SameOn (x.all.jA (((by exact Y.tup) : type_of% t.r.Y.tup) u)) (((by exact Y.jA) : ∀ u, (Fin (rDim (w.st Z).toD7
      (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A t.r.z.F.P1 t.r.z.F.ψ1 u) → (w.st Z).toD7.what₂.LL) →ₛₗ[(w.st Z).toD7.what₂.embLL]
        (w.st Z).toD7.what₂.Amb (((by exact Y.tup) : type_of% t.r.Y.tup) u)) u) :=
  sameOn_congr (fun μ => x.all.jA μ) s.tup_eq (k := fun u => t.r.Y.jA u)
    (heq_map (P := fun u μ => (Fin (rDim (w.st Z).toD7
      (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A t.r.z.F.P1 t.r.z.F.ψ1 u) → (w.st Z).toD7.what₂.LL) →ₛₗ[(w.st Z).toD7.what₂.embLL]
        (w.st Z).toD7.what₂.Amb μ) (fun _ _ j => (j : _ → _)) s.tup_eq ((by with_unfolding_all exact (s.jA :)))) x.jA_use u

set_option maxHeartbeats 2000000 in

theorem ReadSame.movedReadingSameMaps_baseReading_agrees (s : ReadSame N h t Y L) (x : RXs t) (u) :
    SameOn (x.all.jA0 (((by exact Y.tup) : type_of% t.r.Y.tup) u)) (((by exact Y.jA0) : ∀ u, JAT (D := (w.st Z).toD7)
      (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A p0.s t.r.z.F.P0 t.r.z.F.ψ0 u (((by exact Y.tup) : type_of% t.r.Y.tup) u)) u) :=
  sameOn_congr (fun μ => x.all.jA0 μ) s.tup_eq (k := fun u => t.r.Y.jA0 u)
    (heq_map (P := fun u μ => JAT (D := (w.st Z).toD7)
      (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A p0.s t.r.z.F.P0 t.r.z.F.ψ0 u μ) (fun _ _ j => (j : _ → _)) s.tup_eq ((by with_unfolding_all exact (s.jA0 :)))) x.movedReadingSameMaps_baseReading_agrees u

abbrev EMtT (t : RowsT K w Z Wt p0) (i : Fin (w.st Z).toD7.R.m) (u : TupU w.I (usedOf w.I T Wt)) (μ : (w.st Z).toD7.what₂.Tup) : Type :=
  (Fin (lDim (w.st Z).toD7 (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A t.r.z.F.P0 t.r.z.F.ψ0 i u) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL]
    (w.st Z).toD7.what₂.MtL μ ((i : ℕ) + 1)

theorem eMt_heq (t : RowsT K w Z Wt p0) {tup tup' : TupU w.I (usedOf w.I T Wt) → (w.st Z).toD7.what₂.Tup} (e : tup' = tup)
    {k : ∀ i u, EMtT t i u (tup u)} {k' : ∀ i u, EMtT t i u (tup' u)} (ek : HEq k' k) (i) : HEq (k' i) (k i) := by
  subst e
  obtain rfl := eq_of_heq ek
  exact HEq.rfl

set_option maxHeartbeats 2000000 in

theorem ReadSame.eMt_use (s : ReadSame N h t Y L) (x : RXs t) (i : Fin (w.st Z).toD7.R.m) (u) :
    SameOn (x.all.eMt i (((by exact Y.tup) : type_of% t.r.Y.tup) u))
      (((by exact Y.eMt) : ∀ i u, EMtT t i u (((by exact Y.tup) : type_of% t.r.Y.tup) u)) i u) :=
  sameOn_congr (fun μ => x.all.eMt i μ) s.tup_eq (k := fun u => t.r.Y.eMt i u)
    (heq_map (P := fun u μ => EMtT t i u μ) (fun _ _ j => (j : _ → _)) s.tup_eq
      (eMt_heq t s.tup_eq (k := t.r.Y.eMt) (k' := (by with_unfolding_all exact (Y.eMt :))) ((by with_unfolding_all exact (s.eMt :))) i)) (x.eMt_use i) u

set_option maxHeartbeats 4000000 in

def ReadSame.rxs (s : ReadSame N h t Y L) (x : RXs t) : RXs s.what₂ where
  all := (by with_unfolding_all exact ((allMv N h t x) :))
  jA_use := (by with_unfolding_all exact ((s.jA_use x) :))
  movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact ((s.movedReadingSameMaps_baseReading_agrees x) :))
  eMt_use := (by with_unfolding_all exact ((s.eMt_use x) :))
  e := (by with_unfolding_all exact (x.e :))
  eMt0 := (by with_unfolding_all exact (x.eMt0 :))
  eMtTw := (by with_unfolding_all exact (x.eMtTw :))
  crd := (by with_unfolding_all exact (x.crd :))
  io := (by with_unfolding_all exact (x.io :))
  sha := (by with_unfolding_all exact (x.sha :))
  laws := (by with_unfolding_all exact ((Mv.lawsCore_tr (a := Z) (Db.setDivZ Z N h) x.laws) :))
  canon := (by with_unfolding_all exact (x.canon :))
  rank := (by with_unfolding_all exact (x.rank :))
  pb := (by with_unfolding_all exact (x.pb :))
  std := kc% x.std

end Rows

set_option maxHeartbeats 4000000 in

theorem ReadSame.objT {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ} {O : Obj2 (w.D Z)} {t : RowsT K w Z Wt O.p0}
    {Y : Read (datMv N h t.r.z).R.toRealDat (datMv N h t.r.z).F.lv2 ((p0Mv N h O.p0))}
    {L : ReadL (datMv N h t.r.z).R (datMv N h t.r.z).F ((p0Mv N h O.p0)) Y} (s : ReadSame N h t Y L) (H : ObjT O t) :
    ObjT (Z := Db.setDivZ Z N h) (Wt := Wt) (K := K) (O.tr N h) ((by with_unfolding_all exact (s.what₂ :))) where
  amb := (by with_unfolding_all exact ((And.intro (s.amb1 (a := O.amb) (((O.tr N h).amb)) (((Eq.refl O.amb.MtH))) (((HEq.refl O.amb.jAmb))) ((H.amb.1)))
    (s.amb0 (a := O.amb0) (((O.tr N h).amb0)) (((Eq.refl O.amb0.MtH))) (((HEq.refl O.amb0.jAmb))) ((H.amb.2)))) : _))
  mjH := (by with_unfolding_all exact ((s.mj_fwd (X := O.X) ((H.mjH))) : _))
  kapR σ := (by with_unfolding_all exact (((H.kapR σ).trans (GlobalTheory.EX.OB.kapSharp_tr (D := w.D Z) N h).symm) :))

set_option maxHeartbeats 4000000 in

theorem rows_move_of_read (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (O' : Obj2 (w.D (Db.setDivZ Z N h))) (hO : O' = O.tr N h) (hs : ∃ Y L, ReadSame N h t Y L) :
    ∃ t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0, RowsSame t t' ∧ HEq (SRe.pkOf t') ((SRe.pkOf t).up Z Z.S N h) ∧
      (ObjT O t → ObjT O' t') ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  subst hO
  obtain ⟨Y, L, s⟩ := hs
  exact ⟨(by with_unfolding_all exact (s.what₂ :)), (by with_unfolding_all exact (s.rowsSame :)), (by with_unfolding_all exact (s.pk :)), fun H => (by with_unfolding_all exact ((s.objT H) :)), fun ⟨x⟩ => ⟨(by with_unfolding_all exact ((s.rxs x) :))⟩⟩

end GlobalTheory.Mem.R3.Rw.DivMv

end
