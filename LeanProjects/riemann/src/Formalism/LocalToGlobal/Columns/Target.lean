import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.TiedBack
import Formalism.LocalToGlobal.Columns.ColumnDeterminants.ColsTiedD
import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.Columns.RecLevel
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.GlobalTheory.WindowConstantGeSixteen

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

structure ColJoint (c : ColRec) (C : ColObj c.what₂.LL c.what₂.Word) where
  isoF : ∀ u, Formalism.L2.GlobalTheoryTheory.HLatOps.Iso ((c.fm u).lat 0) (C.Mf u)
  ram : ∀ u, ((c.fm u).ramSub).map (isoF u).e.toLinearMap = LinearMap.range (C.incl u)
  T_eq : ∀ u, (c.mem u).A.T = C.T u
  f_eq : C.f = c.R.f
  k_eq : C.k = c.R.k
  m_eq : C.m = c.R.m
  Dstar_eq : ∀ u, (c.mem u).A.Dstar = C.Dstar

  duStar_eq : ∀ u, ((c.mem u).A.duStar : ℝ) = C.dstar u

def ColObj.onRec (D : D7) {c : ColRec} (h : D.colRec = c) (C : ColObj c.what₂.LL c.what₂.Word) : ColObj D.what₂.LL D.what₂.Word := by
  subst h
  exact C

def ColJoint.onRec (D : D7) {c : ColRec} (h : D.colRec = c) {C : ColObj c.what₂.LL c.what₂.Word} (J : ColJoint c C) :
    ColJoint D.colRec (ColObj.onRec D h C) := by
  subst h
  exact J

structure ColObj.InclOk {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I) : Prop where
  inj : ∀ u, Function.Injective (C.incl u)
  norm : ∀ u v (x : (C.M u).V),
    Formalism.HermitianLatticesTheory.normAt (C.M u).b (C.M u).X v x = Formalism.HermitianLatticesTheory.normAt (C.Mf u).b (C.Mf u).X v (C.incl u x)
  L : ∀ u, (C.M u).L = (C.Mf u).L.comap ((C.incl u).restrictScalars (𝓞 K))

def NuTie (D : D7) (C : ColObj D.what₂.LL D.what₂.Word) (J : ColJoint D.colRec C) : Prop :=
  ∀ u, (D.div.Nu u).L.map ((((J.isoF u).e.toLinearMap).comp (D.nuIn u)).restrictScalars (𝓞 D.what₂.LL)) =
    (C.Npr u).map ((C.incl u).restrictScalars (𝓞 D.what₂.LL))

def DstarTie (d : ColDat) (A : ColArg (Pr := d.Pr) d.W d.Ch) : Prop := d.num.Dstar = (colObj d.W d.Ch d.hX A).Dstar

set_option maxHeartbeats 1000000 in

def concObj (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) : ColObj (d.colRec a).what₂.LL (d.colRec a).what₂.Word :=
  colObj d.W d.Ch d.hX A

def RecJointOf : Prop :=
  ∀ (D : D7) (C : ColObj D.what₂.LL D.what₂.Word) (J : ColJoint D.colRec C), C.InclOk → NuTie D C J → Nonempty (C.RecJoint D)

def ColJointExists : Prop :=
  ∀ (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch), DstarTie d A → 2 * d.X.f * d.R.k < d.Pr.g 0 - 1 →
    d.lev 0 = colLev d.Ch 0 →
    Nonempty (ColJoint (d.colRec a) (concObj d a A))

section Ker

open Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))

theorem twistPrimes_trivialTuple_empty_target : QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime (1 : Chr X.F X.E X.K) = ∅ := by
    ext v
    simp [Qprime]
  show QE sel (1 : Chr X.F X.E X.K) = ∅
  unfold QE
  rw [dif_pos (by rw [h]; exact Set.finite_empty)]
  simp [h]

theorem target_not_mem_qe (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∉ QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) := by
  rw [twistPrimes_trivialTuple_empty_target]
  exact Finset.notMem_empty P

def targetLift {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet X.E n ST SG) :
    DecoF X.E n ST SG (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) :=
  ⟨(p, fun _ => 1), fun P _ => (target_not_mem_qe sel P.1 P.2).elim⟩

def targetCastN {n n' : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (h : n = n') (p : DecoSet X.E n ST SG) :
    DecoSet X.E n' ST SG := h ▸ p

end Ker

section KerRef

open Formalism.L2.Ker Formalism.MainNotions

variable {d : ColDat} (a : ColArgs d) {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 d.X.F) → HeightOneSpectrum (𝓞 d.X.E))

structure KerAmbTied (D : D7) (X : Fields) (σ₀ : X.K →+* ℂ) where
  cc : Ideal (𝓞 D.host.K)
  cc_rec : cc = D.host.ccK
  cc_ok : TaylorLogMetric.IsCurveIdeal D cc
  δ : ℂ
  δ_ok : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ
  B : Base D cc δ
  B_std : B.StdOK
  χ : TaylorLogMetric.IdE D → ℂ
  χ_ok : TaylorLogMetric.IsChi D χ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  idl_ok : TaylorLogMetric.RelDetPinned D idl
  χ_rec : χ = TaylorLogMetric.chiRec D idl
  cD : D.what₂.Tau → ℂ
  cD_ok : IsDgen D cD
  seam : Seam D X
  seam_ok : seam.Ok
  seam_σ : seam.σ₀ = σ₀

def KerAmbTied.amb {D : D7} {X : Fields} {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) : Amb X := ambOf K.seam K.B K.χ K.cD

end KerRef

section Target

open Formalism.L2.GlobalTheoryTheory.ColOpen Formalism.L2.Ker

set_option maxHeartbeats 400000 in

def ColumnsAgreeAt (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) (D : D7) (h : D.colRec = d.colRec a) : Prop :=
  V1.ColHyp d → Nonempty (Formalism.L2.Forms.ColsTied D) ∧
    (Dat.Ok { R := d.R, X := d.X, sig0 := d.σ₀, Pr := d.Pr, Ch := d.Ch, W := d.W, a := A.num.sc.a } →
    Formalism.HermitianLatticesTheory.IsCMUnram d.X.E → MassRatioStd → d.X.f ≤ d.R.k →
    ∀ {Δ : ℝ} {c : d.X.Tau → ℝ} {code : d.Pr.Word → ℕ → ℕ}, Grid (Pr := d.Pr) d.W Δ A.num.Sc c code →
    Ends (Pr := d.Pr) d.W A.num.sc.a A.num.sc.b' A.num.Sc →
    Nodes (Pr := d.Pr) d.W A.num.sc.x A.num.sc.L A.num.eta A.num.Sc → Nums5 d.X d.Pr d.R A.num → NumsZ d.X d.R A.num (logAvC d.X A.num) →
    (∀ u, InWindow d.W d.Ch A.dsig d.num.GamP u) →
    (∀ u, MaxSlopeSummandWithConstant d.W d.Ch u A.num.C0) → ColArgOk d.W d.Ch A →
    ∃ I : ColIface (d.colRec a).what₂.LL (d.colRec a).what₂.Word, I.toColObj = concObj d a A ∧
      ∀ (J : ColJoint D.colRec (ColObj.onRec D h (concObj d a A))), NuTie D (ColObj.onRec D h (concObj d a A)) J →
        Nonempty ((ColObj.onRec D h I.toColObj).RecJoint D) ∧
        ∀ u, ((D.mem u).A.duStar : ℝ) = (ColObj.onRec D h I.toColObj).dstar u ∧
          (D.mem u).A.Xu = (ColObj.onRec D h I.toColObj).Xu u)

def ColumnsAgreeConcrete : Prop :=
  ∀ (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) (D : D7) (h : D.colRec = d.colRec a), ColumnsAgreeAt d a A D h

end Target

end Formalism.L2.Col
