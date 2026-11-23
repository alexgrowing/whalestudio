import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg

theorem nV_pos (X : Stages) : 0 < X.B.R.nV := by
  have h := X.B.R.m_add_three_le_k
  unfold Ranks.nV Ranks.r
  omega

instance nV_neZero (X : Stages) : NeZero X.B.R.nV := ⟨(nV_pos X).ne'⟩

theorem rkEq (X : Stages) (i : Fin X.toD7.R.m) : X.B.R.nV = (Vc X.toD7 i).rank :=
  (X.toD7.sp.V_rank _ (by omega) i.2).symm

def castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) : GL (Fin m) R ≃* GL (Fin n) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finCongr h)).toRingEquiv.toMulEquiv

abbrev EA (X : Stages) : Type := X.toD7.host.E ⊗[X.toD7.host.F] Formalism.L2.Herm.Af X.toD7.host.F

abbrev envL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) :=
  Bridge.envOf (cV i).coef (levEnvOf (Vc X.toD7 i) (L.βV i) (L.datVt i t) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E))
    ((famR X I hX U Xg tr).A.ok t))

abbrev PresL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) : Type :=
  Bridge.ClassPres (Bridge.ratF (Vc X.toD7 i)) ((famR X I hX U Xg tr).A.MtCSD i t) X.toD7.what₂.embLL
    (envL X I hX U Xg tr L cV i t).coef.ρ (envL X I hX U Xg tr L cV i t).lev.J (envL X I hX U Xg tr L cV i t).lev.χ

abbrev sgL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (t : TupU I U) :
    Finset (Pl X.toD7.host.E) :=
  Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1

def FrameOK (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) : Prop :=
  (∃ A0 : GL (Fin X.B.R.nV) X.toD7.host.E, A = Formalism.UG.bc (Formalism.L2.Col.iA X.toD7.host.F X.toD7.host.E) A0) ∧
    A ∈ Formalism.L2.DIV.St 1 ∧
    (∀ x : GL (Fin X.B.R.nV) (EA X), x ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ↔
      castGL (rkEq X i) (A * x * A⁻¹) ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram) ∧
    k ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ∧ k ∈ Formalism.L2.DIV.St 1 ∧
    ∀ PP ∈ sgL X I U t, A * k ∈ Formalism.L2.DIV.princAt 1 PP

def ptL (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (U : Set I.ι) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (g : Bridge.Gf (Vc X.toD7 i)) :
    Formalism.L2.Col.DecoSet X.toD7.host.E X.B.R.nV ∅ (sgL X I U t) :=
  Formalism.L2.Col.decoOf ∅ (sgL X I U t)
    (A⁻¹ * castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin (Vc X.toD7 i).rank) _)) * A * k)

def ReadsStd (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X))
    (P : PresL X I hX U Xg tr L cV i t) : Prop :=
  ∀ (f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) (g : Bridge.Gf (Vc X.toD7 i)),
    P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) g =
      P.coef ((((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f).1 (ptL X I U i t A k g))

end GlobalTheory.Mem.R3.LiftBrg
