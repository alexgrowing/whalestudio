import Mathlib
import Formalism.LocalToGlobal.Divisibility.ColPins
import Formalism.LocalToGlobal.NumberFieldFamilies.EvRowSurjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationDatumOkBaseTuple

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev cstT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) : LocCst B.fields (rowSG (B.primes X) I.sel τ) :=
  twCst I.Ch I.sel τ I.glob

abbrev idxT (τ : Tup B.fields.F B.fields.E B.fields.K I.S) :
    ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) :=
  twIdx I.Ch I.sel τ (cstT I τ) (B.R.m - 2)

variable {I}

theorem cstT_tup (ht : I.IsTw) (a : I.ι) : cstT I (I.tup a) = I.cst a := (ht.cst_eq a).symm

theorem idxT_tup (ht : I.IsTw) (a : I.ι) : idxT I (I.tup a) = I.idx a := (ht.idx_eq a).symm

theorem of_forall_ix (ht : I.IsTw) {U : Set I.ι}
    (p : ∀ τ : Tup B.fields.F B.fields.E B.fields.K I.S, LocCst B.fields (rowSG (B.primes X) I.sel τ) →
      ChIdx B.fields (B.primes X) B.R (QE I.sel (τ : Chr B.fields.F B.fields.E B.fields.K)) → Prop)
    (hp : ∀ a, p (I.tup a) (I.cst a) (I.idx a)) (t : TupU I U) : p t.1 (cstT I t.1) (idxT I t.1) := by
  rw [← tup_ixOf I t, cstT_tup ht, idxT_tup ht]
  exact hp _

theorem idxT_ok (h : I.Ok) (ht : I.IsTw) {U : Set I.ι} (t : TupU I U) :
    (idxT I t.1).Ok I.Ch I.sel t.1 (cstT I t.1) I.glob (B.R.m - 2) :=
  of_forall_ix ht (fun τ c L => L.Ok I.Ch I.sel τ c I.glob (B.R.m - 2)) h.idx_ok t

variable (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞)
  (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)

def colRecC : ColRec3 B.fields (famC I hX U Xg tr) (lev1 I) (chr1 I) where
  Pr := B.primes X
  Rk := B.R
  W := B.wts
  Ch := I.Ch
  sel := I.sel
  Sg := I.S
  hX := hX
  Lv := rPsymF (R := B.R) I.Ch
  Xg := Xg
  m2 := B.R.m - 2
  Gc := I.glob
  mu := fun t => t.1
  cst := fun t => cstT I t.1
  Li := fun t => idxT I t.1
  hL := fun t => idxT_ok h ht t
  hP := fun t => mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel t.1 hX _
  Mem := B.Word
  wd := fun u => u
  b := fun t _ => (idxT_ok h ht t).last_uniq.choose
  hY := fun t u => coupling_index_set_finite (Pr := B.primes X) I.sel t.1 (cstT I t.1) (idxT I t.1) u (B.R.m - 2) _
  Am := I.J.amb B χ
  hK := fun t u => of_forall_ix ht
    (fun τ c L => ∀ b hY, KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel τ c L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).2.2.2) t _ _
  hF := fun t u => of_forall_ix ht (fun τ _ L => ∀ j, (chF (Pr := B.primes X) B.wts I.sel τ L u j).Ok)
    (fun a => (RcHyp.hyps_of_isTw I h hp l Z ht hJ χ hχ a u).1) t
  hE := fun u => by
    have e := RcHyp.evaluationDatum_ok_baseTuple I u
    rw [I.trueColumn_tuple_trivial_eq_one] at e
    exact e
  ev := evC (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
    (rPsymF (R := B.R) I.Ch)

theorem colRecC_ev_bijective (Zs : DefSub (famC I hX U Xg tr).fam3.amb3) (t : TupU I U) :
    Function.Bijective ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).ev Zs t) :=
  evC_bijective (X := B.fields) (Pr := B.primes X) B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr
    (rPsymF (R := B.R) I.Ch) Zs t

theorem fieldsLL_eq : fieldsLL (I.rec7 l Z) B.fields B.tauLL = B.fields := rfl

end GlobalTheory.Mem.R3.SelC

end
