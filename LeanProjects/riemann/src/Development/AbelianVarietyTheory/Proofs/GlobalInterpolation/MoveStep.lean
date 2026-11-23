import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsRecordDat
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OffOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BadPrimeNormPrimeNeLevelPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DecoratedLatticePointMoveDiamond
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SameOfAbove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UkTermOfMoveStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2
open _root_.Formalism.L2.Col

local instance starHost (B : Base) : StarRing B.host.E := B.fields.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev dat (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) : Dat (I.rec7 l Z) u :=
  Inh.ofOk B (I.cols l) Z.W Z.V Z.S Z.N Z.G u (I.chIn u a) (I.atIn u a) (I.perIn u a) (I.fmIn l.pr u a) (l.ch u a) (l.lev u a)
    (l.per u a) (l.ovr u a)

instance datFE (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Bd : Dat (I.rec7 l Z) u) : Field Bd.E := Bd.fE

instance datNE (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Bd : Dat (I.rec7 l Z) u) : NumberField Bd.E := Bd.nE

instance datSE (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Bd : Dat (I.rec7 l Z) u) : StarRing Bd.E := Bd.sE

theorem dat_ch (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (dat I l Z u a).ch = tw (I.tw l l0 Z) u a := rfl

theorem own_eq (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    own (I.rec7 l Z) u = tw (I.tw l l0 Z) u I.mu0 := rfl

example (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) : (dat I l Z u a).Ker i :=
  kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i

variable {I}

theorem isTerm (h : I.Ok) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    KerIsTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  exact IsTerm.kerIsTerm B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr h.sel_ok
    (h.T_mem u) (h.idx_ok a) hi h.ch_ok h.g_mem ⟨_, _, _, _, h.ch_tied⟩ I.A

theorem kerDil (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    Dat.KerDil (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro b b' d d' P c
  exact kAt_dia B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr h.sel_ok (h.T_mem u)
    (h.idx_ok a) (I.Tp a) I.A (isTerm h u a hi) b b' d d' P c

theorem split (u : B.Word) (a : I.ι) (h : I.Ok) (i : ℕ) :
    Nonempty (Split ((I.atIn u a).A i) (B.T u)) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨sp, -⟩ := SplitPts.exists_split B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr
    h.sel_ok (h.T_mem u) (h.idx_ok a) (I.Tp a)
  exact ⟨⟨sp.off, sp.off_act, sp.off_lat, sp.ext, sp.surj, sp.off_up, sp.off_dn, sp.off_dia, sp.dia_deco, sp.gam_surj, sp.T_mem,
    sp.T_nsq, sp.nonconj⟩⟩

open Classical in
theorem sees (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) : (dat I l Z u a).Sees :=
  Inh.sees_ofOk B (I.cols l) Z.W Z.V Z.S Z.N Z.G u X (I.chIn u a) (I.atIn u a) (I.perIn u a) (I.fmIn l.pr u a) (l.ch u a)
    (l.lev u a) (l.per u a) (l.ovr u a) rfl (fun _ h => h) (fun _ _ => rfl) (fun _ => decide_eq_true_iff)

theorem kerEq (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (hth : _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)))
    {i : ℕ} (hi : i < B.R.m)
    (hk : ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1)
      (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c)
        (((dat I l Z u a).I.S (i + 1)).rep c') F)) :
    Dat.KerEq (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  refine ⟨fun b b' g g' d d' => ?_, hk⟩
  rcases lt_trichotomy (i + 2) B.R.m with h1 | h1 | h1
  · exact MatLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth h1 b b' g g' d d'
  · exact CoupledLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth h1 b b' g g' d d'
  · exact TopEq.kAt_top_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth (by omega) b b' g g' d d'

end GlobalTheory.LvT.Built.TrueLaws
