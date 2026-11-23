import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeParahoricEntriesEqColumnDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.Join

section
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)

theorem xiAt_eq_prod (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1))
    (x : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))) :
    xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) x =
      Formalism.L2.Col.phiT B.fields.K (A.p0 i α).1.1.deco.1 (A.p0 (i + 1) γ).1.1.deco.1 x *
        ∏ P : BadPr I a, locXi A i α γ P x := by
  rcases lt_trichotomy (i + 2) B.R.m with h | h | h
  · rw [xiAt, dif_pos h]
    unfold Formalism.L2.Col.XiEntry
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locXi, dif_pos h]
  · rw [xiAt, dif_neg (by omega), dif_pos h]
    unfold Formalism.L2.Col.XiCpl1
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locXi, dif_neg (by omega), dif_pos h]
  · have h1 : i + 1 = B.R.m := by omega
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := B.R.two_le_m; omega⟩
    rw [xiAt, dif_neg (by omega), dif_neg (by omega), dif_pos h1]
    show xiOver _ _ _ _ n h1 _ _ _ x = _
    unfold xiOver
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [locXi, dif_neg (by omega), dif_neg (by omega), dif_pos h1]
    rfl

theorem xi_eq_xiOff_mul (i : ℕ) (hi : i + 1 ≤ B.R.m) (α : Ch₀ i) (γ : Ch₀ (i + 1))
    (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) :
    A.xi i hi α γ z = xiOff A i hi α γ z *
      ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∉ (B.primes X).vGs), B.embLL (locXi A i α γ P (homOf I l Z i hi z)) := by
  unfold TwDat.xi xiOff
  refine (congrArg B.embLL (xiAt_eq_prod A i hi α γ (homOf I l Z i hi z))).trans ?_
  rw [map_mul, map_mul, map_prod, map_prod, mul_assoc, Finset.prod_filter_mul_prod_filter_not]

theorem entry_eq_sgn_mul (hI : I.Ok) : ∀ (c : Comm (I.rec7 l Z)) (v : VCom c) (Bs : GlobalTheory.Fam.Base c) PP (G : QGeo v Bs PP) χ (E : QExt G χ) hψ sg π (P : BadPr I a), ReadsAt A P E hψ sg π → ∀ j d (H : j + 1 + d = G.s) (hj : j + 1 ≤ B.R.m) (hj' : j + 1 < B.R.m) α γ (e' : XIx (Fin B.R.k) (Fin B.R.t) j ≃ Fin (B.R.N j)) (e : XIx (Fin B.R.k) (Fin B.R.t) (j + 1) ≃ Fin (B.R.N (j + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ x, (G.T E.δ E.tame E.η).entry G.ψk G.ν j d H (E.rep j (d + 1) (by omega) (π j α)) (E.rep (j + 1) d H (π (j + 1) γ)) (GlobalTheory.SymBridge.toLoc (G.q.pr.comp (incA (I.rec7 l Z))) e e' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)) = GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h j ((A.b0 j α).get hj) P) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) * GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h (j + 1) ((A.b0 (j + 1) γ).get hj') P) (B.R.N j + Formalism.L2.Col.cOf B.R j) * B.embLL (locXi A j α γ P x) := by
  intro c v Bs PP G χ E hψ sg π P hR j d H hj hj' α γ e' e he' he x
  have hAt := hR.tw
  have hs : G.s = B.R.m - 2 := by have := hAt.steps; omega
  have hL : (I.idx a).Ok I.Ch I.sel (I.tup a) (I.cst a) I.glob G.s := by rw [hs]; exact hI.idx_ok a
  have hEA := GlobalTheory.T.twistPrime_parahoricEntries_eq_columnData B.fields (B.primes X) B.R I.Ch I.sel _ (I.tup a) (I.cst a) B.embLL P G.k
    (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg) G.ν G.unitVol (hI.idx_ok a).cst_ok hAt (I.idx a) I.glob hL
  have h2 := hEA j d H ((A.b0 j α).get hj) ((A.b0 (j + 1) γ).get hj') _ _ (hR.rep j (d + 1) (by omega) hj α)
    (hR.rep (j + 1) d H hj' γ) e' e he' he
    (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)
  have hlt : j + 2 < B.R.m := by have := hAt.steps; omega
  simp only [locXi, dif_pos hlt]
  exact h2

end

theorem xi_factor_and_entry : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → (∀ i (hi : i + 1 ≤ B.R.m) α γ z, A.xi i hi α γ z = xiOff A i hi α γ z * ∏ P ∈ Finset.univ.filter (fun P : BadPr I a => P.1 ∉ (B.primes X).vGs), B.embLL (locXi A i α γ P (homOf I l Z i hi z))) ∧ ∀ (c : Comm (I.rec7 l Z)) (hX : c.X = (I.rec7 l Z).sp.X) (v : VCom c) (Bs : GlobalTheory.Fam.Base c) PP (G : QGeo v Bs PP) χ (E : QExt G χ) hψ sg π (P : BadPr I a), ReadsAt A P E hψ sg π → ∀ j d (H : j + 1 + d = G.s) (hj : j + 1 ≤ B.R.m) (hj' : j + 1 < B.R.m) α γ (e' : XIx (Fin B.R.k) (Fin B.R.t) j ≃ Fin (B.R.N j)) (e : XIx (Fin B.R.k) (Fin B.R.t) (j + 1) ≃ Fin (B.R.N (j + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ x, (G.T E.δ E.tame E.η).entry G.ψk G.ν j d H (E.rep j (d + 1) (by omega) (π j α)) (E.rep (j + 1) d H (π (j + 1) γ)) (GlobalTheory.SymBridge.toLoc (G.q.pr.comp (incA (I.rec7 l Z))) e e' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 j α).1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 (j + 1) γ).1.1 P) x)) = GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h j ((A.b0 j α).get hj) P) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) * GlobalTheory.TwBridge.sgn I.sel (I.tup a) P (E.tw hψ sg) ((I.idx a).h (j + 1) ((A.b0 (j + 1) γ).get hj') P) (B.R.N j + Formalism.L2.Col.cOf B.R j) * B.embLL (locXi A j α γ P x) :=
  fun _ hI _ _ _ _ _ _ A _ => ⟨xi_eq_xiOff_mul A, fun c _ => entry_eq_sgn_mul A hI c⟩

end GlobalTheory.QTw.Join
