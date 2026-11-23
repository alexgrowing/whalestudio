import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.LevSplitAt

set_option maxHeartbeats 4000000

theorem lev_split_at : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J),
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l := by
  intro X px I hX U Xg tr L hI hV hL cV i t x j hj
  classical
  set L' := L.datVt i t with hL'
  set P : Formalism.L2.DIV.Pl X.toD7.host.E := (x.1.1.1 : Formalism.L2.DIV.Pl X.toD7.host.E) with hPdef
  have hoffP : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  obtain ⟨hPc, hPn, hPq⟩ := hoffP

  obtain ⟨c, hβ⟩ := hL.is.βV i
  rw [one_pow] at hβ

  have hPg : ∀ PP ∈ (flag1L L').Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Pg = L.Pg from rfl, hL.Pg] at hPP
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L L').Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    exact Finset.mem_union.2 (Or.inr hPP)
  have hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hm : PP ∈ sgL X I U t := hPP.elim (hPg PP) (hQ PP)
    refine ⟨fun e => hPn ?_, fun hc => hPq PP ?_ ?_⟩
    · subst e; simp [hm]
    · simp [hm]
    · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]

  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hPc
  have hpi : IsPrimeIdem P e (e + cA X.toD7 e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Vc X.toD7 i)).2.2.1 P e _ hpi
  have hff := h01.1
  have hcf := h01.2.1
  have h1 : ((1 : ℕ) : 𝓞 X.toD7.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  obtain ⟨-, -, hsp⟩ := (GlobalTheory.LevSplit.lev_split (Vc X.toD7 i) (L.βV i) (L.ΛV i) 1 (flag1L L') hβ).2 P e _ hpi h1 hoff
  obtain ⟨g, hg, hgj⟩ := GlobalTheory.SplitHeckeAdj.fin_lift (Vc X.toD7 i) j
  have hj' : GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) g ∈ (levEnv (Vc X.toD7 i) (L.βV i) L').J := by rw [hgj]; exact hj
  obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩ := hsp g ((GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' hg).1 hj')
  refine ⟨GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₁, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₁.1).2 h₁,
    GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₂, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩,
    by rw [← hgj, hk, map_mul], ?_⟩
  intro l hl
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp (Vc X.toD7 i) hl he
  exact (GlobalTheory.SplitHeckeAdj.commute_compl (Vc X.toD7 i) _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i))

end GlobalTheory.Mem.R3.LiftBrg.LevSplitAt
