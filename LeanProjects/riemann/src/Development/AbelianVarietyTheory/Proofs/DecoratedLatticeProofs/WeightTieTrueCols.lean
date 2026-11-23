import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTieRec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem weightTie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), DelNat (I.rec7 l Z) → ∀ u : B.Word, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (numDatumOfParameters (I.rec7 l Z) L) (X := B.fields) (Pr := B.primes X) B.wts (plRec (I.rec7 l Z)) u (codeRec L u) := by
  intro B X I _ l Z L hD u
  obtain ⟨n, hn⟩ := hD
  have hfl : ((⌊(I.rec7 l Z).s.Del⌋₊ : ℕ) : ℚ) = (I.rec7 l Z).s.Del := by rw [hn, Nat.floor_natCast]
  refine ⟨B.wts_isOk, fun z => ?_, fun z => ⟨?_, fun i => ?_⟩⟩
  · exact GlobalTheory.ColumnNormCompare.mem_tops_rec (I.rec7 l Z) z
  · exact B.wts_isOk.hc_row u _
  · change ((I.rec7 l Z).hcW u (plRec (I.rec7 l Z) z)).u i = _
    unfold NumDatum.uW
    obtain ⟨i, hi⟩ := i
    have hi' : i < (I.rec7 l Z).R.k := hi
    by_cases h : 1 ≤ i ∧ i + 1 < (I.rec7 l Z).R.k
    · rw [dif_pos h]
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk : k < (I.rec7 l Z).R.k - 2 := by omega
      have a := (I.rec7 l Z).s.u_letter u (plRec (I.rec7 l Z) z) k hk
      have hv := (I.rec7 l Z).hcW_v u (plRec (I.rec7 l Z) z)
      rw [a, hv, ← hfl]
      rfl
    · rw [dif_neg h]
      by_cases h0 : i = 0
      · subst h0
        exact (I.rec7 l Z).hcW_first u _ hi'
      · have h1 : i = (I.rec7 l Z).R.k - 1 := by omega
        subst h1
        exact (I.rec7 l Z).hcW_last u _ (by omega)

end GlobalTheory.CoreHt
