import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.LocalToGlobal.Columns.ChainTw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv

open Classical in

theorem stepRep_eq_one_at_typePrimes {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 j : ℕ)
    (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    (twSt Ch sel mu cst m2 j).h b P = 1 := by
  cases j with
  | zero => rfl
  | succ i =>
    by_cases h1 : i + 1 ≤ m2
    · revert b
      rw [show twSt Ch sel mu cst m2 (i+1) = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) by simp [twSt, h1]]
      intro b
      have hq : P.1 ∉ twQOff (Pr := Pr) sel mu := fun hq => (Finset.mem_sdiff.1 hq).2 hP
      simp only [twNext, hq, dif_neg, not_false_eq_true]
    · by_cases h2 : i + 1 = m2 + 1
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twUnitSt _ (i+1) by simp [twSt, h1, h2]]
        intro b; rfl
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twEmptySt _ (i+1) by simp only [twSt, if_neg h1, if_neg h2]]
        intro b; exact b.elim

theorem colNorm_of_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), (∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧ I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)) → GlobalTheory.Pdv.ColNorm I := by
  intro B X I H a
  obtain ⟨hc, hi⟩ := H a
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; show B.R.m ≤ B.R.m + 1; omega
  · rw [hc]; show B.R.m ≤ B.R.m; exact le_rfl
  · rw [hi]
    intro j _ b P hP
    exact stepRep_eq_one_at_typePrimes _ _ _ _ _ _ b P hP

end GlobalTheory.Pdv
