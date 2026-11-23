import Formalism.LocalToGlobal.Columns.ChainTwMain
import Formalism.LocalToGlobal.Columns.WithTopLevGTop

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwTop

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ)

open Classical

def twIdxTop (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) :
    ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)) :=
  (twIdx Ch sel mu cst m2).withTop m2 Λt Θt

variable {Ch sel mu cst m2}

theorem twSt_subsingleton (hE : twQOff (Pr := Pr) sel mu = ∅) : ∀ j (b b' : (twSt Ch sel mu cst m2 j).β), b = b'
  | 0, _, _ => rfl
  | i + 1, b, b' => by
      revert b b'
      by_cases h1 : i + 1 ≤ m2
      · rw [twSt_succ_le Ch sel mu cst h1]
        intro b b'
        apply Subtype.ext
        funext P
        exact absurd (show P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 X.E))) from hE ▸ P.2) (Finset.notMem_empty _)
      · by_cases h2 : i + 1 = m2 + 1
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twUnitSt _ (i + 1) by rw [twSt, if_neg h1, if_pos h2]]
          intro _ _; rfl
        · rw [show twSt Ch sel mu cst m2 (i + 1) = twEmptySt _ (i + 1) by rw [twSt, if_neg h1, if_neg h2]]
          intro b; exact b.elim

variable (Ch sel mu cst) in

def TwChrRoot : Prop :=
  ∀ (j : ℕ) (P : rowSG Pr sel mu) (h r : AutY X R j), r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h →
    ∃ n : ℕ, 0 < n ∧ chiInv Ch sel mu cst j P h r ^ n = 1

end TwTop

end Formalism.L2.Col
