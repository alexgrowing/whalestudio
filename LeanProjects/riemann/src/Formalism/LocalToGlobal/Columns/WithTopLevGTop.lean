import Formalism.LocalToGlobal.Columns.RecChainYUnfPol

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def ChIdx.withTop (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q) : ChIdx X Pr R Q where
  β j := {b : Option (L.β j) // b.isSome = decide (j ≤ m2 + 1)}
  h j b P := match b.1 with
    | some b' => L.h j b' P
    | none => 1
  levG j b := match b.1 with
    | some b' => L.levG j b'
    | none => Λt j
  levQ j b := match b.1 with
    | some b' => L.levQ j b'
    | none => Θt j

variable (L : ChIdx X Pr R Q) (m2 : ℕ) (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) Q)

def ChIdx.low {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j) : (L.withTop m2 Λt Θt).β j := ⟨some b, by simp [hj]⟩

def ChIdx.top {j : ℕ} (hj : m2 + 1 < j) : (L.withTop m2 Λt Θt).β j := ⟨none, by simp [Nat.not_le.2 hj]⟩

theorem ChIdx.exists_low {j : ℕ} (hj : j ≤ m2 + 1) (b : (L.withTop m2 Λt Θt).β j) : ∃ b', b = ChIdx.low L m2 Λt Θt hj b' := by
  obtain ⟨b, hb⟩ := b
  cases b with
  | none => simp [hj] at hb
  | some b' => exact ⟨b', rfl⟩

end Top

end Formalism.L2.Col
