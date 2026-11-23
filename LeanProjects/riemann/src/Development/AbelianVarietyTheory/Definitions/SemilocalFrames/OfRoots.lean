import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open scoped Classical

namespace GlobalTheory.LoopV

open NumberField Matrix Formalism.MainNotions.S

variable {K : Type} [Field K] {N : ℕ}

def StrUp (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, j ≤ i → x i j = 0

def StrLo (x : Matrix (Fin N) (Fin N) K) : Prop := ∀ i j, i ≤ j → x i j = 0

def expT (x : Matrix (Fin N) (Fin N) K) : Matrix (Fin N) (Fin N) K :=
  ∑ i ∈ Finset.range N, ((i.factorial : K)⁻¹) • x ^ i

def stabU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {a | IsUpUni a ∧ IsLoUni (Z * a * Z⁻¹)}

def lieU (Z : Matrix (Fin N) (Fin N) K) : Set (Matrix (Fin N) (Fin N) K) :=
  {x | StrUp x ∧ StrLo (Z * x * Z.adjugate)}

def roots (w : Matrix (Fin N) (Fin N) K) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ ∃ i j, j < i ∧ w i q.1 ≠ 0 ∧ w j q.2 ≠ 0

def ofRoots (R : Finset (Fin N × Fin N)) (c : R → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if h : (i, j) ∈ R then c ⟨(i, j), h⟩ else if i = j then 1 else 0

def EntIn [NumberField K] (I : Ideal (𝓞 K)) (x : Matrix (Fin N) (Fin N) K) : Prop :=
  ∀ i j, ∃ o ∈ I, ((o : 𝓞 K) : K) = x i j

end GlobalTheory.LoopV

end
