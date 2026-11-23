import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum

noncomputable section

open NumberField

namespace UpperTheory.ConvolutionTheory.BW.Dat

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n : ℕ}

def On (d : Dat S n) (Λ : (E →+* ℂ) → Multiset ℂ) (t : Pl E → Multiset ℂ) : Prop :=
  ∃ z, Λ = msOf (d.ptL z) ∧ ∀ w ∉ S, t w = d.ptS z w

def blo : {n : ℕ} → (d : Dat S n) → Fin d.len → Σ r, Blo S r
  | _, nil => fun j => j.elim0
  | _, cons b d => fun j => Fin.cases (motive := fun _ => Σ r, Blo S r) ⟨_, b⟩ d.blo (j : Fin (d.len + 1))

end UpperTheory.ConvolutionTheory.BW.Dat
