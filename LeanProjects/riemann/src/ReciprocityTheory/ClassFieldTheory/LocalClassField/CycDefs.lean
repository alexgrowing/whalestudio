import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Polynomial

noncomputable section

variable (p : ℕ) [Fact p.Prime]

abbrev Q0 : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥

def Lk (k : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {z : PadicAlgCl p | z ^ (p ^ k) = 1}

variable {p}

def cycH (g : GK p (Q0 p)) (η : PadicAlgCl p) (c n : ℕ) : (PadicAlgCl p)[X] :=
  ∑ j ∈ Finset.range n, C ((g ^ j) η) * ∑ i ∈ Finset.range (c ^ j), X ^ i

def cycY (g : GK p (Q0 p)) (η z : PadicAlgCl p) (c n : ℕ) : PadicAlgCl p :=
  ∑ j ∈ Finset.range n, (g ^ j) η * (z ^ (c ^ j) - 1)

def normQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : Kˣ) : PadicAlgCl p :=
  ((Additive.toMul (normHom p (Q0 p) K (ofK p K (Additive.ofMul a))) : (PadicAlgCl p)ˣ) : PadicAlgCl p)

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
