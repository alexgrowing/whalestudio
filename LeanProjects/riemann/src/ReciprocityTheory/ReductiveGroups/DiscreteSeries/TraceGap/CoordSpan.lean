import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemHighestWeightSubIff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def gaW (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam - rhoC ε + rhoHol ε

section General

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def kFinSub (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Submodule ℂ M :=
  ⨆ (S : Submodule ℂ M) (_ : FiniteDimensional ℂ S ∧ IsKStableSub ε E S), S

end General

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def coordSpan (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))) : Submodule ℂ M :=
  Submodule.span ℂ {v | ∃ (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)), y ∈ Z ∧ v = tco s y}

def lineSub (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (W : Submodule ℂ M) :
    Submodule ℂ (TensorProduct ℂ M (Fock n)) :=
  khwSub ε (diagE ε (eT E) cpT cmT) (gaW ε lam) ⊓ tensFock W ⊓ physicalSubspace ε

def kerZ (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (z : TensorProduct ℂ M (Fock n)) :
    Submodule ℂ (TensorProduct ℂ M (Fock n)) :=
  kLowSpan ε (diagE ε (eT E) cpT cmT) z

def datK (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) : Submodule ℂ M :=
  khwSub ε E (lowK ε lam) ⊓ LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • (1 : Module.End ℂ M)) ⊓ kFinSub ε E

end ReciprocityTheory.ChartRestriction.DS.TRGap
