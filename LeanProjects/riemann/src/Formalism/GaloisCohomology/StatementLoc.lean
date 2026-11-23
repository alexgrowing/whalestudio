import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

open Representation ReciprocityTheory.Gal

namespace Formalism.GaloisCohomology

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

abbrev GK : Type := PadicAlgCl l ≃ₐ[K] PadicAlgCl l

def inertiaSet : Set (GK l K) := {σ | ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}

def inertiaK : Subgroup (GK l K) := Subgroup.closure (inertiaSet l K)

variable {l K}

def unrK {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (GK l K) M) :
    Submodule R (H1 rho) :=
  H1ur rho (inertiaK l K)

def InertiaIsSet : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K →
    ((inertiaK l K : Set (GK l K)) = inertiaSet l K) ∧ (inertiaK l K).Normal ∧
      IsClosed (inertiaK l K : Set (GK l K))

def InertiaProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → inertiaK l K ≠ ⊤

end Formalism.GaloisCohomology
