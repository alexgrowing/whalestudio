import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementB

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def FiltrationStandardSpan : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I}

def FiltrationTypeIntersection : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ x : M.ι → ℤ, x ∈ CF.Mpi pi ↔ (fun i => (x i : ℚ)) ∈ typeSum M pi

def FiltrationCoactionStable : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ x ∈ CF.Mpi pi, ∀ ℓ : GLCoord ℤ n →ₗ[ℤ] ℤ,
      (fun i => ℓ (Matrix.mulVec M.A (fun j => ((x j : ℤ) : GLCoord ℤ n)) i)) ∈ CF.Mpi pi

def FiltrationDirectSummand : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∃ C : Submodule ℤ (M.ι → ℤ), IsCompl (CF.Mpi pi) C

def FiltrationMaximalQuotient : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ mu ∈ pi, (∀ nu ∈ pi, DomLE mu nu → nu = mu) →
      ∃ Φ : (↥(CF.Mpi pi) ⧸ (CF.Mpi (pi \ {mu})).comap (CF.Mpi pi).subtype) ≃ₗ[ℤ]
          TensorProduct ℤ ↥(SMu mu) ↥(CF.MM mu),
        ∀ (j : CF.J) (I : TIdx (CF.mu j)) (x : ↥(CF.Mpi pi)) (y : ↥(SMu mu)) (z : ↥(CF.MM mu)),
          CF.mu j = mu → StdT I → x.1 = CF.vec j I → y.1 = brk (CF.mu j) I → z.1 = CF.vec j (canT (CF.mu j)) →
          Φ (Submodule.Quotient.mk x) = y ⊗ₜ z

def HighestVectorsEqLattice : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (mu : Fin n → ℤ), Dominant mu →
    (CF.MM mu : Set (M.ι → ℤ)) = {x | IsHighest M ℤ mu x}

def HighestVectorsRationalSpan : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (mu : Fin n → ℤ), Dominant mu →
    ∀ x : M.ι → ℚ, IsHighest M ℚ mu x →
      x ∈ Submodule.span ℚ {y | ∃ j, CF.mu j = mu ∧ y = fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)}

theorem filtration_theorem_of_clauses (h1 : FiltrationStandardSpan) (h2 : FiltrationTypeIntersection) (h3 : FiltrationCoactionStable) (h4 : FiltrationDirectSummand) (h5 : FiltrationMaximalQuotient) (h6 : HighestVectorsEqLattice) : ColumnFamilyFiltrationProperties :=
  fun n _ M CF pi hpi => ⟨h1 n M CF pi hpi, h2 n M CF pi hpi, h3 n M CF pi hpi, h4 n M CF pi hpi,
    fun mu hmu hmax => ⟨h5 n M CF pi hpi mu hmu hmax, h6 n M CF mu (hpi.1 mu hmu)⟩⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
