import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def OpModel : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), HInvol H →
    ∃ (M : Submodule ℂ ({x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E))
      (cls : (Matrix (Fin n) (Fin n) ℂ → E) → M) (Eh : Fin n → Fin n → Module.End ℂ M),
      GlRel Eh ∧
      (∀ (t : ℕ) (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
          (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUH H g),
        SmoothOnH H f → qminorOp (EabH H) a b u f g = ((qminor Eh a b u (cls f) : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨g, hg⟩) ∧
      ∀ s : Matrix (Fin n) (Fin n) ℂ, inUH H s → ∃ ρ : Module.End ℂ M,
        (∀ f : Matrix (Fin n) (Fin n) ℂ → E, SmoothOnH H f → cls (fun x => f (x * s)) = ρ (cls f)) ∧
        (∀ (ψ : M) (y : Matrix (Fin n) (Fin n) ℂ) (hy : inUH H y) (y' : Matrix (Fin n) (Fin n) ℂ)
            (hy' : inUH H y'), y' = y * s → ((ρ ψ : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y, hy⟩ = (ψ : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y', hy'⟩) ∧
        ∀ a b : Fin n, Eh a b * ρ = ρ * ∑ c, ∑ d, (s⁻¹ c a * s b d) • Eh c d

end AAInvW
