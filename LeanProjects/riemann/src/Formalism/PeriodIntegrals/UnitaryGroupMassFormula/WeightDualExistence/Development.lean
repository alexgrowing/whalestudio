import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

noncomputable section

namespace PI.UnitaryGroupMassFormula.AlgWtDualEx

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP

def IrrDual : Prop :=
  ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), ρ.IsIrreducible → ρ.dual.IsIrreducible

section

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def Match (γ : GQ L n) (γ₀ : GL (Fin n) L) : Prop :=
  (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
    (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)

def UnitaryOfMatch : Prop := ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L), Match L n γ γ₀ → γ₀ ∈ GQ0 L n

def ConjEmb : Prop := ∀ (τ : L →+* ℂ) (x : L),
  τ ((IsCMField.complexConj L : L →+* L) x) = ComplexEmbedding.conjugate τ x

def AlgDual : Prop := ∀ a : AlgWt L n, IsAlgWeight L n a.ρ.dual

def AlgDualCore : Prop := UnitaryOfMatch L n → ConjEmb L → AlgDual L n

variable {L n}

theorem finDim (a : AlgWt L n) : FiniteDimensional ℂ a.W := by
  first
    | exact a.alg.1
    | (have h := a.alg; unfold Formalism.AUTREP.IsAlgWeight at h; exact h.1)

def dualWt (a : AlgWt L n) (h2 : AlgDual L n) (h3 : IrrDual) : AlgWt L n where
  W := Module.Dual ℂ a.W
  ρ := a.ρ.dual
  alg := h2 a
  irr := by
    have := finDim a
    exact h3 _ _ a.ρ a.irr

end

end PI.UnitaryGroupMassFormula.AlgWtDualEx
