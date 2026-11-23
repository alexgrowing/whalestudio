import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

noncomputable section

open NumberField

namespace Formalism.NormVectorIdentities.Items

open ReciprocityTheory.ChartRestriction.G.T0 (TVar OmS sImg)

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  {Ω : Type} [Field Ω] [Algebra K Ω]

def rkS (M : Submodule (𝓞 K) V) : ℕ := Module.finrank K (Submodule.span K (M : Set V))

abbrev GensS (V : Type) : Type := Σ n : ℕ, Fin (n + 1) → V

def IsGenS (W : Submodule (𝓞 K) V) (ev : V → Ω) (g : GensS V) : Prop :=
  Submodule.span (𝓞 K) (Set.range g.2) = W ∧ ev (g.2 0) ≠ 0

def xsS (ev : V → Ω) (g : GensS V) (k : Fin g.1) : Ω := ev (g.2 k.succ) / ev (g.2 0)

def delAtS (Dn : ℕ) (ev : V → Ω) (g : GensS V) : ℕ :=
  Module.finrank (IntermediateField.adjoin K (Set.range (sImg (D := Dn) (0 : Fin (g.1 + 1)) (xsS ev g)))) (OmS Ω Dn g.1)

open Classical in

def delS (Dn : ℕ) (W : Submodule (𝓞 K) V) (ev : V → Ω) : ℕ :=
  if ∃ g, IsGenS K W ev g then delAtS K Dn ev (Classical.epsilon (IsGenS K W ev)) else 0

def ShareLowS (T Dn : ℕ) (W MT : Submodule (𝓞 K) V) (ev : V → Ω) : Prop :=
  ((T - 1).choose Dn : ℝ) * (delS K Dn W ev : ℝ) ≤ (rkS K MT : ℝ)

end Formalism.NormVectorIdentities.Items
