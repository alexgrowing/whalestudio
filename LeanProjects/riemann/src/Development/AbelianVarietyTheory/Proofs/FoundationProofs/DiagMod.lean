import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Lev (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f

def IntC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V

def SmallC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V.nonunits

def Prim (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop :=
  IntC X V f ∧ ∃ r : ℚ, V.valuation ((X.exp f).coeff r) = 1

def Dom (X : Tower Ω ε) (V : ValuationSubring Ω) (W : ValuationSubring X.K) : Prop :=
  (∀ f, IntC X V f → f ∈ W) ∧ (∀ f, SmallC X V f → W.valuation f < 1) ∧ ∀ f, Prim X V f → W.valuation f = 1

def Gauss {F L : Type} [Field F] [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L) : Prop :=
  (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ ∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
    (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1

def FrobV (V : ValuationSubring Ω) (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Nq (X : Tower Ω ε) (M q : ℕ) (f : X.K) : X.K :=
  ∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f

def DiagMod (M q : ℕ) (γ : SL(2, ℤ)) : Prop :=
  (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = q

def levF (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω (AlgebraicClosure X.K) :=
  IntermediateField.adjoin Ω (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f})

def rootF (X : Tower Ω ε) (M₀ M m : ℕ) (U : X.K) : IntermediateField (levF X M₀) (AlgebraicClosure X.K) :=
  IntermediateField.adjoin (levF X M₀) (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f} ∪
    {y | ∃ γ ∈ CongruenceSubgroup.Gamma M₀, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) U)})

theorem lev_jK (X : Tower Ω ε) (M : ℕ) : Lev X M X.jK := fun γ _ => X.j_inv γ

end GlobalTheory.KZ.ES
