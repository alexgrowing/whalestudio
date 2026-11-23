import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

def OverPair (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ) : Prop :=
  (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (x : E))‖ < 1) ∨
    (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (IsCMField.complexConj E (x : E)))‖ < 1)

def CongTyWt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam lam' : (E →+* ℂ) → DomWeight a) (Jx : Type)
      (t : Jx → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ),
      (∀ j, IsIntegralOpW ι lam w₀ (t j)) → (∀ j, IsIntegralOpW ι lam' w₀ (t j)) → ActsBy K t η →
      (∀ τ, lam' τ ≠ lam τ → OverPair ι w₀ τ) →
      (∃ U₀ : Submodule ℂ (UA E a → ℂ), IsAutRepU U₀ ∧ ∀ τ, HasWeightAt U₀ τ (lam' τ)) →
    ∀ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
      (∀ x ∈ J, ∃ y : Matrix (Fin a) (Fin a) (w₀.adicCompletion E), IntMat w₀ y ∧
        ((x : GL (Fin a) (w₀.adicCompletion E)) : Matrix (Fin a) (Fin a) (w₀.adicCompletion E)) =
          1 + ((l : w₀.adicCompletion E) ^ m) • y) →
    ∀ (θ : J →* Multiplicative (ZMod (l ^ m))), Function.Surjective θ →
    ∀ U, OfType lam K U → HasTypeVec w₀ K J θ 1 U →
      ∃ (s : Finset (Jx → Qbar l)) (c : (Jx → Qbar l) → Qbar l),
        (s : Set (Jx → Qbar l)) ⊆ {ϑ | ∃ U', OfType lam' K U' ∧ (∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧
          HasTypeVec w₀ K J θ χ U') ∧ ϑ = fun j => ι.symm (η U' j)} ∧
        ∀ P : MvPolynomial Jx ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (η U j)) P - ∑ ϑ ∈ s, c ϑ * MvPolynomial.aeval ϑ P‖ ≤
          ((l : ℝ)⁻¹) ^ m

end GlobalTheory.CongW
