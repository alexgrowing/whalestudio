import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OverPair

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def CongWtLv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (v' : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → IsSplitAt v' → Apart v' w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → (∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' a → x ∈ K) →
    ∀ (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))), IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) →
    ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ),
      (∀ j, IsIntegralOpW ι lam w₀ (t j)) → (∀ j, ∀ g ∈ (t j).support, ∀ u, ¬ Apart u v' → cLoc u g = 1) →
      ActsBy (K ⊓ Kv.comap (cLoc v')) t η →
    ∀ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
    ∀ (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), Function.Surjective θ →
    ∀ U, OfType lam (K ⊓ Kv.comap (cLoc v')) U → HasTypeVec w₀ (K ⊓ Kv.comap (cLoc v')) J θ 1 U →
      ∃ (s : Finset (Jx → Qbar l)) (c : (Jx → Qbar l) → Qbar l),
        (s : Set (Jx → Qbar l)) ⊆ {ϑ | ∃ (U' : Submodule ℂ (UA E a → ℂ)) (mu : (E →+* ℂ) → DomWeight a),
          (∀ τ, mu τ ≠ lam τ → OverPair ι v' τ) ∧ OfType mu K U' ∧
          (∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ HasTypeVec w₀ K J θ χ U') ∧ ϑ = fun j => ι.symm (η U' j)} ∧
        ∀ P : MvPolynomial Jx ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (η U j)) P - ∑ ϑ ∈ s, c ϑ * MvPolynomial.aeval ϑ P‖ ≤
          ((l : ℝ)⁻¹) ^ m

end GlobalTheory.CongW
