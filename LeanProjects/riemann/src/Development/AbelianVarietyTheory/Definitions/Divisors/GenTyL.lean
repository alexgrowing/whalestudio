import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlagM3PadicGlobal

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

def GenTyL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ))
      (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ), (∀ j, IsIntegralOpW ι lam w₀ (t j)) → ActsBy K t η →
    ∀ (Fam : ∀ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ), (J →* Multiplicative (ZMod (l ^ m))) → Prop),
      (∀ J m θ, Fam J m θ → IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
        IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧
        Function.Surjective θ) →
      (∀ N : Set (GL (Fin a) (w₀.adicCompletion E)), IsOpen N → 1 ∈ N → ∀ m₀ : ℕ,
        ∃ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), m₀ ≤ m ∧ (J : Set (GL (Fin a) (w₀.adicCompletion E))) ⊆ N ∧ Fam J m θ) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∈ S, IsSplitAt w ∧ Apart w w₀ ∧
        ∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w a → x ∈ K) →
    ∀ D : MvPolynomial (Fin a) ℤ, D.IsSymmetric → D ≠ 0 →
    ∀ U, OfType lam K U →
      PolyApprox (fun j => ι.symm (η U j)) {ϑ | ∃ U', OfType lam K U' ∧
        (∃ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), Fam J m θ ∧ ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ HasTypeVec w₀ K J θ χ U') ∧
        (∀ w ∈ S, GenAt D U' w) ∧ ϑ = fun j => ι.symm (η U' j)}

end GlobalTheory.CongW
