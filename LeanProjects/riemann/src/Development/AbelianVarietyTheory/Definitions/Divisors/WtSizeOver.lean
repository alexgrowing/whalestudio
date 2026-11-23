import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenTyL
import Development.AbelianVarietyTheory.Definitions.Divisors.OverPair

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

open Classical in

def wtSizeOver (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (u : HeightOneSpectrum (𝓞 E)) : ℕ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => OverPair ι u τ), ∑ k : Fin a, ((lam τ).w k).natAbs

def IsIntegralOpW' (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (w₀ : HeightOneSpectrum (𝓞 E))
    (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU E a ∧ (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧
    ∃ d : ℕ, (∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E)))) ∧
      ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d *
        ∑ᶠ (u : HeightOneSpectrum (𝓞 E)) (_ : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ cLoc u g ≠ 1), wtSizeOver ι lam u)

def GenTyL' : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ))
      (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ), (∀ j, IsIntegralOpW' ι lam w₀ (t j)) → ActsBy K t η →
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

end
