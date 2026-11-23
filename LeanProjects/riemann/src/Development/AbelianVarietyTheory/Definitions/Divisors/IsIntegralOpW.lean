import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def wtSize (lam : (E →+* ℂ) → DomWeight a) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ k : Fin a, ((lam τ).w k).natAbs

def IntMat (u : HeightOneSpectrum (𝓞 E)) (x : Matrix (Fin a) (Fin a) (u.adicCompletion E)) : Prop :=
  ∀ i j, x i j ∈ u.adicCompletionIntegers E

def IsIntegralOpW (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (w₀ : HeightOneSpectrum (𝓞 E))
    (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU E a ∧ (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧
    ∃ d : ℕ, (∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E)))) ∧
      ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * wtSize lam)

def HasTypeVec (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E)))
    {A : Type} [Group A] (θ : J →* A) (χ : A →* ℂˣ) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x ∈ K, RU E a x φ = φ) ∧
    ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def CongTy : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ))
      (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ), (∀ j, IsIntegralOpW ι lam w₀ (t j)) → ActsBy K t η →
    ∀ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
    ∀ (m : ℕ) (θ : J →* Multiplicative (ZMod (l ^ m))), Function.Surjective θ →
    ∀ U, OfType lam K U → HasTypeVec w₀ K J θ 1 U →
      ∃ (s : Finset (Jx → Qbar l)) (c : (Jx → Qbar l) → Qbar l),
        (s : Set (Jx → Qbar l)) ⊆ {ϑ | ∃ U', OfType lam K U' ∧ (∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧
          HasTypeVec w₀ K J θ χ U') ∧ ϑ = fun j => ι.symm (η U' j)} ∧
        ∀ P : MvPolynomial Jx ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (η U j)) P - ∑ ϑ ∈ s, c ϑ * MvPolynomial.aeval ϑ P‖ ≤
          ((l : ℝ)⁻¹) ^ m

structure MatchSat (U : Submodule ℂ (UA E a → ℂ)) (π : CuspSub E a) (T : Finset (HeightOneSpectrum (𝓞 E))) : Prop where
  off : MatchOffT U π T
  sat : ∀ (w : HeightOneSpectrum (𝓞 E)), ¬ IsSplitAt w → w ∉ T →
    ∀ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
      ∀ α, HasSatAt U w s ϖ q α → (CG.mk π).HasSat w (GlobalTheory.LGrp.bcParam a α)

def BCBackSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ a : ℕ, 1 ≤ a → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
    ∀ w₀, IsSplitAt w₀ → ScU U w₀ →
    ∃ π : CuspSub E a, MatchSat U π T ∧ GlobalTheory.ContraPair.PolarizedPair π (quadChar E ^ a) ∧
      ∀ w, ¬ IsSplitAt w → w ∉ T → ∃ B, (CG.mk π).HasSat w B

end GlobalTheory.CongW
