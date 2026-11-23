import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

def LevelGrp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Apart w w₀ →
    ∀ K₀ : Subgroup (UA E a), IsLevelAway w₀ K₀ → ∀ J : Subgroup (GL (Fin a) (w.adicCompletion E)),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin a) (w.adicCompletion E))) →
    ∃ K : Subgroup (UA E a), IsLevelAway w₀ K ∧ (∀ c ∈ K, cLoc w c ∈ J) ∧ (∀ x ∈ locU a w, cLoc w x ∈ J → x ∈ K) ∧
      (∀ x ∈ K₀, cLoc w x = 1 → x ∈ K) ∧ ∀ c ∈ K, ∃ k ∈ K₀, cLoc w k = 1 ∧ ∃ y ∈ locU a w, c = k * y

def LevelVec : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ →
    ∀ K : Subgroup (UA E a), K ≤ finU E a → IsCompact (K : Set (UA E a)) → (∀ x ∈ K, cLoc w x = 1) →
    ∀ φ ∈ U, φ ≠ 0 → (∀ x ∈ K, RU E a x φ = φ) →
    ∃ f : σ.V →ₗ[ℂ] (UA E a → ℂ), Function.Injective f ∧ (∀ v, f v ∈ U) ∧
      (∀ x ∈ locU a w, ∀ v, RU E a x (f v) = f (σ.ρ (cLoc w x) v)) ∧ ∀ x ∈ K, ∀ v, RU E a x (f v) = f v

def TrOp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ)
    (u : HeightOneSpectrum (𝓞 E)), IsSplitAt u → ((l : ℕ) : 𝓞 E) ∉ u.asIdeal →
    ∃ (t : UA E a →₀ ℂ) (η : Submodule ℂ (UA E a → ℂ) → ℂ), IsIntegralOp ι t ∧
      ∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ locU a u, cLoc u x ∈ GlobalTheory.LFun.KGL u a → RU E a x φ = φ) →
        opOf (RU E a) t φ = η U • φ ∧ (φ ≠ 0 → ∀ π : CuspSub E a,
          (∀ σ, π.IsLocComp u σ → IsCompAlong U (locU a u) ((cLoc u).comp (locU a u).subtype) σ.ρ) →
          ∃ B, (CG.mk π).HasSat u B ∧ η U = (UpperTheory.V.Af.algSat a (normV u) B).sum)

end UpperTheory.Gal.NearKilling
