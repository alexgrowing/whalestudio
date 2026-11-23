import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FlagM3PadicGlobal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def TyEll : GlobalTheory.CongL.UnitaryAutomorphicTypeClass := fun E _ _ _ l a w₀ U =>
  ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m)))
    (χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ),
    IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
    (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧ Function.Surjective θ ∧ χ ≠ 1 ∧
    (∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
      (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) ∧
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def GenOf (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) : ℕ → ℕ → Multiset ℂˣ → Prop := fun a _ B =>
  ∀ α : Fin a → ℂˣ, Finset.univ.val.map α = B → MvPolynomial.aeval (fun i => (α i : ℂ)) (D a) ≠ 0

end GlobalTheory.CongW
