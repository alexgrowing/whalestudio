import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalOfHypOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMemKOneOfSame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MembersGood

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RecT.Thread

section Level

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def LevelShape (π : NG.AutRep L n) : Prop :=
  ∃ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ NG.HypOutside J χ B ∧
    (∃ f ∈ NG.isoTyp π.ρ π.S, f ∈ NG.TypeSp π.ρ J χ ∧ f ≠ 0) ∧
    ∀ s : SplitPlace L, s.v ∈ B → ∃ s₀ : SplitPlace L, s₀.v = s.v ∧
      ((∃ (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s₀ r ξ) ∨
      ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i) ∧
        ∃ (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ)
          (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelUni J χ s₀ r ψ₀ ξ ∧ NG.IsPsi0 s₀ ψ₀ ∧
          ∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ,
            Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1))

theorem good_of_levelShape (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (π : NG.AutRep L n) (h : LevelShape π) :
    ∀ (s : SplitPlace L) (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s σ →
      GlobalTheory.RecT.Good (GlobalTheory.LocLanglands.cls σ) := by
  obtain ⟨J, χ, B, hc, hH, ⟨f, hf, hfT, hf0⟩, hB⟩ := h
  intro s σ hσ
  by_cases hs : s.v ∈ B
  · obtain ⟨s₀, hv, hB'⟩ := hB s hs
    rcases hB' with ⟨r, ξ, hP⟩ | ⟨hk, r, ψ₀, ξ, hU, hψ, ht⟩
    · exact GlobalTheory.AVGood.good_of_toral (GlobalTheory.ParaToral.toral_of_levelPara hBZ hZ L n π.toAlgWt π.S π.irrS J χ hc s₀ r ξ hP
        f hf hfT hf0 s hv.symm σ hσ)
    · exact GlobalTheory.AVGood.good_of_fixed_KOne hZ hk _ (GlobalTheory.UniDepthZero.main L n π.toAlgWt π.S π.irrS J χ hc s₀ r ψ₀ ξ hU hψ ht
        f hf hfT hf0 s hv.symm σ hσ)
  · exact GlobalTheory.AVGood.good_of_isSpherical hBZ _ (GlobalTheory.SphHyp.isSpherical_of_hypOutside L n π.toAlgWt π.S π.irrS J χ hc B hH
      f hf hfT hf0 s hs σ hσ)

end Level

end GlobalTheory.RecT.Thread

end
