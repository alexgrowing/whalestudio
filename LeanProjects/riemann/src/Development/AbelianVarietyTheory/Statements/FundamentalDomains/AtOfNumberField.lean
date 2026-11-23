import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.IsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow

noncomputable section
namespace GlobalTheory.KeyKa

def ConnFam : Prop :=
  ∀ x : KeyIn ℂ, ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S)
    (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧
    (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧
    ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) →
      (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ),
        charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)

namespace ConnFamTest

def At (x : KeyIn ℂ) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S)
    (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧
    (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧
    ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) →
      (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ),
        charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)

theorem connFam_iff : ConnFam ↔ ∀ x, At x := Iff.rfl

theorem exists_datum (H : TorusAlgebraic) (g : ℕ) (hg : 1 ≤ g) : ∃ x : KeyIn ℂ, x.P.g = g :=
  let ⟨x, _, _, h, _⟩ := KeyPow.Test.exists_classical H g hg 0 0 (Or.inl rfl) (Or.inl rfl)
  ⟨x, h⟩

theorem exists_fibre {k S : Type} [Field k] [NumberField k] [CommRing S] [Algebra k S] (y : KeyIn S) (s₀ : S →ₐ[k] k) :
    ∃ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) := by
  obtain ⟨e⟩ : Nonempty (k →+* ℂ) := inferInstance
  exact ⟨e, exists_keyPB_ring y _⟩

theorem exists_value (hK : KeyFormula) (hU : ThetaUnifAV) {k S : Type} [Field k] [NumberField k] [CommRing S]
    [Algebra k S] (y : KeyIn S) (s₀ : S →ₐ[k] k) : ∃ t₀ : k, t₀ ≠ 0 ∧
    ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) →
      (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ),
        charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8) := by
  obtain ⟨κ, hH, hF, -, hN⟩ := keyRule_one_of_keyFormula hK
  obtain ⟨y₀, hy₀⟩ := exists_keyPB_ring y s₀.toRingHom
  refine ⟨κ k y₀, (κ k y₀).ne_zero, fun e x₀ hx => ?_⟩
  obtain ⟨⟨τ, M, a, b, c, hab, hc, hM, h⟩, -⟩ := KeyNormalExists.exists_normalAt hU x₀
  refine ⟨τ, M, a, b, c, hab, hc, h, ?_⟩
  rw [← hF k ℂ e y₀ x₀ y₀.g_pos (KeyCancel.keyPB_cancel _ _ _ y y₀ x₀ _ _ hy₀ hx)]
  refine (value_at_normalForm (fun _ => 1) 1 (κ ℂ) x₀.P.g a b x₀.g_pos (hH ℂ) ?_ x₀ rfl τ M c hc hM h).trans (pow_one _)
  intro x hg τ' hx'
  exact hN x τ' _ _ x.g_pos ⟨fun i => hab.1 _, fun i => hab.2 _⟩ hx'

end ConnFamTest
end GlobalTheory.KeyKa
end
