import Mathlib
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.IsLocalModelOfIntegral
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyOfPeriod

theorem exists_keyIn_normalAt :
    ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), 1 ≤ g → τ.IsSymm → (τ.map Complex.im).PosDef → charHalf g a b → ∃ (x : KeyIn ℂ) (h : x.P.g = g), NormalAt x (τ.submatrix (Fin.cast h) (Fin.cast h)) 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 := by
  intro _ H g τ a b hg hs hp hab
  obtain ⟨P, u, th, e, hΛ, ⟨h₁, h₂⟩, hth, -⟩ := H g τ a b hs hp hab.1 hab.2
  subst e
  obtain ⟨rig, hr, hR⟩ := Test.exists_isRig u
  choose v hv using fun i : Fin P.g => (h₂ (Pi.single i (2 * Real.pi * Complex.I)⁻¹)).exists
  have hb := Test.isLieBasis_of_isDiff P u h₁ h₂ (inv_ne_zero Complex.two_pi_I_ne_zero) v
    (fun i => (hv i).1) fun i => (hv i).2
  obtain ⟨z, hz⟩ := Function.ne_iff.1 (TorusAlg.thetaChar_level hs hp hab.1 hab.2).1
  obtain ⟨i, hi⟩ := exists_chart P.isLB ((u.ex z).left (default : PrimeSpectrum ℂ))
  have hi' := (top_le_preimage_iff_mem _ _).2 hi
  have hne : th.f i ≠ 0 := fun h => by
    have := hth i z hi'
    rw [h, valAt'_zero] at this
    exact mul_ne_zero hz (u.fr_ne i z hi') this.symm
  exact ⟨⟨P, hg, rig, hr, th, exists_mem_nonzeroLocus P th ⟨i, hne⟩, v, hb⟩, rfl,
    (normalAt_one_iff _ _ _ _).2 ⟨u, hs, hp, hΛ, hR, hth, fun i => (hv i).2⟩⟩

end GlobalTheory.KeyOfPeriod
