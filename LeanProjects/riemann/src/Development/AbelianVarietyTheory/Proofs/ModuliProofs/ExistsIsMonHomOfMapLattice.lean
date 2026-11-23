import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open LatticeHom in

theorem exists_isMonHom_of_map_lattice :
    ThetaUnifAV → Out.Laws → ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f := by
  intro hT hL P P' g u u' F hg hg' hF
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (w : HolUnif Q.A Q.L g), Q.g = g →
      ∃ (v : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : v.Λ → ℂ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        v.IsAH Hm χ ∧ (∀ (k : ℕ) θ, v.IsThetaFn Hm χ k θ → ∃ s, v.IsFnPow k s θ) ∧
        (∀ (k : ℕ) s, ∃ θ, v.IsThetaFn Hm χ k θ ∧ v.IsFnPow k s θ) ∧ ∀ z, v.ex (T z) = w.ex z := by
    rintro Q w rfl
    obtain ⟨rig, hrig⟩ := Q.rigid
    obtain ⟨v, Hm, χ, -, hAH, -, -, -, -, hsec, -⟩ := hT Q rig hrig
    obtain ⟨T, hTv⟩ := exists_linearEquiv_of_holUnif hL.mulN Q w v
    exact ⟨v, Hm, χ, T, hAH, fun k θ h => ((hsec k).2 θ h).exists, fun k s => ((hsec k).1 s).exists, hTv⟩
  obtain ⟨v, Hm, χ, T, hAH, hsec, -, hv⟩ := key P u hg
  obtain ⟨v', Hm', χ', T', hAH', -, hfn, hv'⟩ := key P' u' hg'
  let F₀ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := T'.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap
  have hF₀ : ∀ z, F₀ (T z) = T' (F z) := fun z => by simp [F₀]
  have hΛ : ∀ l ∈ v.Λ, F₀ l ∈ v'.Λ := fun l hl => by
    obtain ⟨z, rfl⟩ := T.surjective l
    rw [hF₀, ← v'.ker, hv', u'.ker]
    refine hF z ?_
    rwa [← u.ker, ← hv, v.ker]
  obtain ⟨d, hd⟩ := exists_complementary_theta ThetaLarge.exists_theta_apply_ne_zero v v' P.isLB P'.isLB hAH hAH'
    F₀ hΛ 4
  obtain ⟨f, hf, hfe⟩ := exists_isMonHom_of_complementary hL.ample P P' v v' hsec hfn F₀ hΛ d hd
  exact ⟨f, hf, fun z => by rw [← hv', ← hF₀, hfe, hv]⟩

end GlobalTheory
