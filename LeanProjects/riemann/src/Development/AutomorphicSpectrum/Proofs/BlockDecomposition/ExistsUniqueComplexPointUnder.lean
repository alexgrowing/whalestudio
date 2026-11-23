import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Under

open GlobalTheory.TuplePoint GlobalTheory.Points

theorem spZ_ext (f g : Sp ℂ ⟶ Sp ℤ) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

theorem top_ext {s s' : Γ(Sp ℂ, ⊤)} (h : valR (𝟙 (Sp ℂ)) ⊤ s = valR (𝟙 (Sp ℂ)) ⊤ s') : s = s' :=
  ext_of_dense (𝟙 (Sp ℂ)) fun _ => h

theorem hom_eq_of_val {N : ℕ} {φ ψ : Sp ℂ ⟶ PSpace ℤ N} (i : Fin (N + 1))
    (h₁ : ⊤ ≤ φ ⁻¹ᵁ chart ℤ N i) (h₂ : ⊤ ≤ ψ ⁻¹ᵁ chart ℤ N i)
    (h : ∀ j, valR φ (chart ℤ N i) (ratio ℤ N i j) = valR ψ (chart ℤ N i) (ratio ℤ N i j)) : φ = ψ := by
  refine GlobalTheory.ProjSpace.hom_ext (spZ_ext _ _) fun y => ⟨⊤, trivial, i, h₁, h₂, fun j => top_ext ?_⟩
  have e₁ := valR_appLE (𝟙 (Sp ℂ)) φ h₁ le_rfl (ratio ℤ N i j)
  have e₂ := valR_appLE (𝟙 (Sp ℂ)) ψ h₂ le_rfl (ratio ℤ N i j)
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h j).trans e₂.symm)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev blockVec (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) : Fin (n k + 1) → ℂ := fun i => z ⟨k, i⟩

theorem blockVec_ne_zero {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : Fin (m + 1)) :
    blockVec z k ≠ 0 := fun h => by
  obtain ⟨i, hi⟩ := hz k
  exact hi (congrFun h i)

theorem isUnder_of_comp {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (y : CxPts (mpStr ℤ m n) σ₀)
    (h : ∀ k, y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k)) : IsUnder y z := fun k i => by
  refine ⟨⟨fun hy => ne_zero_of_le (h k) hy le_rfl, fun hi => le_preimage_chart (h k) hi⟩, fun j hy => ?_⟩
  exact valR_pullRatio (h k) hy le_rfl j

theorem comp_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {y : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder y z) (k : Fin (m + 1)) :
    y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k) := by
  obtain ⟨i, hi⟩ := hz' k
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((H k i).1).2 hi
  refine hom_eq_of_val i (le_preimage_comp y.1 _ le_rfl hy)
    ((le_point_preimage_iff (o := ℤ) (ht := hz k) i).2 hi) fun j => ?_
  refine (valR_appLE y.1 (prB n k) le_rfl hy (ratio ℤ (n k) i j)).symm.trans ?_
  exact ((H k i).2 j hy).trans (valR_point_ratio (t := blockVec z k) (ht := hz k) hi j).symm

theorem existsUnique_isUnder (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∃! y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z := by
  have ht := blockVec_ne_zero hz
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k => point ℤ (blockVec z k) (ht k)
  have ha : ∀ k, a k ≫ toSpecBase ℤ (n k) = spMap σ₀ := fun _ => spZ_ext _ _
  let y : CxPts (mpStr ℤ m n) σ₀ := ⟨lift m n (spMap σ₀) a ha, lift_mpStr m n _ a ha⟩
  have hy : ∀ k, y.1 ≫ prB n k = a k := lift_pr m n _ a ha
  refine ⟨y, isUnder_of_comp ht y hy, fun y' H => Subtype.ext ?_⟩
  exact GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k =>
    (comp_of_isUnder ht hz H k).trans (hy k).symm

end GlobalTheory.CompanionTheory.MPDict.Under
