import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

namespace GlobalTheory

theorem lbIso_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X₀ : Over (Sp k)) (X : Over (Sp K)) (φ : X.left ⟶ X₀.left) (M N : LB X₀.left), IsPullback φ X.hom X₀.hom (spMap σ) → QuasiCompact X₀.hom → QuasiSeparated X₀.hom → M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ : Over (Sp k₁)) (χ : X₁.left ⟶ X₀.left), IsPullback χ X₁.hom X₀.hom (spMap α) → LBIso (M.pull χ) (N.pull χ) := by
  intro k K _ _ σ X₀ X φ M N hφ hqc hqs hM hN H
  letI := σ.toAlgebra
  have same : ∀ {Y Y' : Scheme.{0}} (a : Y ⟶ X₀.left) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀.left), a' = j ≫ a →
      LBIso (M.pull a) (N.pull a) → LBIso (M.pull a') (N.pull a') := fun a j a' e h =>
    LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h
  have hφ' : IsPullback φ X.hom X₀.hom (spMap (algebraMap k K)) := hφ
  have H₁ := same φ hφ'.isoPullback.inv (pullback.fst X₀.hom (spMap (algebraMap k K)))
    (IsPullback.isoPullback_inv_fst hφ').symm H
  obtain ⟨R, hR₀, ⟨s, rfl⟩, hiso⟩ := exists_fg_lbIso (C := K) (R₀ := ⊥) X₀.hom Subalgebra.fg_bot
    (M.pull (pullback.fst _ _)) (N.pull (pullback.fst _ _)) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.chartPull
      (chartPullOut M _ _ _ _ fun _ => (baseChangeMap_fst X₀.hom _).symm)
      (chartPullOut N _ _ _ _ fun _ => (baseChangeMap_fst X₀.hom _).symm) H₁)
  have H₂ := LBIso.chartPull (chartPullIn M _ _ _) (chartPullIn N _ _ _) hiso
  refine ⟨s, ?_⟩
  intro k₁ _ α β hαβ hs X₁ χ hχ
  have hR : ∀ x : Algebra.adjoin k (s : Set K), ∃ y, β y = x := by
    rintro ⟨x, hx⟩
    change x ∈ β.range
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact ⟨α r, RingHom.congr_fun hαβ r⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  choose ρ₀ hρ₀ using hR
  let ρ : Algebra.adjoin k (s : Set K) →+* k₁ :=
    { toFun := ρ₀
      map_one' := β.injective (by simp [hρ₀])
      map_mul' := fun x y ↦ β.injective (by simp [hρ₀])
      map_zero' := β.injective (by simp [hρ₀])
      map_add' := fun x y ↦ β.injective (by simp [hρ₀]) }
  have hρ₂ : ρ.comp (algebraMap k _) = α := RingHom.ext fun r ↦ β.injective
    ((hρ₀ _).trans (RingHom.congr_fun hαβ r).symm)
  let j : X₁.left ⟶ pullback X₀.hom (spMap (algebraMap k (Algebra.adjoin k (s : Set K)))) :=
    pullback.lift χ (X₁.hom ≫ spMap ρ) (by rw [Category.assoc, spMap_comp_ring, hρ₂, hχ.w])
  have hj₁ : j ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  refine same _ j χ ?_ H₂
  rw [baseChangeMap_fst, hj₁]

end GlobalTheory
