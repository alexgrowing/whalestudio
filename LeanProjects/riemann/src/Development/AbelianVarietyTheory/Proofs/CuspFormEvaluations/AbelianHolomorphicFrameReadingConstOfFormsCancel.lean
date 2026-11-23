import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsHolomorphicGeneratorReadingAutomorphyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnVal.genRd_const : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)), t.IsGen → ∀ (N : ℕ) (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (Λ : K → (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Ga : AddSubgroup (Fin N → ℂ)), IsHolFam q → (∀ z k, q z ≫ φ k = (Φ.e (Λ k z)).left) → Submodule.span ℝ (Ga : Set (Fin N → ℂ)) = ⊤ → (∀ gm ∈ Ga, (∀ z, q (z + gm) = q z) ∧ ∀ k, Λ k gm ∈ Φ.lat) → (∀ z w, ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k w) = 0) → (∃ v : ℂ, v ≠ 0 ∧ ∀ z, Φ.GenRd φ ε t (q z) (fun k => Λ k z) v) ∧ ∀ gm ∈ Ga, ∏ k, Φ.χ (Λ k gm) ^ ε k = 1 := by
  intro S A _ _ L x0 g Φ Z K _ φ ε t ht N q Λ Ga hq hqe hspan hper hH
  obtain ⟨v, hv, hv0, hrd, -, hfac⟩ := GlobalTheory.T.exists_holomorphic_generator_reading_automorphy S A L x0 g Φ Z K φ ε t ht N q (fun k z => Λ k z) hq
    (fun k => (LinearMap.toContinuousLinearMap (Λ k)).differentiable) hqe
  have hprod : ∀ gm z, ∏ k, Φ.fac (Λ k gm) (Λ k z) ^ ε k = ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm z
    simp only [AnFr.fac, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
    have h : ∑ k, (ε k : ℂ) * (Real.pi * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * hermForm Φ.Hm (Λ k gm) (Λ k gm)) =
        Real.pi * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k z) (Λ k gm) +
        Real.pi / 2 * ∑ k, (ε k : ℂ) * hermForm Φ.Hm (Λ k gm) (Λ k gm) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, hH, hH]
    simp
  have hstep : ∀ gm ∈ Ga, ∀ z, v (z + gm) = v z * ∏ k, Φ.χ (Λ k gm) ^ ε k := by
    intro gm hgm z
    rw [← hprod gm z]
    exact hfac z (z + gm) (fun k => Λ k gm) ((hper gm hgm).1 z)
      (fun k => ⟨(hper gm hgm).2 k, map_add _ _ _⟩)
  have hnorm : ∀ gm ∈ Ga, ∀ z, ‖v (z + gm)‖ = ‖v z‖ := by
    intro gm hgm z
    rw [hstep gm hgm z, norm_mul, norm_prod]
    have : ∀ k, ‖Φ.χ (Λ k gm) ^ ε k‖ = 1 := fun k => by
      rw [norm_zpow, Φ.χ_norm _ ((hper gm hgm).2 k), one_zpow]
    simp [this]
  have hconst : ∀ z, v z = v 0 := by
    intro z
    refine norm_periodic_const_range Ga.subtype ?_ v hv (fun z a => hnorm a a.2 z) z 0
    simpa using hspan
  refine ⟨⟨v 0, hv0 0, fun z => hconst z ▸ hrd z⟩, fun gm hgm => ?_⟩
  have h := hstep gm hgm 0
  rw [hconst] at h
  exact (mul_eq_left₀ (hv0 0)).1 h.symm
