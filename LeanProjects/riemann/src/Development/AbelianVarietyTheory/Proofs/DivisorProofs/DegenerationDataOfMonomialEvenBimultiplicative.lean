import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegFromMonomial

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (m : ℕ) (r : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ D.X), D.PsiEven → D.TauBimult → IsMonomial D r β → (∀ i, r i ∈ maximalIdeal R) → (∀ i y z, β i y z = β i z y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ DD : DegData R (maximalIdeal R), DD.toPre = D := by
  intro R _ _ _ D m r β hE hT hM hr hs hp
  have hmem : ∀ (y : D.X) (u : Rˣ) (n : Fin m → ℕ) (k : ℕ), k ≤ ∑ i, n i →
      (u : R) * ∏ i, r i ^ n i ∈ maximalIdeal R ^ k := by
    intro y u n k hk
    refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hr i) _
  let S : LinearMap.BilinForm ℤ D.X := ∑ i, β i
  have hS : ∀ y z, S y z = ∑ i, β i y z := fun y z => by
    simp [S, LinearMap.sum_apply]
  have hSs : ∀ y z, S y z = S z y := fun y z => by
    rw [hS, hS]; exact Finset.sum_congr rfl fun i _ => hs i y z
  have hSp : ∀ y, y ≠ 0 → 0 < S y y := fun y hy => by
    rw [hS]
    obtain ⟨i, hi⟩ := hp y hy
    exact Finset.sum_pos' (fun j _ => hM.nonneg j y) ⟨i, Finset.mem_univ _, hi⟩
  refine ⟨{ toPre := D, psi_even := hE, tau_bimult := hT, psi_pos := ?_, psi_tendsto := ?_ }, rfl⟩
  · intro y hy
    obtain ⟨u, n, hn, hc⟩ := hM y
    refine (GlobalTheory.PeriodFormEdge.psiIn_iff hc _).2 ?_
    have h1 := hmem y u n 1 ?_
    · rwa [pow_one] at h1
    · obtain ⟨i, hi⟩ := hp y hy
      have : 1 ≤ n i := by have := hn i; omega
      exact this.trans (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i))
  · intro k
    refine (GlobalTheory.ToricData.finite_form_le S hSs hSp (2 * k)).subset fun y hy => ?_
    simp only [Set.mem_setOf_eq] at hy ⊢
    by_contra hlt
    obtain ⟨u, n, hn, hc⟩ := hM y
    refine hy ((GlobalTheory.PeriodFormEdge.psiIn_iff hc _).2 (hmem y u n k ?_))
    have e : S y y = 2 * ((∑ i, n i : ℕ) : ℤ) := by
      rw [hS, Nat.cast_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hn i
    omega

end GlobalTheory.DegFromMonomial
