import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntisymOfEventually

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

noncomputable section

namespace GlobalTheory.CovTest

theorem exists_eval_eq_pow_lin {ι : Type} [Fintype ι] (d : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) :
    ∃ Q : MvPolynomial ι ℝ, ∀ x : ι → ℝ, eval x Q = Φ (GlobalTheory.ArInt.lin x ^ d) := by
  classical
  refine ⟨∑ a ∈ (Finset.univ : Finset ι).piAntidiag d,
    monomial (Finsupp.equivFunOnFinite.symm a) ((Nat.multinomial Finset.univ a : ℝ) *
      Φ (monomial (Finsupp.equivFunOnFinite.symm a) 1)), fun x => ?_⟩
  rw [GlobalTheory.ArInt.lin, Finset.sum_pow_eq_sum_piAntidiag, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : (Nat.multinomial Finset.univ a : MvPolynomial ι ℝ) * ∏ i, (C (x i) * MvPolynomial.X i) ^ a i =
      ((Nat.multinomial Finset.univ a : ℝ) * ∏ i, x i ^ a i) • monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℝ) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), smul_eq_C_mul]
    simp [mul_pow, Finset.prod_mul_distrib, mul_assoc]
  rw [e, map_smul, eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul]
  ring

theorem pow_lin_add_comp_eq_zero {ι : Type} [Fintype ι] (d : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (e : ι → ι)
    (h : ∀ n : ι → ℤ, Φ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ d) + Φ (GlobalTheory.ArInt.lin (fun i => (n (e i) : ℝ)) ^ d) = 0)
    (x : ι → ℝ) : Φ (GlobalTheory.ArInt.lin x ^ d) + Φ (GlobalTheory.ArInt.lin (fun i => x (e i)) ^ d) = 0 := by
  obtain ⟨Q, hQ⟩ := exists_eval_eq_pow_lin d Φ
  have h0 : Q + rename e Q = 0 := by
    refine funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun y hy => ?_
    choose n hn using fun i => hy i trivial
    obtain rfl : (fun i => (n i : ℝ)) = y := funext hn
    simp only [map_add, eval_rename, hQ, Function.comp_def, map_zero]
    exact h n
  have := congrArg (eval x) h0
  simpa only [map_add, eval_rename, hQ, Function.comp_def, map_zero] using this

theorem antisym_of_swapEq : ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (Φ : ℝ → Fn Y) (hh : Fn Y)
    (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ), LimFam Φ → Propor Y → SwapEq Y G hh (degFl D.what₂.Tau Y.N) →
    (∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → SwapEq Y G (Y.arDeg (GlobalTheory.FlagAr.setB Y B) R) Y.chern) → Antisym Φ hh := by
  intro D Y Φ hh G hlim hprop hG hA
  refine antisym_of_eventually D Y Φ hh hlim fun B hB => ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR τ a b hab hj u
  let L : Fn Y := Y.arDeg (GlobalTheory.FlagAr.setB Y B) R - Y.vol • hh
  have hint : ∀ n : D.what₂.Tau × Fin Y.N → ℤ,
      L (GlobalTheory.ArInt.lin (fun z => (n z : ℝ)) ^ (dimFl D.what₂.Tau Y.N + 1)) +
        L (GlobalTheory.ArInt.lin (fun z => (n (swapAt τ a b z) : ℝ)) ^ (dimFl D.what₂.Tau Y.N + 1)) = 0 := by
    intro n
    have h1 := hA B hB R hR τ a b hab hj n
    have h2 := hG τ a b hab hj n
    rw [hprop] at h1
    simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination h1 - Y.vol * h2
  have hreal := pow_lin_add_comp_eq_zero _ L (swapAt τ a b) hint (fun z => -u z.1 z.2)
  have e1 : ∀ v : Wt Y, linRoot v = GlobalTheory.ArInt.lin (fun z => -v z.1 z.2) := fun v => by
    simp [linRoot, GlobalTheory.ArInt.lin, Finset.sum_neg_distrib]
  simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hreal
  simp only [GlobalTheory.FlagAr.atWt, e1]
  linear_combination hreal

end GlobalTheory.CovTest
