import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.PolarDeg

theorem lin_coeff_eq {ι κ : Type} (s : Finset ι) (s' : Finset κ) (a : ι → ℝ) (e : ι → ℕ) (b : κ → ℝ) (e' : κ → ℕ)
    (h : ∀ t : ℝ, ∑ i ∈ s, a i * t ^ e i = ∑ j ∈ s', b j * t ^ e' j) :
    ∑ i ∈ s, (if e i = 1 then a i else 0) = ∑ j ∈ s', (if e' j = 1 then b j else 0) := by
  have hP : (∑ i ∈ s, Polynomial.C (a i) * Polynomial.X ^ e i) =
      ∑ j ∈ s', Polynomial.C (b j) * Polynomial.X ^ e' j := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact h t
  have := congrArg (fun p => Polynomial.coeff p 1) hP
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
  simpa [eq_comm] using this

theorem num_expand {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ)
    (hf : ∀ (v : Fin (n + 1) → V) (π : Equiv.Perm (Fin (n + 1))), f (v ∘ π) = f v) (x y : V) (t : ℝ) :
    f (fun _ => x + t • y) =
      ∑ s : Finset (Fin (n + 1)), f (s.piecewise (fun _ => y) (fun _ => x)) * t ^ s.card := by
  have h1 : (fun _ : Fin (n + 1) => x + t • y) = (fun _ => t • y) + (fun _ => x) := by
    funext i; simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : s.piecewise (fun _ : Fin (n + 1) => t • y) (fun _ => x) =
      s.piecewise (fun i => (fun _ : Fin (n + 1) => t) i • (s.piecewise (fun _ => y) (fun _ => x)) i)
        (s.piecewise (fun _ => y) (fun _ => x)) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h2, MultilinearMap.map_piecewise_smul, Finset.prod_const, smul_eq_mul, mul_comm]

theorem num_lin {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ)
    (hf : ∀ (v : Fin (n + 1) → V) (π : Equiv.Perm (Fin (n + 1))), f (v ∘ π) = f v) (x y : V) :
    ∑ s : Finset (Fin (n + 1)), (if s.card = 1 then f (s.piecewise (fun _ => y) (fun _ => x)) else 0) =
      ((n : ℝ) + 1) * f (Fin.cons y fun _ => x) := by
  rw [← Finset.sum_filter]
  have hS : (Finset.univ.filter fun s : Finset (Fin (n + 1)) => s.card = 1) =
      Finset.univ.map ⟨fun i => {i}, Finset.singleton_injective⟩ := by
    ext s
    rw [Finset.mem_filter, Finset.mem_map, Finset.card_eq_one]
    simp only [Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor <;> rintro ⟨a, h⟩ <;> exact ⟨a, h.symm⟩
  rw [hS, Finset.sum_map]
  have h3 : ∀ i : Fin (n + 1), f (({i} : Finset (Fin (n + 1))).piecewise (fun _ => y) (fun _ => x)) =
      f (Fin.cons y fun _ => x) := by
    intro i
    rw [Finset.piecewise_singleton]
    have h4 : Function.update (fun _ : Fin (n + 1) => x) i y ∘ (Equiv.swap 0 i) =
        (Fin.cons y fun _ => x : Fin (n + 1) → V) := by
      rw [Function.update_comp_equiv]
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp [Function.update, Equiv.swap_apply_def]
    rw [← h4, hf]
  simp only [Function.Embedding.coeFn_mk, h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.PolarDeg

namespace GlobalTheory.PolarDeg

open MvPolynomial in

theorem linRoot_add_smul {ι : Type} [Fintype ι] {N : ℕ} (u w : ι → Fin N → ℝ) (t : ℝ) :
    Formalism.DegreeFormula.linRoot (u + t • w) = C t * Formalism.DegreeFormula.linRoot w + Formalism.DegreeFormula.linRoot u := by
  simp only [Formalism.DegreeFormula.linRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, C_add, C_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_neg, mul_assoc]
  ring

open MvPolynomial in

theorem arDeg_lin_mul_pow (D : D7) (Y : DV.ShimX D.what₂.Tau) (T : Real0 Y) (hT : TieDeg T) (B : ℝ) (hB : 2 ≤ B)
    (R : ℝ) (hR : Real.exp 2 ≤ R) (w u : Wt Y) :
    Y.arDeg (GlobalTheory.FlagAr.setB Y B) R (Formalism.DegreeFormula.linRoot w * Formalism.DegreeFormula.linRoot u ^ Formalism.MainNotions.WeightThresholdDefs.dimY Y) =
      ∑ c, (T.K B c).num (Fin.cons (T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) := by
  set A := Y.arDeg (GlobalTheory.FlagAr.setB Y B) R with hA
  set lw := Formalism.DegreeFormula.linRoot w
  set lu := Formalism.DegreeFormula.linRoot u
  have hf : ∀ t : ℝ, A (Formalism.DegreeFormula.linRoot (u + t • w) ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)) =
      ∑ m ∈ Finset.range (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 + 1), ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m * A (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m))) * t ^ m := by
    intro t
    rw [linRoot_add_smul, add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : (C t * lw) ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m) * ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m : MvPolynomial _ ℝ) =
        (t ^ m * ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m : ℝ)) • (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m)) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow, C_mul, ← map_natCast (C : ℝ →+* MvPolynomial _ ℝ)]
      ring
    rw [h1, map_smul, smul_eq_mul]
    ring
  have hg : ∀ t : ℝ, ∑ c, T.fR B c (u + t • w) 0 R =
      ∑ p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)),
        (T.K B p.1).num (p.2.piecewise (fun _ => T.L B p.1 w + (T.K B p.1).ar ((T.F p.1).phR R w))
          (fun _ => T.L B p.1 u + (T.K B p.1).ar ((T.F p.1).phR R u))) * t ^ p.2.card := by
    intro t
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h2 : T.L B c (u + t • w) + (0 : ℝ) • T.a B c + (T.K B c).ar ((T.F c).phR R (u + t • w)) =
        (T.L B c u + (T.K B c).ar ((T.F c).phR R u)) + t • (T.L B c w + (T.K B c).ar ((T.F c).phR R w)) := by
      simp only [map_add, map_smul, zero_smul, add_zero, smul_add]
      abel
    rw [Real0.fR, Calc.top, h2]
    exact num_expand (T.K B c).num (T.K B c).symm _ _ t
  have hfg : ∀ t : ℝ,
      ∑ m ∈ Finset.range (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 + 1), ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m * A (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m))) * t ^ m =
      ∑ p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)),
        (T.K B p.1).num (p.2.piecewise (fun _ => T.L B p.1 w + (T.K B p.1).ar ((T.F p.1).phR R w))
          (fun _ => T.L B p.1 u + (T.K B p.1).ar ((T.F p.1).phR R u))) * t ^ p.2.card := by
    intro t
    rw [← hf, ← hg]
    exact hT B hB R hR (u + t • w)
  have hc := lin_coeff_eq _ _ _ (fun m => m) _ (fun p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)) => p.2.card) hfg
  rw [Fintype.sum_prod_type] at hc
  simp only [Finset.sum_ite_eq', Finset.mem_range] at hc
  have hsum : ∀ c, (∑ s : Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)), if s.card = 1 then
      (T.K B c).num (s.piecewise (fun _ => T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        (fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u))) else 0) =
      ((Formalism.MainNotions.WeightThresholdDefs.dimY Y : ℝ) + 1) * (T.K B c).num (Fin.cons (T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) := fun c => by
    convert num_lin (T.K B c).num (T.K B c).symm _ _ using 5
  replace hc := hc.trans (Finset.sum_congr rfl fun c _ => hsum c)
  have hn1 : (0 : ℝ) < (Formalism.MainNotions.WeightThresholdDefs.dimY Y : ℝ) + 1 := by positivity
  rw [if_pos (by omega), Nat.choose_one_right, pow_one, Nat.add_sub_cancel, ← Finset.mul_sum] at hc
  push_cast at hc
  exact mul_left_cancel₀ hn1.ne' hc

end GlobalTheory.PolarDeg
