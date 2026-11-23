import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory

namespace IntegralCusp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem norm_eval_le_of_isHomogeneous' {N d : ℕ} {p : MvPolynomial (Fin N) ℂ}
    (hp : p.IsHomogeneous d) (w : Fin N → ℂ) :
    ‖MvPolynomial.eval w p‖ ≤ (∑ s ∈ p.support, ‖p.coeff s‖) * ‖w‖ ^ d := by
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdeg : ∑ j, s j = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  calc ∏ j, ‖w j ^ s j‖ ≤ ∏ j, ‖w‖ ^ s j := by
        refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w j) _
    _ = ‖w‖ ^ d := by rw [Finset.prod_pow_eq_pow_sum, hdeg]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.IntegralCusp.exists_root_bound (N k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) ℂ)
    (hc : ∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin N → ℂ) (g : ℂ),
      g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i = 0 →
        ‖g‖ ≤ C * ‖w‖ ^ k := by
  classical
  set A : ℕ → ℝ := fun i => ∑ s ∈ (cf i).support, ‖(cf i).coeff s‖ with hA
  have hA0 : ∀ i, 0 ≤ A i := fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set B : ℝ := 1 + ∑ i ∈ Finset.range m, A i with hBdef
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hA0 i)
  have hB0 : 0 < B := by linarith
  refine ⟨B, hB0.le, fun w g hg => ?_⟩
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero]; positivity
  have hroot : g ^ m = -∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
    have h1 : g * (g ^ m + ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i) = 0 := by
      have hs : ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i =
          g * ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
      rw [mul_add, ← hs]
      exact hg
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h1).resolve_left hg0)
  set x := ‖g‖ with hx
  set t := ‖w‖ ^ k with ht
  have hx0 : 0 < x := norm_pos_iff.mpr hg0
  have ht0 : 0 ≤ t := by positivity
  by_contra hlt
  push_neg at hlt
  have htx : t ≤ x / B := by rw [le_div_iff₀ hB0]; linarith
  have hterm : ∀ i ∈ Finset.range m,
      ‖MvPolynomial.eval w (cf i) * g ^ i‖ ≤ A i * (x ^ m / B) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow]
    have hci := norm_eval_le_of_isHomogeneous' (hc i him) w
    have hpow : ‖w‖ ^ ((m - i) * k) = t ^ (m - i) := by rw [ht, ← pow_mul, mul_comm]
    have hkey : t ^ (m - i) * x ^ i ≤ x ^ m / B := by
      have h1 : t ^ (m - i) ≤ (x / B) ^ (m - i) := pow_le_pow_left₀ ht0 htx _
      have h2 : B ≤ B ^ (m - i) := le_self_pow₀ hB1 (by omega)
      calc t ^ (m - i) * x ^ i ≤ (x / B) ^ (m - i) * x ^ i := by gcongr
        _ = x ^ m / B ^ (m - i) := by
          rw [div_pow, div_mul_eq_mul_div, ← pow_add, Nat.sub_add_cancel him.le]
        _ ≤ x ^ m / B := div_le_div_of_nonneg_left (by positivity) hB0 h2
    calc ‖MvPolynomial.eval w (cf i)‖ * x ^ i ≤ A i * t ^ (m - i) * x ^ i := by
          gcongr
          rw [← hpow]
          exact hci
      _ = A i * (t ^ (m - i) * x ^ i) := by ring
      _ ≤ A i * (x ^ m / B) := mul_le_mul_of_nonneg_left hkey (hA0 i)
  have hbound : x ^ m ≤ (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by
    calc x ^ m = ‖g ^ m‖ := by rw [norm_pow]
      _ = ‖∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i‖ := by rw [hroot, norm_neg]
      _ ≤ ∑ i ∈ Finset.range m, ‖MvPolynomial.eval w (cf i) * g ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range m, A i * (x ^ m / B) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by rw [Finset.sum_mul]
  have hS : ∑ i ∈ Finset.range m, A i = B - 1 := by rw [hBdef]; ring
  have hxm : 0 < x ^ m / B := by positivity
  have hBx : B * (x ^ m / B) = x ^ m := by field_simp
  rw [hS, sub_mul, _root_.one_mul, hBx] at hbound
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.IntegralCusp.nfac_nsmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (k : ℕ) (h : ∀ τ i, la' τ i = k * la τ i) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la' x = X.nfac la x ^ k := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
variable {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} in

theorem _root_.GlobalTheory.IntegralCusp.laU_nsmul {σ : c.F →+* ℂ} {r : ℕ} (U : _root_.Formalism.L2.PjFree.Unf Xo c σ r)
    (a : (E →+* ℂ) × ℕ → ℕ) (n k : ℕ) (hn : Even n) (j : U.Comp) (τ : (U.X j).Ψ) (i : Fin r) :
    _root_.Formalism.L2.PjFree.laU U (k • a) (k * n) j τ i = k * _root_.Formalism.L2.PjFree.laU U a n j τ i := by
  unfold _root_.Formalism.L2.PjFree.laU
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Nat.mul_div_assoc k hn.two_dvd]
  split_ifs <;> push_cast <;> ring

def evHom {σ : c.F →+* ℂ} (y : FrPt Xo c (CAt σ))
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    Rul Xo c →+* ℂ where
  toFun f := Formalism.L2.PjFree.toC (evR Xo c f y)
  map_one' := evalAt_one _ _ y hy
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
variable {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} in
theorem _root_.GlobalTheory.IntegralCusp.evHom_aeval {σ : c.F →+* ℂ} (y : _root_.Formalism.L2.Pj.FrPt Xo c (_root_.Formalism.L2.Pj.CAt σ))
    (hy : _root_.Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => _root_.Formalism.L2.Pj.FrPt Xo c S) (fun φ y z => _root_.Formalism.L2.Pj.FrMap φ y z) y) {N : ℕ}
    (w : Fin N → _root_.Formalism.L2.Pj.Rul Xo c) (p : MvPolynomial (Fin N) c.F) :
    _root_.GlobalTheory.IntegralCusp.evHom y hy (MvPolynomial.aeval w p) =
      MvPolynomial.eval (fun i => _root_.GlobalTheory.IntegralCusp.evHom y hy (w i))
        (MvPolynomial.map σ p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.eval_C,
      Algebra.algebraMap_eq_smul_one]
    show _root_.Formalism.L2.PjFree.toC (_root_.Formalism.L2.Pj.evalAt _ _ (a • (1 : _root_.Formalism.L2.Pj.Rul Xo c)) y) = σ a
    rw [_root_.Formalism.L2.Pj.evalAt_smul, _root_.Formalism.L2.Pj.evalAt_one _ _ y hy, _root_.mul_one]
    rfl
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.eval_X]

end IntegralCusp

end GlobalTheory
