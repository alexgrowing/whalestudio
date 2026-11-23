import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.LogHermHess

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι]

def affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x : E) : ℂ :=
  ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (c j + L j x)

theorem hasFDerivAt_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x : E) :
    HasFDerivAt (fun y => c + L y) L x := L.hasFDerivAt.const_add c

theorem contDiff_aff (c : ℂ) (L : E →L[ℂ] ℂ) : ContDiff ℝ 2 (fun y => c + L y) :=
  contDiff_const.add (L.restrictScalars ℝ).contDiff

theorem contDiff_conj_aff (c : ℂ) (L : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (starRingEnd ℂ) (c + L y)) :=
  Complex.conjCLE.contDiff.comp (contDiff_aff c L)

theorem del_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : del (fun y => c + L y) x v = L v := by
  rw [del_eq_fderiv (hasFDerivAt_aff c L x).differentiableAt, (hasFDerivAt_aff c L x).fderiv]

theorem dbar_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : dbar (fun y => c + L y) x v = 0 := by
  rw [dbar_eq_zero (hasFDerivAt_aff c L x).differentiableAt]; rfl

theorem contDiff_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) :=
  ((contDiff_aff c L).mul contDiff_const).mul (contDiff_conj_aff c' L')

theorem del_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    del (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = L v * q * (starRingEnd ℂ) (c' + L' x) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [del_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    del_mul h1 (differentiableAt_const q), del_conj, dbar_aff, del_aff]
  simp

theorem dbar_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    dbar (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = (c + L x) * q * (starRingEnd ℂ) (L' v) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [dbar_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    dbar_mul h1 (differentiableAt_const q), dbar_conj, dbar_aff, del_aff]
  simp

theorem contDiff_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (affForm Q c L) :=
  ContDiff.sum fun _ _ => ContDiff.sum fun _ _ => contDiff_term _ _ _ _ _

theorem del_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    del (affForm Q c L) x v = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x) := by
  unfold affForm
  rw [del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => del_term _ _ _ _ _ _ _

theorem dbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    dbar (affForm Q c L) x v = ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j v) := by
  unfold affForm
  rw [dbar_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dbar_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => dbar_term _ _ _ _ _ _ _

theorem ddbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v w : E) :
    ddbar (affForm Q c L) x v w = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w) := by
  rw [ddbar_eq_del_dbar (contDiff_affForm Q c L).contDiffAt]
  have : (fun y => dbar (affForm Q c L) y w)
      = affForm Q c L ∘ id - affForm Q c L ∘ id + fun y => ∑ i, ∑ j,
        (c i + L i y) * Q i j * (starRingEnd ℂ) (L j w + (0 : E →L[ℂ] ℂ) y) := by
    funext y; simp [dbar_affForm]
  rw [this, sub_self, zero_add,
    del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [del_term]; simp

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem ofReal_re_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x : E) : ((affForm Q c L x).re : ℂ) = affForm Q c L x := by
  rw [← Complex.conj_eq_iff_re, affForm]
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : (starRingEnd ℂ) (Q j i) = Q i j := hQ.apply i j
  rw [this]; ring

theorem leviForm_log_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x v w : E) (hx : affForm Q c L x ≠ 0) :
    leviForm (fun y => Real.log (affForm Q c L y).re) x v w
      = (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x
        - (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x))
          * (∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x ^ 2 := by
  have hre : (fun y => ((affForm Q c L y).re : ℂ)) = affForm Q c L :=
    funext (ofReal_re_affForm hQ c L)
  have hx' : (affForm Q c L x).re ≠ 0 := fun h => hx (by
    rw [← ofReal_re_affForm hQ c L x, h]; simp)
  have ht : ContDiffAt ℝ 2 (fun y => (affForm Q c L y).re) x :=
    (Complex.reCLM.contDiff.comp (contDiff_affForm Q c L)).contDiffAt
  rw [leviForm_real_comp (h := Real.log) (t := fun y => (affForm Q c L y).re)
    (Real.contDiffAt_log.2 hx') ht, leviForm, hre, ddbar_affForm, del_affForm, dbar_affForm,
    Real.deriv_log', deriv_inv]
  push_cast
  rw [ofReal_re_affForm hQ]
  ring

end General

theorem leviForm_log_herm : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2 := by
  intro n B _ _ e _ Q hQ u z hu h q hq hq0 a b
  let c : Option B → ℂ := fun i => Option.elim i 1 (fun a => z (e a))
  let L : Option B → (B → ℂ) →L[ℂ] ℂ := fun i => Option.elim i 0 (fun a => ContinuousLinearMap.proj a)
  let M : (B → ℂ) →L[ℂ] V n :=
    ∑ a, (ContinuousLinearMap.proj a : (B → ℂ) →L[ℂ] ℂ).smulRight (coordVec (e a))
  have hM : ∀ t, M t = ∑ a, t a • coordVec (e a) := fun t => by
    simp [M, ContinuousLinearMap.sum_apply]
  have hM1 : ∀ a, M (Pi.single a 1) = coordVec (e a) := fun a => by
    rw [hM]; simp [Pi.single_apply, ite_smul]
  have hφ : HasFDerivAt (fun t => z + M t) M 0 := M.hasFDerivAt.const_add z
  have h0 : z + M 0 = z := by simp
  have hc := leviForm_comp_holo (u := u) (φ := fun t => z + M t) (z := 0) (by rw [h0]; exact hu)
    (contDiff_const.add M.contDiff).contDiffAt (Pi.single a 1) (Pi.single b 1)
  rw [hφ.fderiv, hM1, hM1, h0] at hc
  have hw : ∀ (t : B → ℂ) i, Option.elim i 1 (fun a => z (e a) + t a) = c i + L i t := by
    intro t i; cases i <;> simp [c, L]
  have hf : (fun t => u (z + M t)) = fun t => Real.log (affForm Q c L t).re := by
    funext t
    rw [hM, h, affForm]
    simp only [hw]
    rfl
  have hq' : affForm Q c L 0 = q := by
    rw [hq, affForm]; simp [c]
  rw [← hc, hf, leviForm_log_affForm hQ _ _ _ _ _ (hq' ▸ hq0), hq']
  have hL : ∀ (a : B) i, L i (Pi.single a 1) = if i = some a then 1 else 0 := by
    intro a i; cases i <;> simp [L, Pi.single_apply]
  simp only [hL, map_zero, add_zero, apply_ite (starRingEnd ℂ), map_one, ite_mul, mul_ite, one_mul,
    zero_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  rfl

end GlobalTheory.LogHermHess
