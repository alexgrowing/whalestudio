import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.OneMom

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def flip (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

@[simp] theorem flip_flip (k : Fin m × Fin n × Bool) : flip (flip k) = k := by
  obtain ⟨a, i, b⟩ := k; simp [flip]

def g1 (c : ℝ) (p q : ℕ) : ℂ := if p = q then ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) else 0

def phi (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ := ∏ a, ∏ i, g1 c (s (a, i, false)) (s (a, i, true))

def fac (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) (z : ℂ) : ℂ :=
  z ^ s (a, i, false) * star z ^ s (a, i, true) * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ))

theorem evX_monomial_mul_gs (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) (x : Fin m → Fin n → ℂ) :
    evX (monomial s r) x * gs c x = r * ∏ a, ∏ i, fac c s a i (x a i) := by
  have h1 : evX (monomial s r) x = r * ∏ a, ∏ i, (x a i ^ s (a, i, false) * star (x a i) ^ s (a, i, true)) := by
    rw [evX, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.prod_bool]
    simp [mul_comm]
  have h2 : gs c x = ∏ a, ∏ i, Complex.exp ((-(c * ‖x a i‖ ^ 2) : ℝ)) := by
    rw [gs, ← Complex.ofReal_neg]
    have : (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℝ) = ∑ a, ∑ i, (-(c * ‖x a i‖ ^ 2)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [this, Complex.ofReal_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Complex.ofReal_sum, Complex.exp_sum]
  rw [h1, h2, mul_assoc, ← Finset.prod_mul_distrib]
  congr 2
  funext a
  rw [← Finset.prod_mul_distrib]
  rfl

variable (hM : OneMom)

include hM in
theorem integrable_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX (monomial s r) x * gs c x) := by
  simp_rw [evX_monomial_mul_gs]
  refine Integrable.const_mul ?_ r
  exact Integrable.fintype_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))
    (fun a => Integrable.fintype_prod (f := fun i (z : ℂ) => fac c s a i z) (fun i => (hM c hc _ _).1))

include hM in
theorem mom_monomial (c : ℝ) (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) (r : ℂ) :
    mom c (monomial s r) = r * phi c s := by
  rw [mom]
  simp_rw [evX_monomial_mul_gs]
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_volume_eq_prod (f := fun a (y : Fin n → ℂ) => ∏ i, fac c s a i (y i))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (z : ℂ) => fac c s a i z)]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (hM c hc _ _).2

include hM in
theorem integrable_evX (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s r => exact integrable_monomial hM c hc s r
  | add P Q hP hQ =>
    have : (fun x => evX (P + Q) x * gs c x) = fun x => evX P x * gs c x + evX Q x * gs c x := by
      funext x; simp [evX, add_mul]
    rw [this]; exact hP.add hQ

include hM in
theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  rw [mom, mom, mom, ← integral_add (integrable_evX hM c hc P) (integrable_evX hM c hc Q)]
  congr 1; funext x; simp [evX, add_mul]

omit hM in
theorem mom_smul (c : ℝ) (r : ℂ) (P : PX m n) : mom c (r • P) = r * mom c P := by
  rw [mom, mom, ← integral_const_mul]
  congr 1; funext x; simp [evX, mul_assoc]

end PositivityTheory.Rg.Sw.LC
