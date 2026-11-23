import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SgSmul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PartialDerivMonomialLaplace

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

variable {n : ℕ}

private theorem cf_ext' {f g : FR n} (h : ∀ x, cf f x = cf g x) : f = g := (cfBasic n).2.2.1 f g h

private theorem cf_add' (f g : FR n) (x : Wt n) : cf (f + g) x = cf f x + cf g x :=
  ((cfBasic n).2.2.2.1 f g 0 x).1

private theorem cf_smul' (c : ℂ) (f : FR n) (x : Wt n) : cf (c • f) x = c * cf f x :=
  ((cfBasic n).2.2.2.1 f f c x).2

private theorem cf_ex_mul (f : FR n) (x y : Wt n) : cf (ex y * f) x = cf f (x - y) :=
  (cfBasic n).2.2.2.2.1 f x y

private theorem cf_zero' (x : Wt n) : cf (0 : FR n) x = 0 := by
  simpa using cf_smul' 0 (0 : FR n) x

private theorem cf_sub' (f g : FR n) (x : Wt n) : cf (f - g) x = cf f x - cf g x := by
  have h : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h, cf_add', cf_smul']; ring

private theorem cf_sum' {ι : Type*} (s : Finset ι) (g : ι → FR n) (x : Wt n) :
    cf (∑ i ∈ s, g i) x = ∑ i ∈ s, cf (g i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cf_zero']
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, cf_add', ih]

private def partialDerivMonomialLaplace (a : Fin n) (f : FR n) : FR n :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support (fun x => (x a : ℂ) * f.coeff x)
    (fun x hx => by
      simp only [Finsupp.mem_support_iff]
      exact right_ne_zero_of_mul hx))

private theorem coeff_laplacian_diagonal (a : Fin n) (f : FR n) (x : Wt n) :
    cf (partialDerivMonomialLaplace a f) x = (x a : ℂ) * cf f x := by
  simp [cf, partialDerivMonomialLaplace]

private def lapD (a : Fin n) : FR n →ₗ[ℂ] FR n where
  toFun := partialDerivMonomialLaplace a
  map_add' f g := cf_ext' fun x => by
    rw [cf_add', coeff_laplacian_diagonal, coeff_laplacian_diagonal, coeff_laplacian_diagonal, cf_add', mul_add]
  map_smul' c f := cf_ext' fun x => by
    simp only [RingHom.id_apply]
    rw [cf_smul', coeff_laplacian_diagonal, coeff_laplacian_diagonal, cf_smul']; ring

private theorem cf_lapD (a : Fin n) (f : FR n) (x : Wt n) :
    cf (lapD a f) x = (x a : ℂ) * cf f x := coeff_laplacian_diagonal a f x

private theorem lapD_single (a : Fin n) (m : Wt n) (r : ℂ) :
    lapD a (AddMonoidAlgebra.single m r) = AddMonoidAlgebra.single m ((m a : ℂ) * r) := by
  refine cf_ext' fun x => ?_
  rw [cf_lapD]
  by_cases h : m = x
  · subst h; simp [cf]
  · simp [cf, Finsupp.single_apply, h]

private theorem lapD_ex (a : Fin n) (m : Wt n) : lapD a (ex m) = (m a : ℂ) • ex m := by
  simp [ex, lapD_single]

private theorem lapD_one (a : Fin n) : lapD a (1 : FR n) = 0 := by
  have h := lapD_ex a (0 : Wt n)
  rw [(cfBasic n).2.1] at h
  simpa using h

private theorem lapD_mul (a : Fin n) (f g : FR n) :
    lapD a (f * g) = lapD a f * g + f * lapD a g :=
  _root_.UpperTheory.Reformulated.B.Gs1.lapD_mul a f g

private theorem lapD_prod {ι : Type*} [DecidableEq ι] (a : Fin n) (s : Finset ι) (g : ι → FR n) :
    lapD a (∏ i ∈ s, g i) = ∑ i ∈ s, lapD a (g i) * ∏ j ∈ s.erase i, g j := by
  induction s using Finset.induction_on with
  | empty => simp [lapD_one]
  | insert i s hi ih =>
    rw [prod_insert hi, lapD_mul, ih, sum_insert hi, erase_insert hi, mul_sum]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    have hik : i ≠ k := fun h => hi (h ▸ hk)
    rw [erase_insert_of_ne hik, prod_insert (by simp [hi])]
    ring

private def lapL (f : FR n) : FR n := ∑ a, lapD a (lapD a f)

private theorem cf_lapL (f : FR n) (x : Wt n) : cf (lapL f) x = (nsq x : ℂ) * cf f x := by
  rw [lapL, cf_sum']
  simp only [cf_lapD, nsq]
  push_cast
  rw [sum_mul]
  exact sum_congr rfl fun a _ => by ring

private def lapE (p : Fin n × Fin n) : FR n := ex (-rt p.1 p.2)

private def lapP (p : Fin n × Fin n) : FR n := 1 - lapE p

private def lapQ (p : Fin n × Fin n) : FR n := ex (rhoV n) * ∏ j ∈ (posP n).erase p, lapP j

private theorem alt_rho : alt (rhoV n) = ex (rhoV n) * ∏ p ∈ posP n, lapP p := by
  simpa [lapP, lapE] using denom n 1

private theorem alt_q {p : Fin n × Fin n} (hp : p ∈ posP n) : alt (rhoV n) = lapP p * lapQ p := by
  rw [alt_rho, lapQ, ← mul_prod_erase (posP n) lapP hp]
  ring

private theorem rho_sum (a : Fin n) :
    (rhoV n a : ℂ) = ∑ p ∈ posP n, ((rt p.1 p.2 a : ℝ) : ℂ) / 2 := by
  obtain ⟨-, -, -, -, -, -, -, h1, h2⟩ := chRF n
  have h := congrFun (h1.symm.trans (h2 (posP n))) a
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
  have h' : rhoV n a = ∑ p ∈ posP n, rt p.1 p.2 a / 2 := by
    rw [← sum_div, ← h]; ring
  rw [h']
  push_cast
  rfl

private theorem lapD_P (a : Fin n) (p : Fin n × Fin n) :
    lapD a (lapP p) = ((rt p.1 p.2 a : ℝ) : ℂ) • lapE p := by
  simp [lapP, lapE, map_sub, lapD_one, lapD_ex]

private theorem lapD_alt (a : Fin n) :
    lapD a (alt (rhoV n)) =
      ∑ p ∈ posP n, (((rt p.1 p.2 a : ℝ) : ℂ) / 2) • ((1 + lapE p) * lapQ p) := by
  have h1 : lapD a (ex (rhoV n) * ∏ p ∈ posP n, lapP p) =
      (rhoV n a : ℂ) • (ex (rhoV n) * ∏ p ∈ posP n, lapP p) +
        ∑ p ∈ posP n, ((rt p.1 p.2 a : ℝ) : ℂ) • (lapE p * lapQ p) := by
    rw [lapD_mul, lapD_ex, lapD_prod, mul_sum, smul_mul_assoc]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    rw [lapD_P, lapQ]
    simp only [smul_mul_assoc, mul_smul_comm]
    congr 1
    ring
  rw [← alt_rho] at h1
  rw [h1, rho_sum, sum_smul, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [alt_q hp, lapP]
  have e1 : (1 - lapE p) * lapQ p = lapQ p - lapE p * lapQ p := by ring
  have e2 : (1 + lapE p) * lapQ p = lapQ p + lapE p * lapQ p := by ring
  rw [e1, e2]
  module

private theorem lapL_alt : lapL (alt (rhoV n)) = (nsq (rhoV n) : ℂ) • alt (rhoV n) :=
  cf_ext' fun x => by
    rw [cf_lapL, cf_smul']
    by_cases h : cf (alt (rhoV n)) x = 0
    · simp [h]
    · obtain ⟨w, rfl⟩ := (cfBasic n).2.2.2.2.2.2.2.2.2.2.1 (rhoV n) x h
      have e : nsq (rhoV n ∘ w) = nsq (rhoV n) := by
        simp only [nsq, Function.comp]
        exact Equiv.sum_comp w fun a => rhoV n a ^ 2
      rw [e]

private theorem lapL_mul (f g : FR n) :
    lapL (f * g) = lapL f * g + ∑ a, 2 * (lapD a f * lapD a g) + f * lapL g := by
  simp only [lapL]
  rw [sum_mul, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  simp only [lapD_mul, map_add]
  ring

private theorem rt_sum (g : Fin n → FR n) (i j : Fin n) :
    ∑ a, ((rt i j a : ℝ) : ℂ) • g a = g i - g j := by
  have h : ∀ a, ((rt i j a : ℝ) : ℂ) • g a =
      (if a = i then g a else 0) - (if a = j then g a else 0) := by
    intro a
    simp only [rt, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [sum_congr rfl fun a _ => h a, sum_sub_distrib]
  simp only [sum_ite_eq', mem_univ, if_true]

private theorem lap_cross (c : FR n) :
    ∑ a, 2 * (lapD a (alt (rhoV n)) * lapD a c) =
      ∑ p ∈ posP n, (1 + lapE p) * lapQ p * (lapD p.1 c - lapD p.2 c) := by
  have h : ∀ a, 2 * (lapD a (alt (rhoV n)) * lapD a c) =
      ∑ p ∈ posP n, ((rt p.1 p.2 a : ℝ) : ℂ) • ((1 + lapE p) * lapQ p * lapD a c) := by
    intro a
    rw [lapD_alt, sum_mul, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [smul_mul_assoc, two_mul, ← add_smul, add_halves]
  simp_rw [h]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← rt_sum (fun a => lapD a c) p.1 p.2, mul_sum]
  exact sum_congr rfl fun a _ => (mul_smul_comm _ _ _).symm

private theorem laplacian_difference_eq_mul (c u : FR n) (p : Fin n × Fin n)
    (h : ∀ μ, cf u μ - cf u (μ + rt p.1 p.2) = ((μ p.1 - μ p.2 : ℝ) : ℂ) * cf c μ) :
    lapD p.1 c - lapD p.2 c = lapP p * u :=
  cf_ext' fun μ => by
    have e : lapP p * u = u - ex (-rt p.1 p.2) * u := by
      rw [lapP, lapE, sub_mul, one_mul]
    rw [e, cf_sub', cf_sub', cf_lapD, cf_lapD, cf_ex_mul, sub_neg_eq_add, h]
    push_cast
    ring

private theorem laplacian_sum_decomposition (c : FR n) (t : Fin n × Fin n → FR n) (s : ℂ)
    (h : ∀ μ, s * cf c μ = (nsq μ : ℂ) * cf c μ +
      ∑ p ∈ posP n, (cf (t p) μ + cf (t p) (μ + rt p.1 p.2))) :
    s • c = lapL c + ∑ p ∈ posP n, (1 + lapE p) * t p :=
  cf_ext' fun μ => by
    rw [cf_smul', cf_add', cf_lapL, cf_sum', h]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    have e : (1 + lapE p) * t p = t p + ex (-rt p.1 p.2) * t p := by
      rw [lapE, add_mul, one_mul]
    rw [e, cf_add', cf_ex_mul, sub_neg_eq_add]

theorem UpperTheory.RealTr.lapForm :
    ∀ (n : ℕ) (c : FR n) (t : Fin n × Fin n → FR n) (s : ℂ),
      (∀ p ∈ posP n, ∀ μ, cf (t p) μ - cf (t p) (μ + rt p.1 p.2) = ((μ p.1 - μ p.2 : ℝ) : ℂ) * cf c μ) →
      (∀ μ, s * cf c μ = (nsq μ : ℂ) * cf c μ + ∑ p ∈ posP n, (cf (t p) μ + cf (t p) (μ + rt p.1 p.2))) →
      ∀ x, cf (alt (rhoV n) * c) x ≠ 0 → (nsq x : ℂ) = s + (nsq (rhoV n) : ℂ) := by
  intro n c t s h1 h2 x hx
  have hq : lapL (alt (rhoV n) * c) = ((nsq (rhoV n) : ℂ) + s) • (alt (rhoV n) * c) := by
    have e1 : ∑ p ∈ posP n, (1 + lapE p) * lapQ p * (lapD p.1 c - lapD p.2 c) =
        alt (rhoV n) * ∑ p ∈ posP n, (1 + lapE p) * t p := by
      rw [mul_sum]
      refine sum_congr rfl fun p hp => ?_
      rw [laplacian_difference_eq_mul c (t p) p (h1 p hp), alt_q hp]
      ring
    rw [lapL_mul, lapL_alt, lap_cross, e1, add_smul, smul_mul_assoc, ← mul_smul_comm s,
      laplacian_sum_decomposition c t s h2]
    ring
  have h := congrArg (fun f => cf f x) hq
  simp only [cf_lapL, cf_smul'] at h
  rw [add_comm s]
  exact mul_right_cancel₀ hx h
