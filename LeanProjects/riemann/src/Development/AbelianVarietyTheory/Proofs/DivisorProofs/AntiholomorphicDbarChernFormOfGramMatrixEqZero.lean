import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.ChernDbar

variable {n : ℕ}

theorem dbar_dbar_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x v) z w = dbar (fun x => dbar u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e (a b : V n) : dbar (fun x => dbar u x a) z b = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ u) z b a
      + Complex.I * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) a + Complex.I * fderiv ℝ (fderiv ℝ u) z b (Complex.I • a)
      - fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a)) := by
    have e0 : (fun x => dbar u x a) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a + Complex.I • fderiv ℝ u x (Complex.I • a)) :=
      funext fun x => dbar_apply u x a
    rw [e0, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, dbar_apply,
      fderiv_fderiv_apply hu, smul_eq_mul]
    linear_combination (1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a) * Complex.I_mul_I
  rw [e, e, hs.eq w v, hs.eq (Complex.I • w) v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem dbarAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ} (hg : ∀ p, DifferentiableAt ℝ (g p) v)
    (c : ι → Alt n) : dbarAt (fun x => ∑ p, g p x • c p) v =
      ∑ a, ∑ p, dbar (g p) v (coordVec a) • (dzb a * c p) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have : coefwise (fun f => dbar f v (coordVec a)) (fun x => ∑ p, g p x • c p) =
      ∑ p, dbar (g p) v (coordVec a) • c p := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [dbar_sum (A := fun p x => g p x * (bas n).repr (c p) S) (fun p _ => (hg p).mul (differentiableAt_const _)),
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dbar_mul (hg p) (differentiableAt_const _)]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem differentiableAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ}
    (hg : ∀ p, DifferentiableAt ℝ (g p) v) (c : ι → Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun x => (bas n).repr (∑ p, g p x • c p) S) v := by
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact DifferentiableAt.fun_sum fun p _ => (hg p).mul (differentiableAt_const _)

theorem dbarAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v := by
  simp only [dbarAt, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  simp only [map_add, Finsupp.add_apply, FormMul.repr_coefwise]
  rw [dbar_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem dbarAt_const (c : Alt n) (v : V n) : dbarAt (fun _ => c) v = 0 := by
  simp [dbarAt, coefwise]

def IsClosedAt (v : V n) (F : V n → Ev n) : Prop :=
  (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ dbarAt (fun x => (F x : Alt n)) v = 0

theorem isClosedAt_const (v : V n) (c : Ev n) : IsClosedAt v fun _ => c :=
  ⟨fun _ => differentiableAt_const _, dbarAt_const _ _⟩

def closedAt (v : V n) : Subsemiring (V n → Ev n) where
  carrier := {F | IsClosedAt v F}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · rw [show (fun x => (bas n).repr ((F * G) x : Alt n) S) = _ from
        funext fun x => FormMul.repr_mul (F x : Alt n) (G x : Alt n) S]
      exact DifferentiableAt.fun_sum fun p _ => ((hF _).mul (hG _)).mul (differentiableAt_const _)
    · obtain ⟨y, hy⟩ := FormMul.dbarAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  one_mem' := isClosedAt_const v 1
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add, Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [dbarAt_add hF hG, hF0, hG0, add_zero]
  zero_mem' := isClosedAt_const v 0

theorem const_mem (v : V n) (c : Ev n) : (fun _ => c) ∈ closedAt v := isClosedAt_const v c

def closedRing (v : V n) : Subring (V n → Ev n) :=
  { closedAt v with
    neg_mem' := fun {F} hF => by
      have := (closedAt v).mul_mem (const_mem v (-1)) hF
      have e : (fun _ => (-1 : Ev n)) * F = -F := funext fun x => neg_one_mul _
      rwa [e] at this }

theorem dzb_dz_dzb (a b c : Fin n) : dzb c * (dz a * dzb b) = -(dzb b * (dz a * dzb c)) := by
  have h (b c : Fin n) : dzb c * (dz a * dzb b) = dz a * dzb b * dzb c :=
    Subalgebra.mem_center_iff.1 (sym (a, b)).2 (dzb c)
  rw [h, h, mul_assoc, mul_assoc, ← mul_neg]
  exact congrArg _ (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _))

theorem dbar_form_mem {v : V n} {θ : Fin n → V n → ℂ} (hθ : ∀ a, ContDiffAt ℝ 2 (θ a) v) :
    (fun x => ∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b)) ∈ closedRing v := by
  have e (x : V n) : ((∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b) : Ev n) : Alt n) =
      ∑ p : Fin n × Fin n, dbar (θ p.1) x (coordVec p.2) • (dz p.1 * dzb p.2) := by
    simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym, Fintype.sum_prod_type]
  have hd (p : Fin n × Fin n) : DifferentiableAt ℝ (fun x => dbar (θ p.1) x (coordVec p.2)) v :=
    differentiableAt_dbar_apply (hθ p.1) _
  change IsClosedAt v _
  refine ⟨fun S => ?_, ?_⟩
  · simp only [e]
    exact differentiableAt_sum_smul hd _ S
  · simp only [e]
    rw [dbarAt_sum_smul hd]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    set s : Alt n := ∑ c, ∑ b, dbar (fun x => dbar (θ a) x (coordVec b)) v (coordVec c) • (dzb c * (dz a * dzb b))
      with hs
    have h2 : s = -s := by
      conv_lhs => rw [hs, Finset.sum_comm]
      rw [hs, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dzb_dz_dzb a b c, dbar_dbar_comm (hθ a), smul_neg]
    have h3 : (2 : ℂ) • s = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h2
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

theorem coeff_charpolyRev_map {A B r : Type} [CommRing A] [CommRing B] [Fintype r] [DecidableEq r] (f : A →+* B)
    (M : Matrix r r A) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map, charpolyRev, charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 2
  ext i k : 2
  by_cases h : i = k <;> simp [h, Matrix.one_apply]

theorem dbarAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)),
    IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s,
    dbarAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have hθ (i k : r) (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn H x (coordVec a) i k) v :=
    h3.conn (hu v hv) (by norm_num) (coordVec a) i k
  let M : Matrix r r (closedRing v) := Matrix.of fun i k => ⟨_, dbar_form_mem (hθ i k)⟩
  have key (w : V n) : MvPolynomial.aeval sym (chernPoly H w j) = (M.charpolyRev.coeff j : V n → Ev n) w := by
    have h1 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have h2 := coeff_charpolyRev_map ((Pi.evalRingHom (fun _ : V n => Ev n) w).comp (closedRing v).subtype) M j
    refine h1.symm.trans (Eq.trans ?_ h2)
    congr 2
    ext i k : 2
    simp [M, curvPoly, curv, Algebra.smul_def]
  have hm : IsClosedAt v _ := (closedRing v).mul_mem (const_mem v (algebraMap ℂ _ (kappa ^ j))) (M.charpolyRev.coeff j).2
  have e : (fun w => (chernAt H w j : Alt n)) = fun w =>
      ((algebraMap ℂ (Ev n) (kappa ^ j) * (M.charpolyRev.coeff j : V n → Ev n) w : Ev n) : Alt n) :=
    funext fun w => by rw [chernAt, key, Algebra.smul_def]
  rw [e]
  exact hm.2

end GlobalTheory.CxForm.ChernDbar
