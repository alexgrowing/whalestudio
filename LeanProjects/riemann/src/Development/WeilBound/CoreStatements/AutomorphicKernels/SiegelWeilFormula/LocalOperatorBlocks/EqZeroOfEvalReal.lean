import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzPolyMulGauss

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

theorem fP_add_smul (a : ℂ) (P Q : PX m n) : fP (a • P + Q) = a • fP P + fP Q := by
  funext u
  simp [fP, evX, MvPolynomial.eval_add, MvPolynomial.smul_eval, add_mul, mul_assoc]

theorem fP_zero : fP (0 : PX m n) = 0 := by
  funext u
  simp [fP, evX]

theorem fP_one_zero : fP (1 : PX m n) 0 = 1 := by
  simp [fP, evX, gs]

section Real

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (MvPolynomial.coeff k p).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (MvPolynomial.coeff k p).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : MvPolynomial.coeff k (reP p) = (MvPolynomial.coeff k p).re := by
  classical
  rw [reP, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_re]

theorem coeff_imP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : MvPolynomial.coeff k (imaginary p) = (MvPolynomial.coeff k p).im := by
  classical
  rw [imaginary, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_im]

theorem eval_map_real (q : MvPolynomial σ ℝ) (y : σ → ℝ) :
    MvPolynomial.eval (fun i => (y i : ℂ)) (MvPolynomial.map (algebraMap ℝ ℂ) q) = ((MvPolynomial.eval y q : ℝ) : ℂ) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = MvPolynomial.map (algebraMap ℝ ℂ) (reP p) + MvPolynomial.C Complex.I * MvPolynomial.map (algebraMap ℝ ℂ) (imaginary p) := by
  ext k
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, coeff_reP,
    coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, MvPolynomial.eval (fun i => (y i : ℂ)) p = 0) :
    p = 0 := by
  have hre : ∀ y : σ → ℝ, MvPolynomial.eval y (reP p) = 0 ∧ MvPolynomial.eval y (imaginary p) = 0 := by
    intro y
    have h1 := h y
    rw [eq_map_re_add_im p, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C] at h1
    rw [eval_map_real, eval_map_real] at h1
    have hr := congrArg Complex.re h1
    have hi := congrArg Complex.im h1
    simp at hr hi
    exact ⟨hr, hi⟩
  have a1 : reP p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).1
  have a2 : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).2
  rw [eq_map_re_add_im p, a1, a2]
  simp

end Real

def subF (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)
  else MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)

def subG (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.C (2 * Complex.I)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.X (k.1, k.2.1, true))
  else MvPolynomial.C (2 : ℂ)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.X (k.1, k.2.1, true))

theorem subG_subF (P : PX m n) : MvPolynomial.bind₁ subG (MvPolynomial.bind₁ subF P) = P := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x _ = MvPolynomial.aeval x P
  rw [MvPolynomial.aeval_bind₁, MvPolynomial.aeval_bind₁]
  have e : (fun i => MvPolynomial.aeval (fun i => MvPolynomial.aeval x (subG (m := m) (n := n) i)) (subF i)) = x := by
    funext k
    obtain ⟨a, j, b⟩ := k
    cases b <;> simp [subF, subG] <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [e]

theorem evX_injective : Function.Injective (evX (m := m) (n := n)) := by
  intro P Q h
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : ∀ x, evX R x = 0 := fun x => by
    simp only [R, evX, map_sub]; exact sub_eq_zero.2 (congrFun h x)
  have h0 : MvPolynomial.bind₁ subF R = 0 := by
    apply eq_zero_of_eval_real
    intro y
    change MvPolynomial.aeval (fun i => (y i : ℂ)) _ = 0
    rw [MvPolynomial.aeval_bind₁]
    have := hR (fun a j => (y (a, j, false) : ℂ) + Complex.I * y (a, j, true))
    rw [evX] at this
    have e : (fun i => MvPolynomial.aeval (fun i => (y i : ℂ)) (subF (m := m) (n := n) i)) =
        fun k => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true))
          else (y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true) := by
      funext k
      obtain ⟨a, j, b⟩ := k
      cases b <;> simp [subF, Complex.ext_iff]
    rw [e]
    exact this
  rw [← subG_subF R, h0, map_zero]

theorem fP_injective : Function.Injective (fP (m := m) (n := n)) := by
  intro P Q h
  apply evX_injective
  funext u
  have e := congrFun h u
  simp only [fP] at e
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) e

theorem isSw_fP (P : PX m n) : IsSw (fP P) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_schwartz_poly_mul_gauss m n P
  exact ⟨φ, hφ⟩

theorem fP_eq_gZ (sg : ℤˣ) (P : PX m n) :
    fP P = fun u => evX P u * gZ sg ((Complex.I * ((sg : ℤ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) u := by
  funext u
  simp only [fP, gs, gZ]
  congr 2
  have htr : Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diag]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have hI : Complex.I * ((sg : ℤ) : ℂ) * (Complex.I * ((sg : ℤ) : ℂ)) = -1 := by
    rcases Int.units_eq_one_or sg with rfl | rfl <;> simp
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, htr, smul_eq_mul]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (-2 * (Real.pi : ℂ) * ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ)) * hI

theorem fin_deg (d : ℕ) : FiniteDimensional ℂ (MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d) :=
  inferInstance

def evW (d : ℕ) : MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d →ₗ[ℂ] ((Fin m → Fin n → ℂ) → ℂ) where
  toFun Q u := evX Q.1 u
  map_add' Q Q' := by funext u; simp [evX]
  map_smul' a Q := by funext u; simp [evX]

theorem evW_injective (d : ℕ) : Function.Injective (evW (m := m) (n := n) d) := fun Q Q' h =>
  Subtype.ext (evX_injective (funext fun u => congrFun h u))

theorem continuousOn_of_evX {X : Type} [TopologicalSpace X] {S : Set X} (d : ℕ) (φ : X → PX m n)
    (hd : ∀ x ∈ S, (φ x).totalDegree ≤ d) (hc : ∀ u, ContinuousOn (fun x => evX (φ x) u) S) (l : PX m n →ₗ[ℂ] ℂ) :
    ContinuousOn (fun x => l (φ x)) S := by
  classical
  set W := MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d
  let e : W ≃ₗ[ℂ] LinearMap.range (evW (m := m) (n := n) d) := LinearEquiv.ofInjective _ (evW_injective d)
  haveI : FiniteDimensional ℂ (LinearMap.range (evW (m := m) (n := n) d)) := e.finiteDimensional
  let l' : LinearMap.range (evW (m := m) (n := n) d) →ₗ[ℂ] ℂ := l ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  have hl' : Continuous l' := LinearMap.continuous_of_finiteDimensional l'
  have hW : ∀ x ∈ S, φ x ∈ W := fun x hx => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hd x hx)
  rw [continuousOn_iff_continuous_restrict]
  let g : S → LinearMap.range (evW (m := m) (n := n) d) := fun x => e ⟨φ x, hW x x.2⟩
  have hg : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun u => ?_
    exact (hc u).restrict
  refine (hl'.comp hg).congr fun x => ?_
  simp [l', g]

theorem gramX_true (x : Fin m → Fin n → ℂ) : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
  ext i j
  simp [gramX, Qp, Qb, evX, Matrix.mul_apply, Matrix.conjTranspose_apply, MvPolynomial.eval_sum]

end PositivityTheory.SiegelWeilFormula.KLI

end
