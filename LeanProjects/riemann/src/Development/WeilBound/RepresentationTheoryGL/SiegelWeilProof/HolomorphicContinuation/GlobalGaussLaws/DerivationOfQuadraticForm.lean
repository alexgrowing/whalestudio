import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.MatLApply
import GroundTheory.GlobalFields.CompletionAtPlace

noncomputable section

open Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def Dv (X : Matrix (Fin m) (Fin m) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  MvPolynomial.mkDerivation ℂ (fun k : Fin m × Fin n × Bool => xyP X k.1 k.2.1 k.2.2)

theorem Dv_X (X : Matrix (Fin m) (Fin m) ℂ) (k : Fin m × Fin n × Bool) :
    Dv X (MvPolynomial.X k : PX m n) = xyP X k.1 k.2.1 k.2.2 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem Dv_eq (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    Dv X P = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k P := by
  let D₂ : Derivation ℂ (PX m n) (PX m n) :=
    ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • pderiv k
  have hs : ∀ Q : PX m n, D₂ Q = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k Q := by
    intro Q
    show (Derivation.coeFnAddMonoidHom (R := ℂ) (A := PX m n) (M := PX m n)
      (∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • (pderiv k : Derivation ℂ (PX m n) (PX m n)))) Q = _
    rw [map_sum, Finset.sum_apply]
    simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
  have h : Dv X P = D₂ P := by
    refine MvPolynomial.derivation_eq_of_forall_mem_vars (fun i _ => ?_)
    rw [hs, Dv_X]
    simp [pderiv_X, Pi.single_apply]
  rw [h, hs]

def Q2 (m n : ℕ) : PX m n := ∑ a, ∑ i, MvPolynomial.X (a, i, false) * MvPolynomial.X (a, i, true)

theorem derivation_quadraticForm_eq_sum (X : Matrix (Fin m) (Fin m) ℂ) :
    Dv X (Q2 m n) = ∑ a, ∑ i, (MvPolynomial.X (a, i, false) * xyP X a i true + MvPolynomial.X (a, i, true) * xyP X a i false) := by
  simp only [Q2, map_sum, Derivation.leibniz, Dv_X, smul_eq_mul]

theorem vfX_eq_Dv (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    vfX c X P = Dv X P - C (c : ℂ) * Dv X (Q2 m n) * P := by
  rw [Dv_eq, derivation_quadraticForm_eq_sum, vfX]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  ring

theorem eval_xyP (X : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (xyP X a i b) =
      if b then star (matL X u a i) else matL X u a i := by
  cases b <;> simp [xyP, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord, matL_apply, star_sum, star_mul']

theorem gs_eq (c : ℝ) (u : Fin m → Fin n → ℂ) :
    gs c u = Complex.exp (-(c : ℂ) * MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (Q2 m n)) := by
  rw [gs]
  congr 1
  simp only [Q2, map_sum, map_mul, MvPolynomial.eval_X, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord]
  push_cast
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Finset.mul_sum]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {σ : Type*} [Fintype σ] (g : ℝ → σ → ℂ) (g' : σ → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (Q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0 := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun Q => HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0) Q ?_ ?_ ?_
  · intro a
    simpa using hasDerivAt_const (0 : ℝ) a
  · intro p q hp hq
    refine ((hp.fun_add hq).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [mul_add, Finset.sum_add_distrib]
    · exact Filter.Eventually.of_forall (fun t => by simp)
  · intro p k hp
    refine ((hp.fun_mul (hg k)).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib,
        apply_ite, Finset.sum_ite_eq]
      rw [add_comm]
      congr 1
      · ring
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    · exact Filter.Eventually.of_forall (fun t => by simp)

theorem hasDerivAt_curve (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) (fP c (vfX c X P) x) 0 := by
  set u : ℝ → (Fin m → Fin n → ℂ) := fun t => matL (NormedSpace.exp ((t : ℂ) • X)) x with hu
  have hu0 : u 0 = x := by simp [hu, matL_one]
  clear_value u
  rw [show (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) =
    fun t => fP c P (u t) by rw [hu]]
  let e : (Fin m → Fin n → ℂ) → Fin m × Fin n × Bool → ℂ :=
    fun v k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k v
  have hg : ∀ k, HasDerivAt (fun t => e (u t) k) (MvPolynomial.eval (e x) (xyP X k.1 k.2.1 k.2.2)) 0 := by
    rintro ⟨a, i, b⟩
    have hlin : HasDerivAt (fun t => u t a i) (matL X x a i) 0 := by
      have hs := HasDerivAt.fun_sum (u := Finset.univ)
        (fun c (_ : c ∈ Finset.univ) => (hasDerivAt_entry X a c).mul_const (x c i))
      simpa only [hu, matL_apply] using hs
    rw [eval_xyP]
    cases b
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin.star
  have hf : (fun t : ℝ => fP c P (u t)) = fun t => MvPolynomial.eval (e (u t)) P *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e (u t)) (Q2 m n)) := by
    funext t
    rw [fP, gs_eq]
    rfl
  have hx : fP c (vfX c X P) x = MvPolynomial.eval (e x) (vfX c X P) *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e x) (Q2 m n)) := by
    rw [fP, gs_eq]
    rfl
  rw [hf, hx, vfX_eq_Dv, Dv_eq X P, Dv_eq X (Q2 m n)]
  have hP := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg P
  have hQ := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg (Q2 m n)
  have H := hP.fun_mul ((hQ.const_mul (-(c : ℂ))).cexp)
  rw [hu0] at H
  refine H.congr_deriv ?_
  simp only [map_sub, map_mul, map_sum, MvPolynomial.eval_C]
  ring

end PositivityTheory.Rg.Sw.Glob.SchDH
