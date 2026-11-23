import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FSInv

open scoped ComplexConjugate
open MeasureTheory MvPolynomial CP

noncomputable section

theorem Orth.proof (hU : UnitaryInv.Statement) (hP : PairMk.Statement) : Orth.Statement := by
  intro N a b hab hdeg
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
    by_contra h
    exact hab (Finsupp.ext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have hA : monomial a (1 : ℂ) ∈ H0 N a.degree :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ rfl)
  have hB : monomial b (1 : ℂ) ∈ H0 N a.degree :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ hdeg.symm)

  set θ : ℝ := Real.pi / |(b k : ℝ) - a k| with hθ
  have key : ((b k : ℝ) - a k) * θ = Real.pi ∨ ((b k : ℝ) - a k) * θ = -Real.pi := by
    rcases lt_or_gt_of_ne hk with h | h
    · have h' : (0 : ℝ) < (b k : ℝ) - a k := by
        have : (a k : ℝ) < b k := by exact_mod_cast h
        linarith
      have hne : (b k : ℝ) - a k ≠ 0 := h'.ne'
      left
      rw [hθ, abs_of_pos h']
      field_simp
    · have h' : (b k : ℝ) - a k < 0 := by
        have : (b k : ℝ) < a k := by exact_mod_cast h
        linarith
      have hne : (b k : ℝ) - a k ≠ 0 := h'.ne
      right
      rw [hθ, abs_of_neg h']
      field_simp
  have hzmem : Complex.exp (θ * Complex.I) ∈ unitary ℂ := by
    rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  set z : unitary ℂ := ⟨Complex.exp (θ * Complex.I), hzmem⟩ with hz
  have hfac : conj ((z : ℂ) ^ a k) * (z : ℂ) ^ b k = -1 := by
    rw [hz, map_pow, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have harg : (a k : ℂ) * (θ * -Complex.I) + (b k : ℂ) * (θ * Complex.I) =
        (((b k : ℝ) - a k) * θ : ℝ) * Complex.I := by
      push_cast; ring
    rw [harg]
    rcases key with h | h <;> rw [h]
    · exact Complex.exp_pi_mul_I
    · rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num

  set w : Fin (N + 1) → unitary ℂ := fun i => if i = k then z else 1 with hw
  have hwv : ∀ i, ((w i : unitary ℂ) : ℂ) = if i = k then (z : ℂ) else 1 := fun i => by
    simp only [hw]; split_ifs <;> rfl
  have hwn : ∀ i, ‖((w i : unitary ℂ) : ℂ)‖ = 1 := fun i => by
    rw [hwv]; split_ifs
    · rw [hz]; exact Complex.norm_exp_ofReal_mul_I θ
    · exact norm_one
  have hprod : ∀ c : Fin (N + 1) →₀ ℕ, ∏ i, ((w i : unitary ℂ) : ℂ) ^ c i = (z : ℂ) ^ c k := by
    intro c
    simp only [hwv, ite_pow, one_pow, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hlin : ∀ v : Fin (N + 1) → ℂ,
      Matrix.toLin' (diagUnitary w : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) v =
        fun i => ((w i : unitary ℂ) : ℂ) * v i := fun v => by
    funext i
    simp [diagUnitary, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hev : ∀ (c : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ),
      eval (fun i => ((w i : unitary ℂ) : ℂ) * v i) (monomial c (1 : ℂ)) =
        (z : ℂ) ^ c k * eval v (monomial c 1) := fun c v => by
    rw [← hprod c, eval_monomial, eval_monomial, one_mul, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      ← Finset.prod_mul_distrib]
    simp only [mul_pow]
  have hnorm : ∀ v : Fin (N + 1) → ℂ, norm2 (fun i => ((w i : unitary ℂ) : ℂ) * v i) = norm2 v :=
    fun v => by simp only [norm2, normSq2, norm_mul, hwn, one_mul]

  set f := fsPair (N := N) a.degree (monomial a (1 : ℂ)) (monomial b 1) with hf
  have hpt : ∀ x, f (unitaryAct (diagUnitary w) x) = -f x := by
    intro x
    induction x using Projectivization.ind with
    | h v hv =>
      rw [hf, unitaryAct_mk, hP N _ _ _ hA hB, hP N _ _ _ hA hB, hlin, hev, hev, hnorm, map_mul]
      linear_combination (conj (eval v (monomial a (1 : ℂ))) * eval v (monomial b 1) /
        ((norm2 v ^ (2 * a.degree) : ℝ) : ℂ)) * hfac

  have hcont : Continuous f := by
    rw [ProjTopology.continuous_iff]
    have e : f ∘ Projectivization.mk' ℂ = fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} =>
        conj (eval v.1 (monomial a (1 : ℂ))) * eval v.1 (monomial b 1) /
          ((norm2 v.1 ^ (2 * a.degree) : ℝ) : ℂ) := by
      funext ⟨v, hv⟩
      exact hP N _ _ _ hA hB v hv
    rw [e]
    have hc2 : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
      Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
        (continuous_norm.comp (continuous_apply j)).pow 2)
    refine Continuous.div ?_ ?_ ?_
    · exact (Complex.continuous_conj.comp ((MvPolynomial.continuous_eval _).comp
        continuous_subtype_val)).mul ((MvPolynomial.continuous_eval _).comp continuous_subtype_val)
    · exact Complex.continuous_ofReal.comp ((hc2.comp continuous_subtype_val).pow _)
    · intro v
      exact_mod_cast (pow_pos (euclideanNorm_pos v.2) _).ne'

  have hmp := hU N (diagUnitary w)
  have hint : ∫ x, f x ∂fsMeasure N = ∫ x, f (unitaryAct (diagUnitary w) x) ∂fsMeasure N := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hcont.measurable.aestronglyMeasurable
  rw [show (fun x => f (unitaryAct (diagUnitary w) x)) = fun x => -f x from funext hpt,
    integral_neg] at hint
  show ∫ x, f x ∂fsMeasure N = 0
  linear_combination hint / 2

end

end GroundTheory.Heights₂.Heights.FSInv
