import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

noncomputable def mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) :
    Polynomial ℂ :=
  MvPolynomial.aeval (fun i => Polynomial.C (a i) + Polynomial.C (b i - a i) * Polynomial.X) q

theorem eval_mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) (t : ℂ) :
    (mvPolynomialOnLine q a b).eval t = MvPolynomial.eval (a + t • (b - a)) q := by
  unfold mvPolynomialOnLine
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr => rw [map_add, Polynomial.eval_add, hp, hr, map_add]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring

theorem finite_zeros_on_line {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ)
    (hb : MvPolynomial.eval b q ≠ 0) :
    {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}.Finite := by
  have hP : mvPolynomialOnLine q a b ≠ 0 := by
    intro h
    apply hb
    have := eval_mvPolynomialOnLine q a b 1
    simpa [h] using this.symm
  convert Polynomial.finite_setOfPred_isRoot hP using 1
  ext t
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, eval_mvPolynomialOnLine]

private theorem mvPolynomial_exists_eval_ne_zero {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (hq : q ≠ 0) :
    ∃ x : Fin d → ℂ, MvPolynomial.eval x q ≠ 0 := by
  by_contra h
  push Not at h
  exact hq (MvPolynomial.funext fun x => by simp [h x])

private theorem joinedIn_setOf_eval_ne_zero {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ)
    (ha : MvPolynomial.eval a q ≠ 0) (hb : MvPolynomial.eval b q ≠ 0) :
    JoinedIn {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} a b := by
  have hZ := finite_zeros_on_line q a b hb
  have hpc : IsPathConnected {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ :=
    hZ.countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)
  have h0 : (0 : ℂ) ∈ {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ := by simpa using ha
  have h1 : (1 : ℂ) ∈ {t : ℂ | MvPolynomial.eval (a + t • (b - a)) q = 0}ᶜ := by simpa using hb
  have hf : Continuous fun t : ℂ => a + t • (b - a) := by fun_prop
  have hj := (hpc.joinedIn 0 h0 1 h1).map hf
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at hj
  refine hj.mono ?_
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isConnected_and_dense_compl_hypersurface :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) := by
  intro d q hq
  obtain ⟨b, hb⟩ := mvPolynomial_exists_eval_ne_zero q hq
  refine ⟨(isPathConnected_iff.2 ⟨⟨b, hb⟩, fun x hx y hy => joinedIn_setOf_eval_ne_zero q x y hx hy⟩).isConnected,
    fun x => ?_⟩
  have hf : Continuous fun t : ℂ => x + t • (b - x) := by fun_prop
  have hlim : Tendsto (fun t : ℂ => x + t • (b - x)) (𝓝[≠] (0 : ℂ)) (𝓝 x) := by
    have := hf.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine mem_closure_of_tendsto hlim ?_
  have hZ := finite_zeros_on_line q x b hb
  have hcl : IsClosed ({t : ℂ | MvPolynomial.eval (x + t • (b - x)) q = 0} \ {0}) :=
    (hZ.subset Set.sdiff_subset).isClosed
  have e1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      t ∉ ({t : ℂ | MvPolynomial.eval (x + t • (b - x)) q = 0} \ {0}) :=
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp))
  have e2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
  filter_upwards [e1, e2] with t ht1 ht2
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_and, not_not] at ht1
  show MvPolynomial.eval (x + t • (b - x)) q ≠ 0
  exact fun h => ht2 (ht1 h)

end GlobalTheory
