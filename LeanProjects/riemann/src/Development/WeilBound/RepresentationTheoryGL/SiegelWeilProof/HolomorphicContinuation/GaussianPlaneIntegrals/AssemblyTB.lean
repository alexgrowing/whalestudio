import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyTA

noncomputable section

open MeasureTheory MvPolynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA

variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem ext_all (hE : Ext) [Fintype A] [Fintype B] {p : PV ι A B} (hp : IsInv p) (M : Matrix ι ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (act M (M.map star) z) p = eval (act 1 (M.transpose * M.map star) z) p := by
  have key : ∀ M : Matrix ι ι ℂ, M.det ≠ 0 →
      eval (act M (M.map star) z) p = eval (act 1 (M.transpose * M.map star) z) p := by
    intro M hM
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have h1 : M⁻¹ * (M.transpose).transpose = 1 := by
      rw [Matrix.transpose_transpose]; exact Matrix.nonsing_inv_mul M hu
    have hq := hE ι A B p hp M⁻¹ M.transpose h1
    conv_lhs => rw [← hq]
    rw [eval_sub, act_act, Matrix.nonsing_inv_mul M hu]
  let F : ℂ → ℂ := fun t => eval (act (M + t • 1) ((M + t • 1).map star) z) p -
    eval (act 1 ((M + t • (1 : Matrix ι ι ℂ)).transpose * (M + t • 1).map star) z) p
  have c1 : Continuous fun t : ℂ => M + t • (1 : Matrix ι ι ℂ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hF : Continuous F :=
    (continuous_act_eval c1 (c1.matrix_map continuous_star) z p).sub
      (continuous_act_eval continuous_const (c1.matrix_transpose.mul (c1.matrix_map continuous_star)) z p)
  let S := {t : ℂ | (Matrix.charpoly (-M)).IsRoot t}
  have hS : S.Countable := (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-M)).ne_zero).countable
  have hd : Dense Sᶜ := hS.dense_compl ℂ
  have hz : Set.EqOn F (fun _ => 0) Sᶜ := by
    intro t ht
    have hdet : (M + t • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
      intro h0
      apply ht
      show (Matrix.charpoly (-M)).eval t = 0
      rw [Matrix.eval_charpoly]
      have e : Matrix.scalar ι t - -M = M + t • (1 : Matrix ι ι ℂ) := by
        rw [sub_neg_eq_add, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, add_comm]
      rw [e]; exact h0
    simp only [F, key _ hdet, sub_self]
  have h0 := congrFun (hF.ext_on hd continuous_const hz) 0
  simp only [F, zero_smul, add_zero] at h0
  exact sub_eq_zero.mp h0

theorem pair_inv {q : PV ι A B} (hq : q ∈ pairAlg ι A B) : IsInv q := by
  intro u hu
  have hu' : star u * u = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have hle : pairAlg ι A B ≤ AlgHom.equalizer (sub u (u.map star)) (AlgHom.id ℂ (PV ι A B)) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    show sub u (u.map star) _ = _
    apply MvPolynomial.funext
    intro z
    rw [eval_sub]
    simp only [map_sum, map_mul, eval_X, act, Sum.elim_inl, Sum.elim_inr, Matrix.map_apply, AlgHom.id_apply]
    have e : ∀ i, (∑ j, u i j * z (Sum.inl (j, a))) * (∑ l, star (u i l) * z (Sum.inr (l, b))) =
        ∑ j, ∑ l, (star (u i l) * u i j) * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) := by
      intro i
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have e2 : ∀ l, ∑ i, star (u i l) * u i j * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) =
        (star u * u) l j * (z (Sum.inl (j, a)) * z (Sum.inr (l, b))) := by
      intro l
      rw [Matrix.mul_apply, Finset.sum_mul]
      rfl
    simp_rw [e2, hu', Matrix.one_apply]
    simp
  exact hle hq

theorem gip_integrable (hP : Pos) [Fintype A] [Fintype B] (f g : PV ι A B) :
    Integrable (fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  have hG : Continuous fun z : (ι × A) ⊕ (ι × B) → ℂ => Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) := by fun_prop
  have hc : ∀ f g : PV ι A B, Continuous fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) := fun f g =>
    ((MvPolynomial.continuous_eval f).mul ((MvPolynomial.continuous_eval g).star)).mul hG
  have h1 : ∀ f : PV ι A B, Integrable (fun z : (ι × A) ⊕ (ι × B) → ℂ =>
      eval z f * star (eval z f) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro f
    by_cases hf : f = 0
    · subst hf; simp
    · by_contra hn
      have h := (hP ι A B 1 Matrix.PosSemidef.one f).2.2 Matrix.PosDef.one hf
      rw [sub_one_one, gip, integral_undef hn] at h
      simp at h
  refine Integrable.mono' ((h1 f).norm.add (h1 g).norm) (hc f g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [norm_mul, norm_star, Pi.add_apply]
  have ha := norm_nonneg (eval z f)
  have hb := norm_nonneg (eval z g)
  have hcn := norm_nonneg (Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)))
  nlinarith [mul_nonneg hcn (sq_nonneg (‖eval z f‖ - ‖eval z g‖)), mul_nonneg (mul_nonneg ha hb) hcn]

def gipL (hP : Pos) [Fintype A] [Fintype B] (p : PV ι A B) : PV ι A B →ₗ[ℂ] ℂ where
  toFun q := gip q p
  map_add' q1 q2 := by
    simp only [gip, map_add, add_mul]
    exact integral_add (gip_integrable hP q1 p) (gip_integrable hP q2 p)
  map_smul' c q := by
    simp only [gip, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    ring

theorem gipL_apply (hP : Pos) [Fintype A] [Fintype B] (p q : PV ι A B) : gipL hP p q = gip q p := rfl

theorem exists_points {σ : Type} [Fintype σ] (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ c : (σ → ℂ) →₀ ℂ, ∀ q : W, ℓ q = c.sum fun z a => a * eval z (q : MvPolynomial σ ℂ) := by
  let ev : (σ → ℂ) → Module.Dual ℂ W := fun z => (MvPolynomial.aeval z).toLinearMap.comp W.subtype
  have hev : ∀ z (q : W), ev z q = eval z (q : MvPolynomial σ ℂ) := fun z q => by
    simp [ev]
  set S := Submodule.span ℂ (Set.range ev)
  have hco : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : MvPolynomial σ ℂ) = 0 := MvPolynomial.funext fun z => by
      rw [map_zero, ← hev]
      exact hw _ (Submodule.subset_span ⟨z, rfl⟩)
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq S
    rw [hco, finrank_bot, add_zero] at h
    exact Submodule.eq_top_of_finrank_eq (h.trans (Subspace.dual_finrank_eq).symm)
  have hℓ : ℓ ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hℓ
  refine ⟨c, fun q => ?_⟩
  rw [← hc, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [LinearMap.smul_apply, hev, smul_eq_mul]

end PositivityTheory.Rg.Sw.FFTSteps.AsmA
