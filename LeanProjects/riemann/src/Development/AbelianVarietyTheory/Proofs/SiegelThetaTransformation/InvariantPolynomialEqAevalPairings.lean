import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.PairingInvariants

theorem exists_unitary_diagonal_unitary {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g) :
    ∃ (u₁ u₂ : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℝ), u₁ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      u₂ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      g = u₁ * diagonal (fun i => cexp (a i)) * u₂ := by
  have hP : (gᴴ * g).PosDef := Matrix.PosDef.conjTranspose_mul_self g (Matrix.mulVec_injective_iff_isUnit.2 hg)
  have hH := hP.isHermitian
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUm : U ∈ Matrix.unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary.2
  have h1 : star U * (gᴴ * g) * U = diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [hU, Function.comp_def] using this
  have hpos : ∀ i, 0 < hH.eigenvalues i := hP.eigenvalues_pos
  let a : Fin n → ℝ := fun i => Real.log (hH.eigenvalues i) / 2
  have ha : ∀ i, cexp (-(a i : ℂ)) * ((hH.eigenvalues i : ℝ) : ℂ) * cexp (-(a i : ℂ)) = 1 := by
    intro i
    have : ((hH.eigenvalues i : ℝ) : ℂ) = cexp ((a i : ℂ) + a i) := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_exp]
      congr 1
      simp only [a, add_halves]
      rw [Real.exp_log (hpos i)]
    rw [this, ← Complex.exp_add, ← Complex.exp_add]
    simp
  refine ⟨g * U * diagonal (fun i => cexp (-(a i : ℂ))), star U, a, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hd : star (diagonal (fun i => cexp (-(a i : ℂ)))) = diagonal (fun i => cexp (-(a i : ℂ))) := by
      rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
      congr 1
      funext i
      simp [← Complex.exp_conj]
    rw [star_mul, star_mul, hd]
    calc _ = diagonal (fun i => cexp (-(a i : ℂ))) * (star U * (gᴴ * g) * U) * diagonal (fun i => cexp (-(a i : ℂ))) := by
            simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
      _ = 1 := by
            rw [h1, diagonal_mul_diagonal, diagonal_mul_diagonal]
            simp only [ha, diagonal_one]
  · exact Unitary.star_mem hUm
  · have h2 : diagonal (fun i => cexp (-(a i : ℂ))) * diagonal (fun i => cexp (a i : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal]
      simp [← Complex.exp_add]
    have h3 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hUm
    rw [Matrix.mul_assoc (g * U), h2, Matrix.mul_one, Matrix.mul_assoc, h3, Matrix.mul_one]

variable {T : Type} {n N : ℕ}

noncomputable def act (g h : T → Matrix (Fin n) (Fin n) ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    T × Bool × Fin n × Fin N → ℂ :=
  fun v => ∑ l, (if v.2.1 then g v.1 v.2.2.1 l else h v.1 v.2.2.1 l) * z (v.1, v.2.1, l, v.2.2.2)

theorem act_mul (g h g' h' : T → Matrix (Fin n) (Fin n) ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    act (fun t => g t * g' t) (fun t => h t * h' t) z = act g h (act g' h' z) := by
  funext ⟨t, b, k, j⟩
  cases b <;>
  · simp only [act, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, if_true, Bool.false_eq_true, if_false, mul_assoc]
    exact Finset.sum_comm

theorem act_diagonal (a b : T → Fin n → ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    act (fun t => diagonal (a t)) (fun t => diagonal (b t)) z =
      fun v => (if v.2.1 then a v.1 v.2.2.1 else b v.1 v.2.2.1) * z v := by
  funext ⟨t, c, k, j⟩
  cases c <;> simp [act, diagonal_apply]

theorem differentiable_eval {σ : Type} (p : MvPolynomial σ ℂ) (f : ℂ → σ → ℂ)
    (hf : ∀ v, Differentiable ℂ (fun c => f c v)) :
    Differentiable ℂ (fun c => MvPolynomial.eval (f c) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; exact hp.fun_add hq
  | mul_X p v hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.fun_mul (hf v)

theorem eval_act_diagonal (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z, MvPolynomial.eval (act u (fun t => (u t).map conj) z) p = MvPolynomial.eval z p)
    (a : T → Fin n → ℝ) (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval (act (fun t => diagonal fun i => cexp (a t i))
      (fun t => diagonal fun i => cexp (-(a t i : ℂ))) z) p = MvPolynomial.eval z p := by
  let F : ℂ → ℂ := fun c => MvPolynomial.eval (act (fun t => diagonal fun i => cexp (c * a t i))
      (fun t => diagonal fun i => cexp (-(c * a t i : ℂ))) z) p
  have hF : Differentiable ℂ F := by
    apply differentiable_eval
    rintro ⟨t, b, k, j⟩
    simp only [act_diagonal]
    cases b <;> simp only [if_true, Bool.false_eq_true, if_false] <;> fun_prop
  have hI : ∀ y : ℝ, F (y * I) = MvPolynomial.eval z p := by
    intro y
    rw [← hp (fun t => diagonal fun i => cexp (y * I * a t i)) ?_ z]
    · simp only [F]
      congr 3
      funext t
      rw [diagonal_map (by simp)]
      congr 1
      funext i
      simp [← Complex.exp_conj]
    · intro t
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      simp [← Complex.exp_conj, ← Complex.exp_add]
  have hfr : ∃ᶠ c in 𝓝[≠] (0 : ℂ), F c = (fun _ => MvPolynomial.eval z p) c := by
    have ht : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Continuous (fun y : ℝ => (y : ℂ) * I) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa using hy
    exact ht.frequently (Frequently.of_forall hI)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun c _ => hF.analyticAt c) analyticOnNhd_const hfr
  simpa [F] using congrFun this 1

theorem eval_act_of_mul_eq_one (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z, MvPolynomial.eval (act u (fun t => (u t).map conj) z) p = MvPolynomial.eval z p)
    (g h : T → Matrix (Fin n) (Fin n) ℂ) (hgh : ∀ t, g t * (h t)ᵀ = 1)
    (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p := by
  have hg : ∀ t, IsUnit (g t) := fun t => IsUnit.of_mul_eq_one _ (hgh t)
  choose u₁ u₂ a h₁ h₂ e using fun t => exists_unitary_diagonal_unitary (g t) (hg t)
  have eh : h = fun t => (u₁ t).map conj * diagonal (fun i => cexp (-(a t i : ℂ))) * (u₂ t).map conj := by
    funext t
    apply Matrix.transpose_injective
    apply (hg t).mul_left_cancel
    rw [hgh t, e t]
    have h2 : diagonal (fun i => cexp (a t i : ℂ)) * diagonal (fun i => cexp (-(a t i : ℂ))) = 1 := by
      rw [diagonal_mul_diagonal]
      simp [← Complex.exp_add]
    have k₁ : u₁ t * ((u₁ t).map conj)ᵀ = 1 := Matrix.mem_unitaryGroup_iff.1 (h₁ t)
    have k₂ : u₂ t * ((u₂ t).map conj)ᵀ = 1 := Matrix.mem_unitaryGroup_iff.1 (h₂ t)
    rw [transpose_mul, transpose_mul, diagonal_transpose, Matrix.mul_assoc _ (u₂ t), ← Matrix.mul_assoc (u₂ t), k₂, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), h2, Matrix.one_mul, k₁]
  have eg : g = fun t => u₁ t * diagonal (fun i => cexp (a t i)) * u₂ t := funext e
  rw [eh, eg, act_mul, act_mul, hp _ h₁, eval_act_diagonal p hp, hp _ h₂]

noncomputable def base (z : T × Bool × Fin n × Fin N → ℂ) : T × Bool × Fin n × Fin N → ℂ :=
  fun v => if v.2.1 then (if v.2.2.1.val = v.2.2.2.val then 1 else 0) else
    if h : v.2.2.1.val < N then
      ∑ l, z (v.1, false, l, v.2.2.2) * z (v.1, true, l, ⟨v.2.2.1.val, h⟩) else 0

theorem eq_at_zero_of_countable {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {S : Set ℂ} (hS : S.Countable) (h : ∀ c ∉ S, F c = G c) : F 0 = G 0 :=
  congrFun (Continuous.ext_on (hS.dense_compl ℂ) hF.continuous hG.continuous h) 0

theorem eval_eq_base_of_isUnit (hN : N ≤ n) (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ g h : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, g t * (h t)ᵀ = 1) →
      ∀ z, MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p)
    (G : T → Matrix (Fin n) (Fin n) ℂ) (hG : ∀ t, IsUnit (G t))
    (z : T × Bool × Fin n × Fin N → ℂ) (hz : ∀ t k j, z (t, true, k, j) = G t k (Fin.castLE hN j)) :
    MvPolynomial.eval z p = MvPolynomial.eval (base z) p := by
  have hinv : ∀ t, (G t)⁻¹ * G t = 1 := fun t =>
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hG t))
  set y := act (fun t => (G t)⁻¹) (fun t => (G t)ᵀ) z with hy
  have h1 : MvPolynomial.eval y p = MvPolynomial.eval z p := hp _ _ (by simpa using hinv) z
  have hyt : ∀ t k j, y (t, true, k, j) = if k.val = j.val then 1 else 0 := by
    intro t k j
    have := congrFun (congrFun (hinv t) k) (Fin.castLE hN j)
    simp only [hy, act, hz, if_true]
    rw [← Matrix.mul_apply, this, Matrix.one_apply]
    simp [Fin.ext_iff]
  let Y : ℂ → T × Bool × Fin n × Fin N → ℂ := fun c v =>
    if v.2.1 then y v else (if v.2.2.1.val < N then 1 else c) * y v
  have hY : Differentiable ℂ (fun c => MvPolynomial.eval (Y c) p) := by
    apply differentiable_eval
    intro v
    simp only [Y]
    split_ifs <;> fun_prop
  have h2 : MvPolynomial.eval (Y 0) p = MvPolynomial.eval y p := by
    refine eq_at_zero_of_countable hY (differentiable_const _) (Set.countable_singleton 0) ?_
    intro c hc
    have hc : c ≠ 0 := hc
    rw [← hp (fun _ => diagonal fun k => if k.val < N then 1 else c⁻¹)
      (fun _ => diagonal fun k => if k.val < N then 1 else c) ?_ y, act_diagonal]
    · congr 2
      funext ⟨t, b, k, j⟩
      cases b
      · simp [Y]
      · simp only [Y, if_true, hyt]
        have := j.2
        split_ifs <;> first | omega | simp
    · intro t
      rw [diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      split_ifs <;> simp [hc]
  rw [← h1, ← h2]
  congr 2
  funext ⟨t, b, k, j⟩
  cases b
  · simp only [Y, base, Bool.false_eq_true, if_false]
    split_ifs with h
    · simp only [hy, act, hz, Bool.false_eq_true, if_false, one_mul, transpose_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]
      rfl
    · simp
  · simp only [Y, base, if_true, hyt]

theorem eval_eq_base [Finite T] (hN : N ≤ n) (p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)
    (hp : ∀ g h : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, g t * (h t)ᵀ = 1) →
      ∀ z, MvPolynomial.eval (act g h z) p = MvPolynomial.eval z p)
    (z : T × Bool × Fin n × Fin N → ℂ) :
    MvPolynomial.eval z p = MvPolynomial.eval (base z) p := by
  let G : T → Matrix (Fin n) (Fin n) ℂ := fun t k l =>
    if h : l.val < N then z (t, true, k, ⟨l.val, h⟩) else 0
  let Z : ℂ → T × Bool × Fin n × Fin N → ℂ := fun c v =>
    z v - (if v.2.1 then (if v.2.2.1.val = v.2.2.2.val then 1 else 0) else 0) * c
  have hZ : ∀ v, Differentiable ℂ (fun c => Z c v) := by
    intro v
    simp only [Z]
    fun_prop
  have hZ0 : Z 0 = z := by
    funext v
    simp [Z]
  have := eq_at_zero_of_countable (F := fun c => MvPolynomial.eval (Z c) p)
    (G := fun c => MvPolynomial.eval (base (Z c)) p) (differentiable_eval p _ hZ)
    (differentiable_eval p _ ?_) (S := ⋃ t, spectrum ℂ (G t))
    (Set.countable_iUnion fun t => (Matrix.finite_spectrum (G t)).countable) ?_
  · simpa [hZ0] using this
  · intro v
    simp only [base]
    split_ifs
    · fun_prop
    · fun_prop
    · exact Differentiable.fun_sum fun l _ => (hZ _).fun_mul (hZ _)
    · fun_prop
  · intro c hc
    simp only [Set.mem_iUnion, not_exists, spectrum.mem_iff, not_not] at hc
    refine eval_eq_base_of_isUnit hN p hp (fun t => -(algebraMap ℂ _ c - G t))
      (fun t => (hc t).neg) _ ?_
    intro t k j
    rw [Matrix.neg_apply, Matrix.sub_apply, Matrix.algebraMap_matrix_apply]
    simp [Z, G, Fin.ext_iff]

end GlobalTheory.PairingInvariants

open GlobalTheory.PairingInvariants in

theorem GlobalTheory.invariant_polynomial_eq_aeval_pairings :
    ∀ (T : Type) [Fintype T] [DecidableEq T] (n N : ℕ), N ≤ n → ∀ p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ, (∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ z : T × Bool × Fin n × Fin N → ℂ, MvPolynomial.eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l else conj (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) p = MvPolynomial.eval z p) → ∃ s : MvPolynomial (T × Fin N × Fin N) ℂ, p = MvPolynomial.aeval (fun v : T × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)) s := by
  intro T _ _ n N hN p hp
  have key := eval_eq_base hN p (eval_act_of_mul_eq_one p hp)
  refine ⟨MvPolynomial.aeval (fun v : T × Bool × Fin n × Fin N =>
    if v.2.1 then (if v.2.2.1.val = v.2.2.2.val then 1 else 0) else
      if h : v.2.2.1.val < N then MvPolynomial.X (v.1, v.2.2.2, ⟨v.2.2.1.val, h⟩) else 0) p, ?_⟩
  apply MvPolynomial.funext
  intro z
  rw [key z, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, ← MvPolynomial.coe_aeval_eq_eval,
    ← MvPolynomial.coe_aeval_eq_eval]
  simp only [RingHom.coe_coe]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext v
  simp only [base]
  split_ifs <;> simp
