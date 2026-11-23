import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfB

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN adjH adjH_apply dg)

variable {k r : ℕ}

theorem sum_up {M : Type*} [AddCommMonoid M] (f : UP r → M) :
    ∑ a : Fin r, ∑ b : Fin r, (if h : a < b then f ⟨(a, b), h⟩ else 0) = ∑ p : UP r, f p := by
  classical
  rw [← Fintype.sum_prod_type' (fun a b => if h : a < b then f ⟨(a, b), h⟩ else 0)]
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij' (fun x _ => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩)
    (fun p _ => ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩⟩) ?_ ?_ ?_ ?_ ?_ <;> simp

theorem card_up : 2 * Fintype.card (UP r) + r = r * r := by
  classical
  have h1 := sum_up (M := ℕ) (r := r) (fun _ => 1)
  have h2 : ∑ a : Fin r, ∑ b : Fin r, (if h : b < a then (1 : ℕ) else 0) = Fintype.card (UP r) := by
    rw [Finset.sum_comm]
    simpa using h1
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h1
  have key : ∀ a b : Fin r, (if h : a < b then (1 : ℕ) else 0) + (if h : b < a then (1 : ℕ) else 0) +
      (if a = b then 1 else 0) = 1 := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
    · simp [h]
    · simp [h, not_lt.mpr h.le, (ne_of_lt h).symm]
  have htot : ∑ a : Fin r, ∑ b : Fin r, ((if h : a < b then (1 : ℕ) else 0) + (if h : b < a then (1 : ℕ) else 0) +
      (if a = b then 1 else 0)) = r * r := by
    simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  simp only [Finset.sum_add_distrib] at htot
  rw [h1, h2] at htot
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at htot
  omega

theorem card_CI : Fintype.card (CI k r) = r ^ 2 + r * k := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h := card_up (r := r)
  nlinarith [h]

theorem nsq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := Complex.normSq_conj z

theorem nsq_dD (j : Fin (k + 1)) : Complex.normSq (dD k j j) = 1 := by
  simp only [dD, Matrix.diagonal_apply_eq]
  split_ifs <;> simp

theorem nsq_A (x : CI k r → ℂ) (a b : Fin r) : Complex.normSq ((cA x - 1) a b) =
    if h : a < b then Complex.normSq (x (Sum.inl ⟨(a, b), h⟩)) else 0 := by
  simp only [Matrix.sub_apply, cA, Matrix.one_apply]
  by_cases h : a < b
  · simp [h, ne_of_lt h]
  · by_cases hab : a = b <;> simp [h, hab]

theorem nsq_K (x : CI k r → ℂ) (s : Fin r → ℝ) (a b : Fin r) : Complex.normSq (cK x s a b) =
    (if h : a < b then Complex.normSq (x (Sum.inr (Sum.inr ⟨(a, b), h⟩))) else 0) +
    (if h : b < a then Complex.normSq (x (Sum.inr (Sum.inr ⟨(b, a), h⟩))) else 0) +
    (if a = b then s a ^ 2 else 0) := by
  unfold cK
  by_cases h1 : a < b
  · have h2 : ¬ b < a := not_lt.mpr h1.le
    have h3 : a ≠ b := ne_of_lt h1
    simp [h1, h2, h3]
  · by_cases h2 : b < a
    · simp [h1, h2, (ne_of_lt h2).symm, Complex.normSq_neg, Complex.star_def, Complex.normSq_conj]
    · have h3 : a = b := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      subst h3
      simp [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
      ring

theorem sum_pos (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) :
    ∑ i, ∑ j, F i j = ∑ p : Ix k r, ∑ q : Ix k r, F (posE k r p) (posE k r q) := by
  rw [← Equiv.sum_comp (posE k r) (fun i => ∑ j, F i j)]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Equiv.sum_comp (posE k r) (fun j => F (posE k r p) j)]

section blocks

variable (t : (CI k r → ℂ) × (Fin r → ℝ))

theorem b_ee : ∑ a : Fin r, ∑ b : Fin r, Complex.normSq (Lm t (eI k r a) (eI k r b)) =
    ∑ p : UP r, Complex.normSq (t.1 (Sum.inl p)) := by
  have hL : ∀ a b : Fin r, Lm t (eI k r a) (eI k r b) = (cA t.1 - 1) a b := by
    intro a b
    unfold Lm
    rw [Matrix.sub_apply, mk_ee, mk_ee, Matrix.zero_apply, sub_zero]
  simp only [hL, nsq_A]
  exact sum_up (fun p => Complex.normSq (t.1 (Sum.inl p)))

theorem b_ss : ∑ a : Fin r, ∑ b : Fin r, Complex.normSq (Lm t (esI k r a) (esI k r b)) =
    ∑ p : UP r, Complex.normSq (t.1 (Sum.inl p)) := by
  have hL : ∀ a b : Fin r, Complex.normSq (Lm t (esI k r a) (esI k r b)) = Complex.normSq ((cA t.1 - 1) b a) := by
    intro a b
    unfold Lm
    rw [Matrix.sub_apply, mk_ss, mk_ss, Matrix.zero_apply, sub_zero, Matrix.neg_apply,
      Matrix.conjTranspose_apply, Complex.normSq_neg, nsq_star]
  simp only [hL, nsq_A]
  rw [Finset.sum_comm]
  exact sum_up (fun p => Complex.normSq (t.1 (Sum.inl p)))

theorem b_ws : ∑ j : Fin (k + 1), ∑ b : Fin r, Complex.normSq (Lm t (wI k r j) (esI k r b)) =
    ∑ a : Fin r, ∑ j : Fin (k + 1), Complex.normSq (t.1 (Sum.inr (Sum.inl (a, j)))) := by
  simp only [Lm_ws, Complex.normSq_neg, Complex.normSq_mul, nsq_dD, nsq_star, one_mul]
  exact Finset.sum_comm

theorem b_es : ∑ a : Fin r, ∑ b : Fin r, Complex.normSq (Lm t (eI k r a) (esI k r b)) =
    2 * ∑ p : UP r, Complex.normSq (t.1 (Sum.inr (Sum.inr p))) + ∑ a : Fin r, t.2 a ^ 2 := by
  have hL : ∀ a b : Fin r, Lm t (eI k r a) (esI k r b) = cK t.1 t.2 a b := by
    intro a b
    unfold Lm
    rw [Matrix.sub_apply, mk_es, mk_es, Matrix.zero_apply, sub_zero]
  simp only [hL, nsq_K, Finset.sum_add_distrib]
  have h1 := sum_up (fun p => Complex.normSq (t.1 (Sum.inr (Sum.inr p))))
  have h2 : ∑ a : Fin r, ∑ b : Fin r, (if h : b < a then Complex.normSq (t.1 (Sum.inr (Sum.inr ⟨(b, a), h⟩))) else 0) =
      ∑ p : UP r, Complex.normSq (t.1 (Sum.inr (Sum.inr p))) := by
    rw [Finset.sum_comm]
    exact sum_up (fun p => Complex.normSq (t.1 (Sum.inr (Sum.inr p))))
  have h3 : ∑ a : Fin r, ∑ b : Fin r, (if a = b then t.2 a ^ 2 else 0) = ∑ a : Fin r, t.2 a ^ 2 := by
    simp
  rw [h1, h2, h3]
  ring

end blocks

theorem normLm (t : (CI k r → ℂ) × (Fin r → ℝ)) :
    ∑ i, ∑ j, Complex.normSq (Lm t i j) = 2 * ∑ c, Complex.normSq (t.1 c) + ∑ a, t.2 a ^ 2 := by
  rw [sum_pos]
  simp only [Fintype.sum_sum_type, posE_apply, pos, Fintype.sum_prod_type, Finset.sum_add_distrib]
  simp only [b_ee, b_ss, b_ws, b_es]
  simp only [Lm_ew, Lm_we, Lm_ww, Lm_se, Lm_sw, Complex.normSq_zero, Finset.sum_const_zero, cB]
  ring

def xsL (Z : Mx k r) : CI k r → ℂ
  | Sum.inl p => Z (eI k r p.1.1) (eI k r p.1.2)
  | Sum.inr (Sum.inl q) => Z (eI k r q.1) (wI k r q.2)
  | Sum.inr (Sum.inr p) => Z (eI k r p.1.1) (esI k r p.1.2)

def ssL (Z : Mx k r) : Fin r → ℝ := fun a => (Z (eI k r a) (esI k r a)).im

theorem Lm_read {Z : Mx k r} (hZ : Z ∈ lieN k r) : Lm (xsL Z, ssL Z) = Z := by
  have hF := hZ.1
  have adj : ∀ i j, Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r i *
      star (Z (Formalism.QuantumDeterminants.WeylGroupFacts.tau k r j) (Formalism.QuantumDeterminants.WeylGroupFacts.tau k r i)) * Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r j +
      Z i j = 0 := by
    intro i j
    have := congrFun (congrFun hZ.2 i) j
    rwa [Matrix.add_apply, adjH_apply, Matrix.zero_apply] at this
  ext i j
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab]; rfl
    · rw [chart_matrix_lower _ (not_lt.1 hab)]
      have : b.val ≤ a.val := not_lt.1 hab
      exact (hF _ _ (by rw [dg_eI, dg_eI]; omega)).symm
  · rfl
  · unfold cK
    split_ifs with h1 h2
    · rfl
    · have := adj (eI k r a) (esI k r b)
      simp only [gtau_eI, gtau_esI, gsgn_eI, gsgn_esI, one_mul, mul_one] at this
      show -star (Z (eI k r b) (esI k r a)) = _
      linear_combination (-1 : ℂ) * this
    · have e : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst e
      have := adj (eI k r a) (esI k r a)
      simp only [gtau_eI, gtau_esI, gsgn_eI, gsgn_esI, one_mul, mul_one] at this
      have hre := congrArg Complex.re this
      simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at hre
      apply Complex.ext
      · simp [ssL]; linarith
      · simp [ssL]
  · exact (hF _ _ (by rw [dg_wI, dg_eI]; have := b.isLt; omega)).symm
  · exact (hF _ _ (by rw [dg_wI, dg_wI]; omega)).symm
  · have := adj (wI k r c) (esI k r b)
    simp only [gtau_wI, gtau_esI, gsgn_wI, gsgn_esI, mul_one] at this
    show -(dD k c c * star (Z (eI k r b) (wI k r c))) = _
    linear_combination (-1 : ℂ) * this
  · exact (hF _ _ (by rw [dg_esI, dg_eI]; have := a.isLt; have := b.isLt; omega)).symm
  · exact (hF _ _ (by rw [dg_esI, dg_wI]; have := a.isLt; omega)).symm
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab]
      have := adj (esI k r a) (esI k r b)
      simp only [gtau_esI, gsgn_esI, one_mul, mul_one] at this
      show -star (Z (eI k r b) (eI k r a)) = _
      linear_combination (-1 : ℂ) * this
    · rw [chart_matrix_lower _ (not_lt.1 hab), star_zero, neg_zero]
      have : a.val ≤ b.val := not_lt.1 hab
      exact (hF _ _ (by rw [dg_esI, dg_esI]; have := b.isLt; omega)).symm

theorem norm_RL_sq (X : Mx k r) :
    ‖Formalism.MainNotions.BridgeCSB.RL (k := k) (r := r) X‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (X i j) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Formalism.MainNotions.BridgeCSB.RL, Formalism.MainNotions.S.realifyFun, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
  ring

def cw : J k r → ℝ := Sum.elim (fun _ => (Real.sqrt 2)⁻¹) (fun _ => 1)

theorem cw_ne (j : J k r) : cw j ≠ 0 := by
  rcases j with j | j <;> simp [cw]

def dL : (J k r → ℝ) →ₗ[ℝ] (J k r → ℝ) := Matrix.toLin' (Matrix.diagonal cw)

theorem dL_apply (y : J k r → ℝ) (j : J k r) : dL y j = cw j * y j := by
  simp [dL, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem RL_LJ_mem (y : J k r → ℝ) : Formalism.MainNotions.BridgeCSB.RL (LJ y) ∈ Formalism.MainNotions.S.lieE (Nset k r) := by
  rw [Formalism.MainNotions.BridgeCSB.lieE_N]; exact ⟨LJ y, Lm_mem _, rfl⟩

def TL : (J k r → ℝ) →ₗ[ℝ] Formalism.MainNotions.S.lieE (Nset k r) :=
  (Formalism.MainNotions.BridgeCSB.RL ∘ₗ LJ).codRestrict _ RL_LJ_mem

def Psl : EuclideanSpace ℝ (J k r) →ₗ[ℝ] Formalism.MainNotions.S.lieE (Nset k r) :=
  TL ∘ₗ dL ∘ₗ (WithLp.linearEquiv 2 ℝ (J k r → ℝ)).toLinearMap

theorem norm_Psl (z : EuclideanSpace ℝ (J k r)) : ‖Psl z‖ = ‖z‖ := by
  have hs : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  set w : J k r → ℝ := WithLp.ofLp z with hw
  have hp : ∀ c, 2 * Complex.normSq ((toC (dL w)).1 c) =
      w (Sum.inl (Sum.inl c)) ^ 2 + w (Sum.inl (Sum.inr c)) ^ 2 := by
    intro c
    simp only [toC, dL_apply, cw, Sum.elim_inl, Complex.normSq_mk]
    linear_combination (2 * (w (Sum.inl (Sum.inl c)) ^ 2 + w (Sum.inl (Sum.inr c)) ^ 2)) * hs
  have hq : ∀ a, (toC (dL w)).2 a ^ 2 = w (Sum.inr a) ^ 2 := by
    intro a; simp [toC, dL_apply, cw]
  have h1 : ‖Psl z‖ ^ 2 = ‖z‖ ^ 2 := by
    change ‖Formalism.MainNotions.BridgeCSB.RL (k := k) (r := r) (Lm (toC (dL w)))‖ ^ 2 = _
    rw [norm_RL_sq, normLm, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Fintype.sum_sum_type (fun j : J k r => w j ^ 2),
      Fintype.sum_sum_type (fun j : CI k r ⊕ CI k r => w (Sum.inl j) ^ 2), ← Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_congr rfl (fun c _ => hp c), Finset.sum_congr rfl (fun a _ => hq a)]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem Psl_injective : Function.Injective (Psl (k := k) (r := r)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h := norm_Psl z
  rw [hz, norm_zero] at h
  exact norm_eq_zero.mp h.symm

theorem Psl_surjective : Function.Surjective (Psl (k := k) (r := r)) := by
  rintro ⟨v, hv⟩
  have hv' := hv
  rw [Formalism.MainNotions.BridgeCSB.lieE_N] at hv'
  obtain ⟨Z, hZ, rfl⟩ := hv'
  refine ⟨WithLp.toLp 2 (fun j => fromC (xsL Z, ssL Z) j / cw j), ?_⟩
  apply Subtype.ext
  change Formalism.MainNotions.BridgeCSB.RL (Lm (toC (dL (fun j => fromC (xsL Z, ssL Z) j / cw j)))) = _
  have e : dL (fun j => fromC (xsL (k := k) (r := r) Z, ssL Z) j / cw j) = fromC (xsL Z, ssL Z) := by
    funext j; rw [dL_apply, mul_div_cancel₀ _ (cw_ne j)]
  rw [e, toC_fromC, Lm_read hZ]

def Psi : EuclideanSpace ℝ (J k r) ≃ₗᵢ[ℝ] Formalism.MainNotions.S.lieE (Nset k r) :=
  { LinearEquiv.ofBijective Psl ⟨Psl_injective, Psl_surjective⟩ with norm_map' := norm_Psl }

theorem det_dL : LinearMap.det (dL (k := k) (r := r)) = ((Real.sqrt 2)⁻¹) ^ (2 * Fintype.card (CI k r)) := by
  rw [dL, LinearMap.det_toLin', Matrix.det_diagonal]
  simp [cw, Fintype.prod_sum_type, Finset.prod_const]
  ring

theorem inv_det_dL : (LinearMap.det (dL (k := k) (r := r)))⁻¹ = (2 : ℝ) ^ (r ^ 2 + r * k) := by
  rw [det_dL, card_CI, pow_mul, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp

theorem constant_change_holds : ConstStep := by
  intro k r
  have hTc : Continuous (TL (k := k) (r := r)) := LinearMap.continuous_of_finiteDimensional _
  have hdc : Continuous (dL (k := k) (r := r)) := LinearMap.continuous_of_finiteDimensional _
  refine ⟨TL, hTc.measurable, fun y => rfl, ?_⟩
  have h1 := (Psi (k := k) (r := r)).measurePreserving.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (J k r)).symm
  have e1 : (⇑(Psi (k := k) (r := r)) ∘ ⇑(MeasurableEquiv.toLp 2 (J k r → ℝ)).symm.symm) = ⇑TL ∘ ⇑dL := by
    funext y; rfl
  have hdet : LinearMap.det (dL (k := k) (r := r)) ≠ 0 := by
    intro h
    have := inv_det_dL (k := k) (r := r)
    rw [h, _root_.inv_zero] at this
    exact pow_ne_zero _ two_ne_zero this.symm
  rw [← h1.map_eq, e1, ← Measure.map_map hTc.measurable hdc.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.map_smul, inv_det_dL,
    abs_of_pos (by positivity)]

end Formalism.L2.SG.Pf.NcReal.JX.EC
