import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => (toMK k * pmat z * (toMK k)ᴴ) ab.1.1 ab.1.2

theorem adKAux_K_facts {ε : Fin n → Bool} (k : KG ε) :
    (toMK k)ᴴ * toMK k = 1 ∧ toMK k * Jm ε = Jm ε * toMK k ∧ (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
  obtain ⟨hu, hc⟩ := k.2
  have h1 : (toMK k)ᴴ * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have h2 : toMK k * (toMK k)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  have hc' : toMK k * Jm ε = Jm ε * toMK k := by
    first
      | exact hc
      | exact hc.symm
  refine ⟨h1, hc', ?_⟩
  calc (toMK k)ᴴ * Jm ε = (toMK k)ᴴ * Jm ε * (toMK k * (toMK k)ᴴ) := by rw [h2, Matrix.mul_one]
    _ = (toMK k)ᴴ * (Jm ε * toMK k) * (toMK k)ᴴ := by simp only [Matrix.mul_assoc]
    _ = (toMK k)ᴴ * (toMK k * Jm ε) * (toMK k)ᴴ := by rw [hc']
    _ = (toMK k)ᴴ * toMK k * Jm ε * (toMK k)ᴴ := by simp only [Matrix.mul_assoc]
    _ = Jm ε * (toMK k)ᴴ := by rw [h1, Matrix.one_mul]

theorem inP_conj₂ {ε : Fin n → Bool} (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) :
    inP ε (toMK k * X * (toMK k)ᴴ) := by
  obtain ⟨h1, h2, h3⟩ := adKAux_K_facts k
  obtain ⟨hG, hP⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at hG ⊢
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc toMK k * (Xᴴ * (toMK k)ᴴ) * Jm ε + Jm ε * (toMK k * X * (toMK k)ᴴ)
        = toMK k * Xᴴ * ((toMK k)ᴴ * Jm ε) + (Jm ε * toMK k) * X * (toMK k)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = toMK k * Xᴴ * (Jm ε * (toMK k)ᴴ) + (toMK k * Jm ε) * X * (toMK k)ᴴ := by rw [h3, ← h2]
      _ = toMK k * (Xᴴ * Jm ε + Jm ε * X) * (toMK k)ᴴ := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hG, Matrix.mul_zero, Matrix.zero_mul]
  · calc toMK k * X * (toMK k)ᴴ * Jm ε = toMK k * X * ((toMK k)ᴴ * Jm ε) := by simp only [Matrix.mul_assoc]
      _ = toMK k * X * (Jm ε * (toMK k)ᴴ) := by rw [h3]
      _ = toMK k * (X * Jm ε) * (toMK k)ᴴ := by simp only [Matrix.mul_assoc]
      _ = toMK k * (-(Jm ε * X)) * (toMK k)ᴴ := by rw [hP]
      _ = -((toMK k * Jm ε) * X * (toMK k)ᴴ) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by rw [h2]; simp only [Matrix.mul_assoc]

theorem pmat_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    pmat (adK k z) = toMK k * pmat z * (toMK k)ᴴ := pmat_coords _ (inP_conj₂ k _ (pmat_inP z))

theorem adKAux_hs_eq (M : Matrix (Fin n) (Fin n) ℂ) : hs M = (trace (M * Mᴴ)).re := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hs_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    hs (pmat (adK k z)) = hs (pmat z) := by
  rw [pmat_adK, adKAux_hs_eq, adKAux_hs_eq]
  obtain ⟨h1, -, -⟩ := adKAux_K_facts k
  congr 1
  have e : toMK k * pmat z * (toMK k)ᴴ * (toMK k * pmat z * (toMK k)ᴴ)ᴴ =
      toMK k * (pmat z * (pmat z)ᴴ) * (toMK k)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc toMK k * pmat z * (toMK k)ᴴ * (toMK k * ((pmat z)ᴴ * (toMK k)ᴴ))
        = toMK k * pmat z * ((toMK k)ᴴ * toMK k) * ((pmat z)ᴴ * (toMK k)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = toMK k * (pmat z * (pmat z)ᴴ) * (toMK k)ᴴ := by
          rw [h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm (toMK k * (pmat z * (pmat z)ᴴ)) (toMK k)ᴴ, ← Matrix.mul_assoc, h1,
    Matrix.one_mul]

theorem adKAux_pev_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : pev (adK k z) = pev z := by
  obtain ⟨h1, -, -⟩ := adKAux_K_facts k
  unfold pev
  rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff, pmat_adK, Matrix.charpoly_mul_comm,
    ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem jac_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : Jac (adK k z) = Jac z := by
  unfold Jac
  rw [adKAux_pev_adK]

theorem adKAux_shc_neg (u : ℝ) : shc (-u) = shc u := by
  unfold shc
  by_cases hu : u = 0
  · simp [hu]
  · rw [if_neg (neg_ne_zero.mpr hu), if_neg hu, Real.sinh_neg, neg_div_neg_eq]

theorem adKAux_shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with hu
  · exact one_pos
  · rcases lt_or_gt_of_ne hu with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h
    · exact div_pos (Real.sinh_pos_iff.mpr h) h

def adjointCompactJacobianFactor (x : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (x a - x b)

theorem adKAuxJ_pos (x : Fin n → ℝ) : 0 < adjointCompactJacobianFactor x := by
  exact Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => adKAux_shc_pos _

theorem adKAuxJ_sq (x : Fin n → ℝ) : adjointCompactJacobianFactor x ^ 2 = ∏ a, ∏ b, shc (x a - x b) := by
  have hsym : ∀ a b, shc (x a - x b) = shc (x b - x a) := fun a b => by
    rw [← adKAux_shc_neg, neg_sub]
  have h1 : ∀ a : Fin n, ∏ b, shc (x a - x b) =
      (∏ b ∈ univ.filter (fun b => a < b), shc (x a - x b)) *
        ∏ b ∈ univ.filter (fun b => b < a), shc (x a - x b) := by
    intro a
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun b => a < b)]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter fun b => ¬ a < b) (fun b => b < a)]
    have e1 : (univ.filter fun b : Fin n => ¬ a < b).filter (fun b => b < a) =
        univ.filter (fun b => b < a) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨not_lt.mpr h.le, h⟩
    have e2 : ∏ b ∈ (univ.filter fun b : Fin n => ¬ a < b).filter (fun b => ¬ b < a),
        shc (x a - x b) = 1 := by
      apply Finset.prod_eq_one
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hba : b = a := le_antisymm (not_lt.mp hb.1) (not_lt.mp hb.2)
      rw [hba, sub_self]
      simp [shc]
    rw [e1, e2, mul_one]
  have h2 : ∏ a, ∏ b ∈ univ.filter (fun b => b < a), shc (x a - x b) = adjointCompactJacobianFactor x := by
    rw [Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a => b < a)) (by intro a b; simp)]
    unfold adjointCompactJacobianFactor
    exact Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun a _ => hsym a b
  rw [sq, Finset.prod_congr rfl fun a _ => h1 a, Finset.prod_mul_distrib, h2]
  rfl

theorem adKAux_prod_mset (x : Fin n → ℝ) : ∏ a, ∏ b, shc (x a - x b) =
    ((univ.val.map x).map fun u => ((univ.val.map x).map fun v => shc (u - v)).prod).prod := by
  simp only [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]

theorem adKAuxJ_mset (x y : Fin n → ℝ) (h : univ.val.map x = univ.val.map y) : adjointCompactJacobianFactor x = adjointCompactJacobianFactor y := by
  have h2 : adjointCompactJacobianFactor x ^ 2 = adjointCompactJacobianFactor y ^ 2 := by
    rw [adKAuxJ_sq, adKAuxJ_sq, adKAux_prod_mset, adKAux_prod_mset, h]
  exact (pow_left_inj₀ (adKAuxJ_pos x).le (adKAuxJ_pos y).le two_ne_zero).mp h2

theorem adKAux_pmat_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : pmat (-z) = -pmat z := by
  ext a b
  simp only [pmat, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp

theorem adKAux_pev_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    univ.val.map (pev (-z)) = univ.val.map (fun a => -pev z a) := by
  have hA := pmat_isHermitian z
  have hch : (pmat (-z)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (((-pev z i : ℝ)) : ℂ)) := by
    rw [adKAux_pmat_neg]
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_neg, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
    simp [Matrix.charpoly_diagonal, pev, Matrix.diagonal_neg]
  have hr := (pmat_isHermitian (-z)).roots_charpoly_eq_eigenvalues
  rw [hch, Finset.prod_eq_multiset_prod] at hr
  rw [show (Multiset.map (fun i => Polynomial.X - Polynomial.C ((-pev z i : ℝ) : ℂ)) univ.val) =
      (univ.val.map (fun i => ((-pev z i : ℝ) : ℂ))).map (fun c => Polynomial.X - Polynomial.C c) by
      rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C] at hr
  have := congrArg (Multiset.map Complex.re) hr
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at this
  exact this.symm

theorem jac_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Jac (-z) = Jac z := by
  show adjointCompactJacobianFactor (pev (-z)) = adjointCompactJacobianFactor (pev z)
  rw [adKAuxJ_mset (pev (-z)) (fun a => -pev z a) (adKAux_pev_neg z)]
  unfold adjointCompactJacobianFactor
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  rw [show -pev z a - -pev z b = -(pev z a - pev z b) by ring, adKAux_shc_neg]

theorem adKAux_pmat_add {ε : Fin n → Bool} (z w : PCoord ε → ℂ) : pmat (z + w) = pmat z + pmat w := by
  ext a b
  simp only [pmat, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp [star_add]

theorem adKAux_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

def adjointCompactLinearAction {ε : Fin n → Bool} (k : KG ε) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := adK k
  map_add' z w := by
    funext ab
    simp only [adK, adKAux_pmat_add, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply]
  map_smul' c z := by
    funext ab
    simp only [adK, adKAux_pmat_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Pi.smul_apply,
      Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem adKAux_norm_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    ∑ ab, ‖adK k z ab‖ ^ 2 = ∑ ab, ‖z ab‖ ^ 2 := by
  have h := hs_adK k z
  rw [hs_pmat, hs_pmat] at h
  linarith

theorem adK_measurePreserving {ε : Fin n → Bool} (k : KG ε) :
    MeasurePreserving (adK k) (volume : Measure (PCoord ε → ℂ)) volume := by
  set f := adjointCompactLinearAction k with hf
  have hq : ∀ z, ∑ ab, ‖f z ab‖ ^ 2 = ∑ ab, ‖z ab‖ ^ 2 := adKAux_norm_adK k
  have hinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    have h0 := hq z
    rw [hz] at h0
    simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at h0
    funext ab
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖z i‖)).mp h0.symm ab (mem_univ _)
    simpa using this
  have hdet : LinearMap.det f ≠ 0 :=
    (((LinearMap.isUnit_iff_ker_eq_bot f).mpr hinj).map LinearMap.det).ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (PCoord ε → ℂ))) hdet
  have hcont : Continuous f := LinearMap.continuous_of_finiteDimensional f
  set S := {z : PCoord ε → ℂ | ∑ ab, ‖z ab‖ ^ 2 < 1} with hSdef
  have hSo : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have hpre : f ⁻¹' S = S := by
    ext z
    simp only [Set.mem_preimage, hSdef, Set.mem_ofPred_eq, hq]
  have hpos : volume S ≠ 0 := (hSo.measure_pos volume ⟨0, by simp [hSdef]⟩).ne'
  have hfin : volume S ≠ ⊤ := by
    have hsub : S ⊆ Metric.ball 0 1 := by
      intro z hz
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro ab
      have h1 : ‖z ab‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun i _ => sq_nonneg _) (mem_univ ab)
      have h2 : ∑ i, ‖z i‖ ^ 2 < 1 := hz
      nlinarith [norm_nonneg (z ab)]
    exact ((measure_mono hsub).trans_lt measure_ball_lt_top).ne
  have hS := congrArg (fun μ : Measure (PCoord ε → ℂ) => μ S) hmap
  rw [Measure.map_apply hcont.measurable hSo.measurableSet, hpre, Measure.smul_apply, smul_eq_mul] at hS
  have hc : ENNReal.ofReal |(LinearMap.det f)⁻¹| = 1 := by
    have h1 : 1 * volume S = ENNReal.ofReal |(LinearMap.det f)⁻¹| * volume S := by rw [one_mul]; exact hS
    exact ((ENNReal.mul_left_inj hpos hfin).mp h1).symm
  refine ⟨hcont.measurable, ?_⟩
  show Measure.map (⇑f) volume = volume
  rw [hmap, hc, one_smul]

end ReciprocityTheory.ChartRestriction.DS
