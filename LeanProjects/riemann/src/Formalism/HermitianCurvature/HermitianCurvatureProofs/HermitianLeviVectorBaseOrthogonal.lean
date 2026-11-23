import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x9

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

def iF (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

lemma e0_eq : e0 k r' = Pi.single (iF k r') 1 := rfl
lemma dual_base_vector_eq_single : es0 k r' = Pi.single (iL k r') 1 := rfl

lemma Hpk_first (j : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (iF k r') j = if j = iL k r' then 1 else 0 := by
  simp only [Hpk, iF, iL, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | (exfalso; simp only [Fin.val_mk] at *; omega)

lemma Hpk_last (i : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') i (iL k r') = if i = iF k r' then 1 else 0 := by
  simp only [Hpk, iF, iL, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | (exfalso; simp only [Fin.val_mk] at *; omega)

private lemma star_bvec' {m : ℕ} (p : Fin m) : star (bvec p) = bvec p := by
  ext j
  by_cases h : j = p
  · subst h; simp [bvec]
  · simp [bvec, Pi.single_apply, h]

private lemma herm_bvec_right_eq_mulVec_apply {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ) (p : Fin m) :
    herm H u (bvec p) = (H *ᵥ u) p := by
  unfold herm
  rw [star_bvec']
  simp [bvec, dotProduct, Pi.single_apply]

lemma hermitian_form_base_vector_right (u : Fin (2 * (1 + r') + k + 1) → ℂ) : herm (Hpk k (1 + r')) u (e0 k r') = u (iL k r') := by
  rw [show e0 k r' = bvec (iF k r') from rfl, herm_bvec_right_eq_mulVec_apply]
  simp [mulVec, dotProduct, Hpk_first]

lemma hermitian_dual_base_vector_left (v : Fin (2 * (1 + r') + k + 1) → ℂ) : herm (Hpk k (1 + r')) (es0 k r') v = star (v (iF k r')) := by
  rw [dual_base_vector_eq_single]
  simp [herm, dotProduct, mulVec, Pi.single_apply, Hpk_last]

lemma liftVec_first (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (iF k r') = 0 := by
  unfold liftVec
  rw [dif_neg]
  simp only [iF, Fin.val_mk]
  omega

lemma liftVec_last (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (iL k r') = 0 := by
  unfold liftVec
  rw [dif_neg]
  simp only [iL, Fin.val_mk]
  omega

lemma liftVec_mid (y : Fin (2 * r' + k + 1) → ℂ) (j : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' y (levPos k 1 r' j) = y j := by
  have hj := j.isLt
  unfold liftVec
  rw [dif_pos (show 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 from
    ⟨show 1 ≤ j.val + 1 by omega, show j.val + 1 < 2 * r' + k + 1 + 1 by omega⟩)]
  congr 1
  all_goals exact Fin.ext (show j.val + 1 - 1 = j.val by omega)

lemma levPos_ne_first (j : Fin (2 * r' + k + 1)) : levPos k 1 r' j ≠ iF k r' := by
  intro h
  have h2 : j.val + 1 = 0 := congrArg Fin.val h
  omega

lemma levPos_ne_last (j : Fin (2 * r' + k + 1)) : levPos k 1 r' j ≠ iL k r' := by
  intro h
  have hj := j.isLt
  have h2 : j.val + 1 = 2 * (1 + r') + k := congrArg Fin.val h
  omega

lemma first_ne_last : iF k r' ≠ iL k r' := by
  intro h
  have h2 : (0 : ℕ) = 2 * (1 + r') + k := congrArg Fin.val h
  omega

def xi (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')

def eta (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) : ℂ × HPar k r' :=
  (v (iL k r'), (fun j => v (levPos k 1 r' j) / v (iL k r'), (v (iF k r') / v (iL k r')).im))

lemma xi_last (p : ℂ × HPar k r') : xi k r' p (iL k r') = p.1 := by
  simp [xi, dual_base_vector_eq_single, e0_eq, liftVec_last, Pi.single_apply, (first_ne_last (k := k) (r' := r')).symm]

lemma hb_im (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) : (hb k r' y s).im = s := by
  simp [hb]

lemma eta_xi (p : ℂ × HPar k r') (hc : p.1 ≠ 0) : eta k r' (xi k r' p) = p := by
  obtain ⟨c, y, s⟩ := p
  simp only at hc
  have hL : xi k r' (c, y, s) (iL k r') = c := xi_last _
  have hM : ∀ j, xi k r' (c, y, s) (levPos k 1 r' j) = c * y j := by
    intro j
    simp [xi, dual_base_vector_eq_single, e0_eq, liftVec_mid, Pi.single_apply, levPos_ne_first, levPos_ne_last]
  have hF : xi k r' (c, y, s) (iF k r') = c * hb k r' y s := by
    simp [xi, dual_base_vector_eq_single, e0_eq, liftVec_first, Pi.single_apply, first_ne_last]
  simp only [eta, hL, hM, hF]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext j
    show c * y j / c = y j
    rw [mul_comm, mul_div_assoc, div_self hc, mul_one]
  · show (c * hb k r' y s / c).im = s
    rw [mul_comm, mul_div_assoc, div_self hc, mul_one, hb_im]

lemma heisenberg_dual_base_vector_formula (HA : HeisAct) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  unfold heis0
  rw [HA k r', hermitian_dual_base_vector_left, hermitian_dual_base_vector_left, liftVec_first]
  have he : e0 k r' (iF k r') = 1 := by rw [e0_eq]; exact Pi.single_eq_same _ _
  rw [he]
  simp only [star_zero, zero_smul, sub_zero, star_one, one_smul]
  abel

private lemma w0_apply_iF_col (c : ℂ) (i : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c i (iF k r') = if i = iL k r' then c else 0 := by
  have h0 : (iF k r').val = 0 := rfl
  show (if i.val = 0 ∧ (iF k r').val = 2 * (1 + r') + k then (star c)⁻¹
    else if i.val = 2 * (1 + r') + k ∧ (iF k r').val = 0 then c
    else if i = iF k r' ∧ 0 < i.val ∧ i.val < 2 * (1 + r') + k then (1 : ℂ) else 0) = _
  have h3 : ¬ (i = iF k r' ∧ 0 < i.val ∧ i.val < 2 * (1 + r') + k) := by
    rintro ⟨h1, h2, -⟩
    rw [h1, h0] at h2
    exact lt_irrefl 0 h2
  by_cases h : i = iL k r'
  · have hi : i.val = 2 * (1 + r') + k := by rw [h]; rfl
    rw [if_neg (by omega), if_pos ⟨hi, h0⟩, if_pos h]
  · have hi : i.val ≠ 2 * (1 + r') + k := fun h' => h (Fin.ext h')
    rw [if_neg (by omega), if_neg (by omega), if_neg h3, if_neg h]

lemma long_weyl_sends_base_to_dual (c : ℂ) : w0 k r' c *ᵥ e0 k r' = c • es0 k r' := by
  rw [e0_eq, dual_base_vector_eq_single]
  ext i
  have hcol : (w0 k r' c *ᵥ Pi.single (iF k r') 1) i = w0 k r' c i (iF k r') := by
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hcol, w0_apply_iF_col, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

def tau (k r' : ℕ) (p : ℂ × HPar k r') : Mt k (1 + r') := heis0 k r' p.2 * w0 k r' p.1

lemma parametrisation_base_vector_image (HA : HeisAct) (p : ℂ × HPar k r') : (Matrix.of (tau k r' p) : Mat k (1 + r')) *ᵥ e0 k r' = xi k r' p := by
  change (heis0 k r' p.2 * w0 k r' p.1) *ᵥ e0 k r' = xi k r' p
  rw [← mulVec_mulVec, long_weyl_sends_base_to_dual, mulVec_smul, heisenberg_dual_base_vector_formula HA]
  rfl

lemma liftVec_zero : liftVec k 1 r' 0 = 0 := by
  ext p
  simp [liftVec]

lemma heis_zero : heis0 k r' (0, 0) = 1 := by
  ext i j
  simp [heis0, heisG, liftVec_zero, hb, herm, vecMulVec_apply]

lemma lev_one : ιLev k 1 r' 1 = 1 := by
  ext p q
  simp only [ιLev, Matrix.one_apply]
  split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> first | rfl | (exfalso; omega) | (exfalso; simp only [Fin.val_mk] at *; omega)

lemma lev_mid (g : Mat k r') (i j : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  have hi := i.isLt
  have hj := j.isLt
  unfold ιLev levPos
  rw [dif_pos (show 1 ≤ i.val + 1 ∧ i.val + 1 < 2 * r' + k + 1 + 1 by omega),
    dif_pos (show 1 ≤ j.val + 1 ∧ j.val + 1 < 2 * r' + k + 1 + 1 by omega)]
  congr 1 <;> exact Fin.ext (by simp)

lemma mid_or (p : Fin (2 * (1 + r') + k + 1)) : (∃ i, p = levPos k 1 r' i) ∨ ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by
  by_cases h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · left
    exact ⟨⟨p.val - 1, by omega⟩, Fin.ext (show p.val = p.val - 1 + 1 by omega)⟩
  · right; exact h

lemma levPos_inj : Function.Injective (levPos k 1 r') := by
  intro a b h
  have h2 : a.val + 1 = b.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)

lemma levPos_mid (i : Fin (2 * r' + k + 1)) : 1 ≤ (levPos k 1 r' i).val ∧ (levPos k 1 r' i).val < 2 * r' + k + 1 + 1 := by
  have hi := i.isLt
  exact ⟨show 1 ≤ i.val + 1 by omega, show i.val + 1 < 2 * r' + k + 1 + 1 by omega⟩

private lemma iotaLev_levPos_apply_of_col_outside (g : Mat k r') (i : Fin (2 * r' + k + 1)) (m : Fin (2 * (1 + r') + k + 1))
    (hm : ¬ (1 ≤ m.val ∧ m.val < 2 * r' + k + 1 + 1)) : ιLev k 1 r' g (levPos k 1 r' i) m = 0 := by
  unfold ιLev
  rw [dif_pos (levPos_mid i), dif_neg hm]

private lemma iotaLev_apply_of_first_index_outside (g : Mat k r') (p : Fin (2 * (1 + r') + k + 1))
    (hp : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)) (m : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g p m = if p = m then 1 else 0 := by
  unfold ιLev
  rw [dif_neg hp]

lemma lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  ext p q
  rw [Matrix.mul_apply]
  rcases mid_or p with ⟨i, rfl⟩ | hp
  · rcases mid_or q with ⟨j, rfl⟩ | hq
    · rw [lev_mid, Matrix.mul_apply]
      have hsub : ∑ m, ιLev k 1 r' g (levPos k 1 r' i) m * ιLev k 1 r' h m (levPos k 1 r' j) =
          ∑ m ∈ Finset.univ.map ⟨levPos k 1 r', levPos_inj⟩,
            ιLev k 1 r' g (levPos k 1 r' i) m * ιLev k 1 r' h m (levPos k 1 r' j) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro m _ hm
        rcases mid_or m with ⟨l, rfl⟩ | hm'
        · exact absurd (Finset.mem_map_of_mem _ (Finset.mem_univ l)) hm
        · rw [iotaLev_levPos_apply_of_col_outside g i m hm', zero_mul]
      rw [hsub, Finset.sum_map]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp only [Function.Embedding.coeFn_mk]
      rw [lev_mid, lev_mid]
    · rw [iotaLev_levPos_apply_of_col_outside _ i q hq]
      symm
      apply Finset.sum_eq_zero
      intro m _
      rcases mid_or m with ⟨l, rfl⟩ | hm
      · rw [iotaLev_levPos_apply_of_col_outside h l q hq, mul_zero]
      · rw [iotaLev_levPos_apply_of_col_outside g i m hm, zero_mul]
  · rw [iotaLev_apply_of_first_index_outside (g * h) p hp q]
    simp only [iotaLev_apply_of_first_index_outside g p hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [iotaLev_apply_of_first_index_outside h p hp q]

lemma lev_inv (g : Mat k r') (hg : IsUnit g.det) : (ιLev k 1 r' g)⁻¹ = ιLev k 1 r' g⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← lev_mul, Matrix.mul_nonsing_inv _ hg, lev_one]

end Formalism.FourierDecayAlt.P.B2x9

namespace Formalism.FourierDecayAlt.P.B2x9

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r r' : ℕ}

def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det

theorem detF_cont : Continuous (detF (k := k) (r := r)) := by
  first
    | exact Continuous.matrix_det continuous_id
    | (unfold detF; fun_prop)
    | (unfold detF; continuity)
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := by
  first
    | exact Continuous.matrix_adjugate continuous_id
    | (unfold adjF; fun_prop)
    | (unfold adjF; continuity)

theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  show (Matrix.of x : Mat k r)⁻¹ = (Matrix.of x : Mat k r).det⁻¹ • (Matrix.of x : Mat k r).adjugate
  rw [Matrix.inv_def, Ring.inverse_eq_inv']

theorem invM_meas : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]
  first
    | exact (detF_cont.measurable.inv).smul adjF_cont.measurable
    | (apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j
       exact (detF_cont.measurable.inv).mul (((continuous_apply j).comp ((continuous_apply i).comp adjF_cont)).measurable))

theorem invM_contOn : ContinuousOn (invM : Mt k r → Mt k r) {x | detF x ≠ 0} := by
  rw [invM_smul]
  exact (detF_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjF_cont.continuousOn

theorem lmulM_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  first
    | exact continuous_const.matrix_mul continuous_id
    | (unfold lmulM; fun_prop)
    | (unfold lmulM; continuity)

theorem mulM_cont : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  first
    | exact continuous_fst.matrix_mul continuous_snd
    | (unfold mulM; fun_prop)
    | (unfold mulM; continuity)

theorem sigmaFinite_of_haar {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨@fun K hK => h.finite_compact K hK⟩
  infer_instance

lemma liftVec_cont : Continuous (liftVec k 1 r') := by
  apply continuous_pi
  intro p
  unfold liftVec
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [dif_pos hp]; exact continuous_apply _
  · simp only [dif_neg hp]; exact continuous_const

lemma herm_cont {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) : Continuous fun p : (Fin m → ℂ) × (Fin m → ℂ) => herm H p.1 p.2 := by
  first
    | (simp only [herm, dotProduct, mulVec]; fun_prop)
    | (simp only [herm, dotProduct, mulVec]; continuity)

lemma hb_cont : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := by
  have h1 : Continuous fun x : HPar k r' => herm (Hpk k r') x.1 x.1 :=
    (herm_cont (Hpk k r')).comp (by fun_prop : Continuous fun x : HPar k r' => (x.1, x.1))
  unfold hb
  exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp h1).neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

def heisF (k r' : ℕ) (x : HPar k r') : Mt k (1 + r') := heis0 k r' x

def w0F (k r' : ℕ) (c : ℂ) : Mt k (1 + r') := w0 k r' c

lemma heisenberg_map_continuous : Continuous (heisF k r') := by
  have hl : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := liftVec_cont.comp continuous_fst
  have hb' : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := hb_cont
  apply continuous_pi; intro i; apply continuous_pi; intro j
  have h1 : Continuous fun x : HPar k r' => herm (Hpk k (1 + r')) (bvec j) (liftVec k 1 r' x.1) :=
    (herm_cont (Hpk k (1 + r'))).comp (continuous_const.prodMk hl)
  have h2 : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 i := (continuous_apply i).comp hl
  show Continuous fun x : HPar k r' => heisG k r' (liftVec k 1 r' x.1) (hb k r' x.1 x.2) i j
  simp only [heisG, Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  exact (continuous_const.sub (continuous_const.mul h1)).add ((h2.add (hb'.mul continuous_const)).mul continuous_const)

lemma long_weyl_family_measurable : Measurable (w0F k r') := by
  apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j
  unfold w0F w0
  first
    | exact Measurable.ite (MeasurableSet.const _) (continuous_star.measurable.inv)
        (Measurable.ite (MeasurableSet.const _) measurable_id (Measurable.ite (MeasurableSet.const _) measurable_const measurable_const))
    | measurability

lemma levM_cont : Continuous (levM k r') := by
  apply continuous_pi; intro p; apply continuous_pi; intro q
  unfold levM ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq]
      first | exact continuous_apply_apply _ _ | fun_prop | continuity
    · simp only [dif_pos hp, dif_neg hq]; exact continuous_const
  · simp only [dif_neg hp]; exact continuous_const

lemma tau_meas : Measurable (tau k r') := by
  have h1 : Measurable fun p : ℂ × HPar k r' => heisF k r' p.2 := heisenberg_map_continuous.measurable.comp measurable_snd
  have h2 : Measurable fun p : ℂ × HPar k r' => w0F k r' p.1 := long_weyl_family_measurable.comp measurable_fst
  unfold tau
  apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum; intro l _
  exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp h1)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp h2))

lemma xi_cont : Continuous (xi k r') := by
  unfold xi
  have hl : Continuous fun p : ℂ × HPar k r' => liftVec k 1 r' p.2.1 :=
    liftVec_cont.comp (continuous_fst.comp continuous_snd)
  have hh : Continuous fun p : ℂ × HPar k r' => hb k r' p.2.1 p.2.2 := hb_cont.comp continuous_snd
  exact continuous_fst.smul ((continuous_const.add hl).add (hh.smul continuous_const))

lemma eta_meas : Measurable (eta k r') := by
  unfold eta
  first
    | fun_prop
    | exact (measurable_pi_apply _).prodMk ((measurable_pi_lambda _ fun j =>
        ((measurable_pi_apply _).div (measurable_pi_apply _))).prodMk
        (Complex.measurable_im.comp ((measurable_pi_apply _).div (measurable_pi_apply _))))
    | measurability

def Psi (k r' : ℕ) (p : ℂ × ((HPar k r' × HPar k r') × Mt k r')) : Mt k (1 + r') :=
  oneStep k r' p.2.1.1 p.1 (Matrix.of p.2.2) p.2.1.2

lemma Psi_meas : Measurable (Psi k r') := by
  have hm : ∀ {α : Type} [MeasurableSpace α] (f g : α → Mt k (1 + r')), Measurable f → Measurable g →
      Measurable fun p => mulM (f p, g p) :=
    fun f g hf hg => mulM_cont.measurable.comp (hf.prodMk hg)
  have hx : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => heisF k r' p.2.1.1 :=
    heisenberg_map_continuous.measurable.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hx' : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => heisF k r' p.2.1.2 :=
    heisenberg_map_continuous.measurable.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hw : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => w0F k r' p.1 :=
    long_weyl_family_measurable.comp measurable_fst
  have hg : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => levM k r' p.2.2 :=
    levM_cont.measurable.comp (measurable_snd.comp measurable_snd)
  have hi : Measurable fun p : ℂ × ((HPar k r' × HPar k r') × Mt k r') => invM (heisF k r' p.2.1.1) :=
    invM_meas.comp hx
  exact hm _ _ (hm _ _ (hm _ _ hi hw) hg) hx'

lemma heis_mem_P (hG : ClosedG) (SD : StabDecomp) (x : HPar k r') : heis0 k r' x ∈ P1set k r' := by
  have h1 : (1 : Mat k r') ∈ GV k r' := by
    first
      | exact (hG k r').one_mem
      | exact (hG k r').2.1
      | exact (hG k r').1.1
      | exact (hG k r').one
      | exact (hG k r').2.2.1
  rw [SD k r']
  unfold mulSet Hset
  show ∃ a ∈ Set.range (heis0 k r'), ∃ b ∈ ιLev k 1 r' '' GV k r', heis0 k r' x = a * b
  exact ⟨heis0 k r' x, ⟨x, rfl⟩, ιLev k 1 r' 1, ⟨1, h1, rfl⟩, by rw [lev_one, Matrix.mul_one]⟩

lemma lev_mem_P (SD : StabDecomp) (g₁ : Mat k r') (h : g₁ ∈ GV k r') : ιLev k 1 r' g₁ ∈ P1set k r' := by
  rw [SD k r']
  unfold mulSet Hset
  show ∃ a ∈ Set.range (heis0 k r'), ∃ b ∈ ιLev k 1 r' '' GV k r', ιLev k 1 r' g₁ = a * b
  exact ⟨1, ⟨(0, 0), heis_zero⟩, ιLev k 1 r' g₁, ⟨g₁, h, rfl⟩, (Matrix.one_mul _).symm⟩

lemma tau_eq_oneStep (HI : HeisInv) (p : ℂ × HPar k r') :
    (Matrix.of (tau k r' p) : Mat k (1 + r')) = oneStep k r' (-p.2.1, -p.2.2) p.1 1 (0, 0) := by
  change heis0 k r' p.2 * w0 k r' p.1 = oneStep k r' (-p.2.1, -p.2.2) p.1 1 (0, 0)
  unfold oneStep
  rw [HI k r', lev_one, heis_zero]
  simp

lemma tau_mem (hG : ClosedG) (HI : HeisInv) (OM : OneStepMem) (p : ℂ × HPar k r') (hc : p.1 ≠ 0) :
    (Matrix.of (tau k r' p) : Mat k (1 + r')) ∈ GV k (1 + r') := by
  have h1 : (1 : Mat k r') ∈ GV k r' := by
    first
      | exact (hG k r').one_mem
      | exact (hG k r').2.1
      | exact (hG k r').1.1
      | exact (hG k r').one
      | exact (hG k r').2.2.1
  rw [tau_eq_oneStep HI p]
  exact (OM k r' (-p.2.1, -p.2.2) (0, 0) p.1 hc 1 h1).1

lemma oneStep_eq (HI : HeisInv) (x x' : HPar k r') (c : ℂ) (g : Mat k r') :
    oneStep k r' x c g x' = (Matrix.of (tau k r' (c, (-x.1, -x.2))) : Mat k (1 + r')) * (ιLev k 1 r' g * heis0 k r' x') := by
  unfold oneStep
  rw [HI k r']
  change _ = heis0 k r' (-x.1, -x.2) * w0 k r' c * (ιLev k 1 r' g * heis0 k r' x')
  simp only [Matrix.mul_assoc]

lemma key (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (OC : OneStepCoord) (SD : StabDecomp)
    (hP : IsClosedSubgroup (P1set k r')) (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) (p : ℂ × HPar k r') (hc : p.1 ≠ 0)
    (hv : (a *ᵥ xi k r' p) (iL k r') ≠ 0) :
    ∃ q ∈ P1set k r', a * (Matrix.of (tau k r' p) : Mat k (1 + r')) =
      (Matrix.of (tau k r' (eta k r' (a *ᵥ xi k r' p))) : Mat k (1 + r')) * q := by
  set g : Mat k (1 + r') := a * (Matrix.of (tau k r' p) : Mat k (1 + r')) with hg
  have hgG : g ∈ GV k (1 + r') := (hG k (1 + r')).mul_mem _ ha _ (tau_mem hG HI OM p hc)
  have hge : g *ᵥ e0 k r' = a *ᵥ xi k r' p := by
    rw [hg, ← Matrix.mulVec_mulVec, parametrisation_base_vector_image HA]
  have hc' : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') ≠ 0 := by
    rw [hermitian_form_base_vector_right, hge]; exact hv
  obtain ⟨⟨x₁, g₁, x₂⟩, ⟨hg₁, hdec⟩, _⟩ := OC k r' g hgG hc'
  dsimp only at hg₁ hdec
  rw [oneStep_eq HI] at hdec
  have hq : ιLev k 1 r' g₁ * heis0 k r' x₂ ∈ P1set k r' :=
    hP.mul_mem _ (lev_mem_P SD g₁ hg₁) _ (heis_mem_P hG SD x₂)
  refine ⟨_, hq, ?_⟩
  have h2 : a *ᵥ xi k r' p = xi k r' (herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r'), (-x₁.1, -x₁.2)) := by
    rw [← hge]
    conv_lhs => rw [hdec]
    rw [← Matrix.mulVec_mulVec, hq.2, parametrisation_base_vector_image HA]
  rw [h2, eta_xi _ hc']
  exact hdec

end Formalism.FourierDecayAlt.P.B2x9

namespace Formalism.FourierDecayAlt.P.B2x9

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

def wt (k r' : ℕ) (c : ℂ) : ℝ≥0∞ := ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1)))

lemma wt_meas : Measurable (wt k r') := by
  unfold wt
  first
    | exact (continuous_norm.pow _).measurable.ennreal_ofReal
    | fun_prop
    | measurability

def mC (k r' : ℕ) : Measure ℂ := (volume : Measure ℂ).withDensity (wt k r')

def mCone (k r' : ℕ) : Measure (ℂ × HPar k r') := (mC k r').prod volume

lemma cone_eq : coneMeas k r' = (mCone k r').map (xi k r') := rfl

def muP (μG₁ : Measure (Mt k r')) : Measure (Mt k (1 + r')) := ((μHeis k r').prod (μG₁.map (levM k r'))).map mulM

def Ff (μP : Measure (Mt k (1 + r'))) (f : Mt k (1 + r') → ℝ≥0∞) (g : Mt k (1 + r')) : ℝ≥0∞ := ∫⁻ q, f (mulM (g, q)) ∂μP

lemma Ff_meas (μP : Measure (Mt k (1 + r'))) [SFinite μP] {f : Mt k (1 + r') → ℝ≥0∞} (hf : Measurable f) :
    Measurable (Ff μP f) := by
  unfold Ff
  exact Measurable.lintegral_prod_right' (hf.comp mulM_cont.measurable)

lemma ae_mem {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : ∀ᵐ x : Mt k r ∂μ, x ∈ (U : Set (Mt k r)) := by
  first
    | exact ae_iff.2 h.conc
    | (rw [ae_iff]; exact h.conc)
    | (rw [ae_iff]; simpa using h.conc)

lemma neg_HPar : (volume : Measure (HPar k r')).map Neg.neg = volume := by
  rw [Measure.volume_eq_prod]
  have : (Neg.neg : HPar k r' → HPar k r') = Prod.map Neg.neg Neg.neg := rfl
  rw [this, ← Measure.map_prod_map _ _ measurable_neg measurable_neg, Measure.map_neg_eq_self, Measure.map_neg_eq_self]

lemma swap (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (h : Mt k (1 + r') → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ q, h q ∂(muP μG₁) =
      ∫⁻ p : HPar k r' × Mt k r', h (mulM (levM k r' p.2, heisF k r' p.1)) ∂((volume : Measure (HPar k r')).prod μG₁) := by
  have := sigmaFinite_of_haar h₁
  have e1 : (μHeis k r').prod (μG₁.map (levM k r')) =
      ((volume : Measure (HPar k r')).prod μG₁).map (Prod.map (heisF k r') (levM k r')) :=
    Measure.map_prod_map _ _ heisenberg_map_continuous.measurable levM_cont.measurable
  have hPM : Measurable (Prod.map (heisF k r') (levM k r')) := heisenberg_map_continuous.measurable.prodMap levM_cont.measurable
  have hH : Measurable fun p : HPar k r' × Mt k r' => h (mulM (levM k r' p.2, heisF k r' p.1)) :=
    hh.comp (mulM_cont.measurable.comp ((levM_cont.measurable.comp measurable_snd).prodMk (heisenberg_map_continuous.measurable.comp measurable_fst)))
  have hNI : Measurable (Prod.map (Neg.neg : HPar k r' → HPar k r') (invM : Mt k r' → Mt k r')) :=
    measurable_neg.prodMap invM_meas
  have hae : ∀ᵐ p : HPar k r' × Mt k r' ∂((volume : Measure (HPar k r')).prod μG₁), p.2 ∈ (GV k r' : Set (Mt k r')) := by
    rw [ae_iff]
    have : {p : HPar k r' × Mt k r' | ¬ p.2 ∈ (GV k r' : Set (Mt k r'))} = Set.univ ×ˢ ((GV k r')ᶜ : Set (Mt k r')) := by
      ext p; simp only [Set.mem_prod, Set.mem_univ, true_and]; exact Iff.rfl
    rw [this, Measure.prod_prod, h₁.conc, mul_zero]
  calc ∫⁻ q, h q ∂(muP μG₁) = ∫⁻ q, h q ∂((muP μG₁).map invM) := by rw [HIv _ _ _ _ hP hμP]
    _ = ∫⁻ q, h (invM q) ∂(muP μG₁) := lintegral_map hh invM_meas
    _ = ∫⁻ p : HPar k r' × Mt k r', h (invM (mulM (heisF k r' p.1, levM k r' p.2))) ∂((volume : Measure (HPar k r')).prod μG₁) := by
        unfold muP
        rw [e1, Measure.map_map mulM_cont.measurable hPM]
        exact lintegral_map (f := fun q => h (invM q)) (hh.comp invM_meas) (mulM_cont.measurable.comp hPM)
    _ = ∫⁻ p : HPar k r' × Mt k r', (fun p' : HPar k r' × Mt k r' => h (mulM (levM k r' p'.2, heisF k r' p'.1)))
          (Prod.map (Neg.neg : HPar k r' → HPar k r') (invM : Mt k r' → Mt k r') p) ∂((volume : Measure (HPar k r')).prod μG₁) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with p hp
        congr 1
        show ((heis0 k r' p.1 * ιLev k 1 r' (Matrix.of p.2) : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) =
          ιLev k 1 r' ((Matrix.of p.2 : Mat k r')⁻¹ : Mat k r') * heis0 k r' (-p.1)
        rw [Matrix.mul_inv_rev, HI, lev_inv (Matrix.of p.2) ((hG k r').unit _ hp)]
        rfl
    _ = ∫⁻ p', h (mulM (levM k r' p'.2, heisF k r' p'.1))
          ∂(((volume : Measure (HPar k r')).prod μG₁).map (Prod.map (Neg.neg : HPar k r' → HPar k r') (invM : Mt k r' → Mt k r'))) :=
        (lintegral_map hH hNI).symm
    _ = _ := by
        rw [← Measure.map_prod_map _ _ measurable_neg invM_meas, neg_HPar, HIv _ _ _ _ (hG k r') h₁]

def II (μG₁ : Measure (Mt k r')) (f : Mt k (1 + r') → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ c : ℂ, wt k r' c * ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (Psi k r' (c, p))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁)

lemma inner_eq (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f)
    (c : ℂ) :
    ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (Psi k r' (c, p))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁) = ∫⁻ x : HPar k r', Ff (muP μG₁) f (tau k r' (c, x)) := by
  haveI := sigmaFinite_of_haar h₁
  haveI : SigmaFinite (muP μG₁) := sigmaFinite_of_haar hμP
  have hPsi : ∀ (x x' : HPar k r') (g : Mt k r'), Psi k r' (c, ((x, x'), g)) =
      mulM (tau k r' (c, (-x.1, -x.2)), mulM (levM k r' g, heisF k r' x')) := by
    intro x x' g
    show oneStep k r' x c (Matrix.of g) x' = _
    rw [oneStep_eq HI]
    rfl
  have hmF : Measurable fun p : (HPar k r' × HPar k r') × Mt k r' => f (Psi k r' (c, p)) :=
    hf.comp (Psi_meas.comp (measurable_const.prodMk measurable_id))
  have hG' : Measurable fun x : HPar k r' => Ff (muP μG₁) f (tau k r' (c, x)) :=
    (Ff_meas _ hf).comp (tau_meas.comp (measurable_const.prodMk measurable_id))
  have hin : ∀ x : HPar k r', ∫⁻ y : HPar k r', ∫⁻ g, f (Psi k r' (c, ((x, y), g))) ∂μG₁ ∂volume =
      Ff (muP μG₁) f (tau k r' (c, (-x.1, -x.2))) := by
    intro x
    have hh : Measurable fun q => f (mulM (tau k r' (c, (-x.1, -x.2)), q)) :=
      hf.comp (mulM_cont.comp (continuous_const.prodMk continuous_id)).measurable
    have hm2 : Measurable fun p : HPar k r' × Mt k r' => f (Psi k r' (c, ((x, p.1), p.2))) :=
      hmF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    calc ∫⁻ y : HPar k r', ∫⁻ g, f (Psi k r' (c, ((x, y), g))) ∂μG₁ ∂volume
        = ∫⁻ p : HPar k r' × Mt k r', f (Psi k r' (c, ((x, p.1), p.2)))
            ∂((volume : Measure (HPar k r')).prod μG₁) := (lintegral_prod _ hm2.aemeasurable).symm
      _ = ∫⁻ p : HPar k r' × Mt k r', f (mulM (tau k r' (c, (-x.1, -x.2)), mulM (levM k r' p.2, heisF k r' p.1)))
            ∂((volume : Measure (HPar k r')).prod μG₁) := by
          refine lintegral_congr (fun p => ?_)
          rw [hPsi]
      _ = Ff (muP μG₁) f (tau k r' (c, (-x.1, -x.2))) := (swap HIv hG HI μG₁ h₁ hP hμP _ hh).symm
  rw [lintegral_prod (fun p => f (Psi k r' (c, p))) hmF.aemeasurable,
    Measure.volume_eq_prod (α := HPar k r') (β := HPar k r'),
    lintegral_prod (fun xx : HPar k r' × HPar k r' => ∫⁻ g, f (Psi k r' (c, (xx, g))) ∂μG₁)
      hmF.lintegral_prod_right'.aemeasurable]
  simp only [hin]
  conv_rhs => rw [← neg_HPar]
  rw [lintegral_map (f := fun x => Ff (muP μG₁) f (tau k r' (c, x))) hG' measurable_neg]
  rfl

lemma II_eq (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f) :
    II μG₁ f = ∫⁻ p, Ff (muP μG₁) f (tau k r' p) ∂(mCone k r') := by
  haveI := sigmaFinite_of_haar h₁
  haveI : SigmaFinite (muP μG₁) := sigmaFinite_of_haar hμP
  have hm : Measurable fun p : ℂ × HPar k r' => Ff (muP μG₁) f (tau k r' p) := (Ff_meas _ hf).comp tau_meas
  unfold II mCone
  rw [lintegral_prod (fun p => Ff (muP μG₁) f (tau k r' p)) hm.aemeasurable]
  unfold mC
  rw [lintegral_withDensity_eq_lintegral_mul _ wt_meas hm.lintegral_prod_right']
  refine lintegral_congr (fun c => ?_)
  simp only [Pi.mul_apply]
  rw [inner_eq HIv hG HI μG₁ h₁ hP hμP f hf c]

end Formalism.FourierDecayAlt.P.B2x9

namespace Formalism.FourierDecayAlt.P.B2x9

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

lemma mC_zero : mC k r' {0} = 0 := by
  unfold mC
  rw [withDensity_apply _ (measurableSet_singleton 0)]
  first
    | exact setLIntegral_measure_zero _ _ (measure_singleton 0)
    | simp

lemma ae_ne : ∀ᵐ p : ℂ × HPar k r' ∂(mCone k r'), p.1 ≠ 0 := by
  rw [ae_iff]
  have hs : {p : ℂ × HPar k r' | ¬ p.1 ≠ 0} = {0} ×ˢ Set.univ := by ext p; simp
  rw [hs, mCone, Measure.prod_prod, mC_zero, zero_mul]

lemma mulVec_cont (a : Mat k (1 + r')) : Continuous fun v : Fin (2 * (1 + r') + k + 1) → ℂ => a *ᵥ v := by
  first
    | exact continuous_const.matrix_mulVec continuous_id
    | fun_prop
    | (simp only [mulVec, dotProduct]; fun_prop)
    | continuity

lemma ae_ne' (CI : ConeInv) (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) :
    ∀ᵐ p : ℂ × HPar k r' ∂(mCone k r'), (a *ᵥ xi k r' p) (iL k r') ≠ 0 := by
  have hx : Measurable (xi k r') := xi_cont.measurable
  have ha' : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => a *ᵥ v := (mulVec_cont a).measurable
  have hS : MeasurableSet {v : Fin (2 * (1 + r') + k + 1) → ℂ | v (iL k r') ≠ 0} := by
    first
      | exact (measurableSet_eq_fun (measurable_pi_apply _) measurable_const).compl
      | measurability
  have h1 : ∀ᵐ v ∂(coneMeas k r'), v (iL k r') ≠ 0 := by
    rw [cone_eq, ae_map_iff hx.aemeasurable hS]
    filter_upwards [ae_ne (k := k) (r' := r')] with p hp
    rwa [xi_last]
  have h2 : ∀ᵐ v ∂(coneMeas k r'), (a *ᵥ v) (iL k r') ≠ 0 := by
    rw [← CI k r' a ha] at h1
    exact (ae_map_iff ha'.aemeasurable hS).1 h1
  rw [cone_eq] at h2
  exact (ae_map_iff hx.aemeasurable (ha' hS)).1 h2

lemma Ff_right (μP : Measure (Mt k (1 + r'))) (hμP : IsHaarOn (P1set k r') μP) {f : Mt k (1 + r') → ℝ≥0∞} (hf : Measurable f)
    (g q : Mt k (1 + r')) (hq : q ∈ (P1set k r' : Set (Mt k (1 + r')))) : Ff μP f (mulM (g, q)) = Ff μP f g := by
  unfold Ff
  have hmeas : Measurable fun q' : Mt k (1 + r') => f (mulM (g, q')) :=
    hf.comp (mulM_cont.comp (continuous_const.prodMk continuous_id)).measurable
  calc ∫⁻ q', f (mulM (mulM (g, q), q')) ∂μP
      = ∫⁻ q', f (mulM (g, lmulM q q')) ∂μP := by
        congr 1; funext q'; congr 1
        show Matrix.of g * Matrix.of q * Matrix.of q' = Matrix.of g * (Matrix.of q * Matrix.of q')
        exact Matrix.mul_assoc _ _ _
    _ = ∫⁻ q', f (mulM (g, q')) ∂(μP.map (lmulM q)) := (lintegral_map hmeas (lmulM_cont q).measurable).symm
    _ = ∫⁻ q', f (mulM (g, q')) ∂μP := by rw [hμP.left q hq]

lemma II_inv (HIv : HaarInv) (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (OC : OneStepCoord) (CI : ConeInv)
    (SD : StabDecomp) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f)
    (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) : II μG₁ (fun g => f (lmulM a g)) = II μG₁ f := by
  haveI := sigmaFinite_of_haar h₁
  haveI : SigmaFinite (muP μG₁) := sigmaFinite_of_haar hμP
  have hfa : Measurable fun g => f (lmulM a g) := hf.comp (lmulM_cont a).measurable
  rw [II_eq HIv hG HI μG₁ h₁ hP hμP _ hfa, II_eq HIv hG HI μG₁ h₁ hP hμP f hf]
  have hE : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => Ff (muP μG₁) f (tau k r' (eta k r' v)) :=
    (Ff_meas _ hf).comp (tau_meas.comp eta_meas)
  have e1 : ∀ x, Ff (muP μG₁) (fun g => f (lmulM a g)) x = Ff (muP μG₁) f (lmulM a x) := by
    intro x
    simp only [Ff]
    congr 1; funext q'; congr 1
    show a * (Matrix.of x * Matrix.of q') = a * Matrix.of x * Matrix.of q'
    exact (Matrix.mul_assoc _ _ _).symm
  have step1 : ∀ᵐ p ∂(mCone k r'), Ff (muP μG₁) (fun g => f (lmulM a g)) (tau k r' p) =
      Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ xi k r' p))) := by
    filter_upwards [ae_ne (k := k) (r' := r'), ae_ne' CI a ha] with p hc hv
    obtain ⟨q, hq, hq'⟩ := key hG HA HI OM OC SD hP a ha p hc hv
    have hk : lmulM a (tau k r' p) = mulM (tau k r' (eta k r' (a *ᵥ xi k r' p)), q) := hq'
    rw [e1, hk, Ff_right _ hμP hf _ _ hq]
  rw [lintegral_congr_ae step1]
  have hxi : Measurable (xi k r') := xi_cont.measurable
  have hav : Measurable fun v : Fin (2 * (1 + r') + k + 1) → ℂ => a *ᵥ v := (mulVec_cont a).measurable
  calc ∫⁻ p, Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ xi k r' p))) ∂(mCone k r')
      = ∫⁻ v, Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ v))) ∂(coneMeas k r') := by
        rw [cone_eq, lintegral_map (f := fun v => Ff (muP μG₁) f (tau k r' (eta k r' (a *ᵥ v)))) (hE.comp hav) hxi]
    _ = ∫⁻ v, Ff (muP μG₁) f (tau k r' (eta k r' v)) ∂(coneMeas k r') := by
        conv_rhs => rw [← CI k r' a ha]
        rw [lintegral_map (f := fun v => Ff (muP μG₁) f (tau k r' (eta k r' v))) hE hav]
    _ = ∫⁻ p, Ff (muP μG₁) f (tau k r' (eta k r' (xi k r' p))) ∂(mCone k r') := by
        rw [cone_eq, lintegral_map (f := fun v => Ff (muP μG₁) f (tau k r' (eta k r' v))) hE hxi]
    _ = ∫⁻ p, Ff (muP μG₁) f (tau k r' p) ∂(mCone k r') := by
        apply lintegral_congr_ae
        filter_upwards [ae_ne (k := k) (r' := r')] with p hc
        rw [eta_xi p hc]

lemma Ff_ind (μP : Measure (Mt k (1 + r'))) (S : Set (Mt k (1 + r'))) (hS : MeasurableSet S) (g : Mt k (1 + r')) :
    Ff μP (S.indicator 1) g = μP ((fun q => mulM (g, q)) ⁻¹' S) := by
  unfold Ff
  have hm : MeasurableSet ((fun q => mulM (g, q)) ⁻¹' S) :=
    (mulM_cont.comp (continuous_const.prodMk continuous_id)).measurable hS
  rw [← lintegral_indicator_one hm]
  first | rfl | (congr 1; ext q; simp [Set.indicator_apply])

def nu (μG₁ : Measure (Mt k r')) : Measure (Mt k (1 + r')) :=
  ((mC k r').prod ((volume : Measure (HPar k r' × HPar k r')).prod μG₁)).map (Psi k r')

lemma lintegral_nu (μG₁ : Measure (Mt k r')) [SFinite μG₁] (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂(nu μG₁) = II μG₁ f := by
  unfold nu II
  rw [lintegral_map hf Psi_meas]
  first
    | rw [lintegral_prod (fun a => f (Psi k r' a)) ((hf.comp Psi_meas).aemeasurable)]
    | rw [lintegral_prod _ (hf.comp Psi_meas).aemeasurable]
  unfold mC
  rw [lintegral_withDensity_eq_lintegral_mul _ wt_meas]
  · rfl
  · exact (hf.comp Psi_meas).lintegral_prod_right'

lemma nu_apply (μG₁ : Measure (Mt k r')) [SFinite μG₁] (S : Set (Mt k (1 + r'))) (hS : MeasurableSet S) :
    nu μG₁ S = II μG₁ (S.indicator 1) := by
  rw [← lintegral_nu μG₁ _ (measurable_one.indicator hS), lintegral_indicator_one hS]

lemma nu_left (HIv : HaarInv) (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (OC : OneStepCoord) (CI : ConeInv)
    (SD : StabDecomp) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁))
    (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) : (nu μG₁).map (lmulM a) = nu μG₁ := by
  haveI := sigmaFinite_of_haar h₁
  ext S hS
  rw [Measure.map_apply (lmulM_cont a).measurable hS, nu_apply _ _ ((lmulM_cont a).measurable hS),
    nu_apply _ _ hS]
  have hi : (lmulM a ⁻¹' S).indicator (1 : Mt k (1 + r') → ℝ≥0∞) = fun g => S.indicator 1 (lmulM a g) := by
    funext g
    first | rfl | simp [Set.indicator_apply]
  rw [hi]
  exact II_inv HIv hG HA HI OM OC CI SD μG₁ h₁ hP hμP _ (measurable_one.indicator hS) a ha

lemma nu_conc (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (OM : OneStepMem)
    (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) :
    nu μG₁ ((GV k (1 + r'))ᶜ : Set (Mt k (1 + r'))) = 0 := by
  haveI := sigmaFinite_of_haar h₁
  have hGc : @IsClosed (Mt k (1 + r')) _ (GV k (1 + r')) := by
    have hG' := hG k (1 + r')
    first | exact hG'.1 | exact hG'.isClosed | exact hG'.closed | exact hG'.2
  rw [nu_apply _ _ ?hS]
  swap
  · exact hGc.measurableSet.compl
  unfold II
  refine (lintegral_congr (fun c => ?_)).trans lintegral_zero
  try dsimp only
  by_cases hc : c = 0
  · subst hc
    have hw : wt k r' 0 = 0 := by
      unfold wt
      rw [norm_zero, zero_pow (by omega), ENNReal.ofReal_zero]
    rw [hw, zero_mul]
  · have hae : ∀ᵐ p ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁), p.2 ∈ (GV k r' : Set (Mt k r')) := by
      rw [ae_iff]
      refine measure_mono_null (t := Set.univ ×ˢ {g : Mt k r' | g ∉ (GV k r' : Set (Mt k r'))})
        (fun p hp => ⟨Set.mem_univ _, hp⟩) ?_
      rw [Measure.prod_prod]
      exact mul_eq_zero_of_right _ h₁.conc
    refine mul_eq_zero_of_right _ ?_
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae] with p hp
    have hmem := (OM k r' p.1.1 p.1.2 c hc (Matrix.of p.2) hp).1
    classical
    rw [Set.indicator_apply, if_neg (fun hn => hn hmem)]

lemma evalE_cont : Continuous fun g : Mt k (1 + r') => (Matrix.of g : Mat k (1 + r')) *ᵥ e0 k r' := by
  first
    | exact continuous_id.matrix_mulVec continuous_const
    | fun_prop
    | (simp only [mulVec, dotProduct]; fun_prop)
    | continuity

lemma nu_fin (HIv : HaarInv) (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (CF : ConeFinite)
    (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁))
    (K : Set (Mt k (1 + r'))) (hK : IsCompact K) : nu μG₁ K < ∞ := by
  have := sigmaFinite_of_haar h₁
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set K' : Set (Mt k (1 + r')) := K ∩ (GV k (1 + r') : Set (Mt k (1 + r'))) with hK'
  have hK'c : IsCompact K' := hK.inter_right (hG k (1 + r')).closed
  have hinvc : IsCompact ((invM : Mt k (1 + r') → Mt k (1 + r')) '' K') :=
    hK'c.image_of_continuousOn (invM_contOn.mono fun x hx => ((hG k (1 + r')).unit x hx.2).ne_zero)
  set D : Set (Mt k (1 + r')) := mulM '' (((invM : Mt k (1 + r') → Mt k (1 + r')) '' K') ×ˢ K') with hD
  have hDc : IsCompact D := (hinvc.prod hK'c).image mulM_cont
  set Ke : Set (Fin (2 * (1 + r') + k + 1) → ℂ) := (fun g : Mt k (1 + r') => (Matrix.of g : Mat k (1 + r')) *ᵥ e0 k r') '' K with hKe
  have hKec : IsCompact Ke := hK.image evalE_cont
  have hKem : MeasurableSet Ke := hKec.isClosed.measurableSet
  have bound : ∀ p : ℂ × HPar k r', p.1 ≠ 0 →
      Ff (muP μG₁) (K.indicator 1) (tau k r' p) ≤ muP μG₁ D * (xi k r' ⁻¹' Ke).indicator 1 p := by
    intro p hp
    rw [Ff_ind _ _ hKm]
    set T : Set (Mt k (1 + r')) := (fun q => mulM (tau k r' p, q)) ⁻¹' K with hT
    have hgG := tau_mem hG HI OM p hp
    have hT' : muP μG₁ (T ∩ (P1set k r' : Set (Mt k (1 + r')))) = muP μG₁ T := measure_inter_conull hμP.conc
    rw [← hT']
    by_cases hne : (T ∩ (P1set k r' : Set (Mt k (1 + r')))).Nonempty
    · obtain ⟨q₀, hq₀T, hq₀P⟩ := hne
      have hq₀K' : mulM (tau k r' p, q₀) ∈ K' := ⟨hq₀T, (hG k (1 + r')).mul_mem _ hgG _ hq₀P.1⟩
      have hxi : xi k r' p ∈ Ke := by
        refine ⟨mulM (tau k r' p, q₀), hq₀T, ?_⟩
        show ((Matrix.of (tau k r' p) : Mat k (1 + r')) * (Matrix.of q₀ : Mat k (1 + r'))) *ᵥ e0 k r' = _
        rw [← Matrix.mulVec_mulVec]
        have : (Matrix.of q₀ : Mat k (1 + r')) *ᵥ e0 k r' = e0 k r' := hq₀P.2
        rw [this, parametrisation_base_vector_image HA]
      rw [Set.indicator_of_mem (show p ∈ xi k r' ⁻¹' Ke from hxi)]
      simp only [Pi.one_apply, mul_one]
      have hq₀inv : ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) ∈ P1set k r' := hP.inv_mem _ hq₀P
      calc muP μG₁ (T ∩ (P1set k r' : Set (Mt k (1 + r'))))
          ≤ muP μG₁ (lmulM ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) ⁻¹' D) := by
            refine measure_mono ?_
            rintro q ⟨hqT, hqP⟩
            refine ⟨(invM (mulM (tau k r' p, q₀)), mulM (tau k r' p, q)), ⟨⟨_, hq₀K', rfl⟩, ⟨hqT, (hG k (1 + r')).mul_mem _ hgG _ hqP.1⟩⟩, ?_⟩
            show (((Matrix.of (tau k r' p) : Mat k (1 + r')) * (Matrix.of q₀ : Mat k (1 + r')))⁻¹ : Mat k (1 + r')) *
              ((Matrix.of (tau k r' p) : Mat k (1 + r')) * (Matrix.of q : Mat k (1 + r'))) =
              ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r')) * (Matrix.of q : Mat k (1 + r'))
            rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.of (tau k r' p) : Mat k (1 + r')),
              Matrix.nonsing_inv_mul _ ((hG k (1 + r')).unit _ hgG), Matrix.one_mul]
        _ = (muP μG₁).map (lmulM ((Matrix.of q₀ : Mat k (1 + r'))⁻¹ : Mat k (1 + r'))) D :=
            (Measure.map_apply (lmulM_cont _).measurable hDc.isClosed.measurableSet).symm
        _ = muP μG₁ D := by rw [hμP.left _ hq₀inv]
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
      exact bot_le
  rw [nu_apply _ _ hKm, II_eq HIv hG HI μG₁ h₁ hP hμP _ (measurable_one.indicator hKm)]
  calc ∫⁻ p, Ff (muP μG₁) (K.indicator 1) (tau k r' p) ∂(mCone k r')
      ≤ ∫⁻ p, muP μG₁ D * (xi k r' ⁻¹' Ke).indicator 1 p ∂(mCone k r') := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_ne] with p hp
        exact bound p hp
    _ = muP μG₁ D * coneMeas k r' Ke := by
        rw [lintegral_const_mul _ (measurable_one.indicator (xi_cont.measurable hKem)),
          lintegral_indicator_one (xi_cont.measurable hKem), cone_eq, Measure.map_apply xi_cont.measurable hKem]
    _ < ∞ := ENNReal.mul_lt_top (hμP.finite_compact D hDc) (CF k r' Ke hKec)

lemma mC_ne : mC k r' ≠ 0 := by
  intro h
  have h1 : wt k r' =ᵐ[volume] 0 := by
    unfold mC at h
    first
      | exact withDensity_eq_zero wt_meas.aemeasurable h
      | exact (withDensity_eq_zero_iff wt_meas.aemeasurable).1 h
  have h2 : ∀ᵐ c : ℂ ∂volume, c = 0 := by
    filter_upwards [h1] with c hc
    simp only [wt, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hc
    by_contra hne
    have : 0 < ‖c‖ ^ (2 * (2 * r' + k + 1)) := pow_pos (norm_pos_iff.2 hne) _
    linarith
  have h3 : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℂ) : (volume : Measure ℂ) {0} = 0)
  have h4 : ∀ᵐ _c : ℂ ∂volume, False := by
    filter_upwards [h2, h3] with c a b using b a
  rw [ae_iff] at h4
  first
    | simp at h4
    | exact (NeZero.ne (volume : Measure ℂ)) (Measure.measure_univ_eq_zero.1 (by simpa using h4))

lemma prod_ne {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    (h1 : μ ≠ 0) (h2 : ν ≠ 0) : μ.prod ν ≠ 0 := by
  intro h
  have hz : μ.prod ν (Set.univ ×ˢ Set.univ) = 0 := by simp [h]
  rw [Measure.prod_prod, mul_eq_zero, Measure.measure_univ_eq_zero, Measure.measure_univ_eq_zero] at hz
  exact hz.elim h1 h2

lemma vol_ne : (volume : Measure (HPar k r' × HPar k r')) ≠ 0 := by
  first
    | exact NeZero.ne _
    | exact prod_ne _ _ (NeZero.ne _) (NeZero.ne _)
    | simp

lemma nu_ne (μG₁ : Measure (Mt k r')) [SFinite μG₁] (h0 : μG₁ ≠ 0) : nu μG₁ ≠ 0 := by
  unfold nu
  rw [Ne, Measure.map_eq_zero_iff Psi_meas.aemeasurable]
  exact prod_ne _ _ mC_ne (prod_ne _ _ vol_ne h0)

theorem assembleOneStep : AssembleOneStep := by
  intro HU HIv hG HA HI OM OC CI CF SD SH k r' μG μG₁ hμG h₁
  obtain ⟨hP, hμP⟩ := SH k r' μG₁ h₁
  have := sigmaFinite_of_haar h₁
  obtain ⟨c, hc⟩ := HU k (1 + r') (GV k (1 + r')) μG (nu μG₁) (hG _ _) hμG (nu_conc HIv hG HI OM μG₁ h₁ hP hμP)
    (fun a ha => nu_left HIv hG HA HI OM OC CI SD μG₁ h₁ hP hμP a ha)
    (fun K hK => nu_fin HIv hG HA HI OM CF μG₁ h₁ hP hμP K hK)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact nu_ne μG₁ h₁.ne_zero hc
  refine ⟨c⁻¹, inv_pos.2 (pos_iff_ne_zero.2 hc0), fun f hf => ?_⟩
  have h2 : II μG₁ f = (c : ℝ≥0∞) * ∫⁻ g, f g ∂μG := by
    rw [← lintegral_nu μG₁ f hf, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  show _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * II μG₁ f
  rw [h2, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0, ENNReal.coe_one, one_mul]

end Formalism.FourierDecayAlt.P.B2x9

namespace Formalism.FourierDecayAlt.P.B2x9.S1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

lemma herm_bvec {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m) : herm H (bvec q) (bvec p) = H p q := by
  rw [herm_bvec_right_eq_mulVec_apply]
  simp [bvec, mulVec, dotProduct, Pi.single_apply]

lemma base_vector_levi_coordinate_zero (i : Fin (2 * r' + k + 1)) : e0 k r' (levPos k 1 r' i) = 0 := by
  rw [e0_eq]
  simp [Pi.single_apply, levPos_ne_first]

lemma hermitian_levi_vector_base_orthogonal (j : Fin (2 * r' + k + 1)) :
    herm (Hpk k (1 + r')) (bvec (levPos k 1 r' j)) (e0 k r') = 0 := by
  rw [show e0 k r' = bvec (iF k r') from rfl, herm_bvec, Hpk_first]
  simp [levPos_ne_last]

lemma levPos_inj : Function.Injective (levPos k 1 r') := by
  intro a b h
  have h2 : a.val + 1 = b.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)

lemma heis_block (x : HPar k r') (i j : Fin (2 * r' + k + 1)) :
    heis0 k r' x (levPos k 1 r' i) (levPos k 1 r' j) = if i = j then 1 else 0 := by
  simp only [heis0, heisG, Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, base_vector_levi_coordinate_zero,
    hermitian_levi_vector_base_orthogonal, zero_mul, mul_zero, sub_zero, add_zero, Matrix.one_apply, levPos_inj.eq_iff]

lemma lev_block (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  exact lev_mid g i j

lemma lev_off (g : Mat k r') (m : Fin (2 * (1 + r') + k + 1)) (hm : m ∉ Set.range (levPos k 1 r'))
    (j : Fin (2 * r' + k + 1)) : ιLev k 1 r' g m (levPos k 1 r' j) = 0 := by
  unfold ιLev
  have hp : ¬ (1 ≤ m.val ∧ m.val < 2 * r' + k + 1 + 1) := by
    rintro ⟨h1, h2⟩
    exact hm ⟨⟨m.val - 1, by omega⟩, Fin.ext (show m.val - 1 + 1 = m.val by omega)⟩
  rw [dif_neg hp, if_neg]
  intro h
  exact hm ⟨j, h.symm⟩

lemma prod_block (x : HPar k r') (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    (heis0 k r' x * ιLev k 1 r' g) (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (levPos k 1 r' i)]
  · rw [heis_block, if_pos rfl, one_mul, lev_block]
  · intro m _ hm
    by_cases hr : m ∈ Set.range (levPos k 1 r')
    · obtain ⟨l, rfl⟩ := hr
      rw [heis_block, if_neg (fun h => hm (by rw [h])), zero_mul]
    · rw [lev_off g m hr, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def rho (k r' : ℕ) (g : Mt k (1 + r')) : Mt k (1 + r') :=
  ιLev k 1 r' (fun i j => g (levPos k 1 r' i) (levPos k 1 r' j))

lemma rho_cont : Continuous (rho k r') := by
  first
    | exact levM_cont.comp (continuous_pi fun i => continuous_pi fun j => continuous_apply_apply _ _)
    | exact levM_cont.comp (by fun_prop)

lemma rho_prod (x : HPar k r') (g : Mat k r') : rho k r' (heis0 k r' x * ιLev k 1 r' g) = ιLev k 1 r' g := by
  unfold rho
  congr 1
  ext i j
  exact prod_block x g i j

lemma parabolic_subgroup_closed (hG : ClosedG) : IsClosed (P1set k r') := by
  have hc : IsClosed {g : Mat k (1 + r') | g *ᵥ e0 k r' = e0 k r'} :=
    isClosed_eq (by first | exact continuous_id.matrix_mulVec continuous_const | fun_prop | continuity)
      continuous_const
  have hG' := hG k (1 + r')
  first
    | exact hG'.1.inter hc
    | exact hG'.isClosed.inter hc
    | exact hG'.closed.inter hc
    | exact hG'.2.inter hc

theorem assembleStab : AssembleStab := by
  intro hSemi hLev hG hHC hHH hConj hConjM hStab k r' μG₁ hμ
  obtain ⟨hBcl, hBhaar⟩ := hLev k r' (GV k r') μG₁ (hG k r') hμ
  have key := hSemi k (1 + r') (Hset k r') (ιLev k 1 r' '' GV k r') (μHeis k r') (μG₁.map (levM k r')) (rho k r')
    (hHC k r').2 hBcl
    (by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨x, rfl⟩
      exact ⟨_, (hConj k r' g hg x).symm⟩)
    (by rw [← hStab]; exact parabolic_subgroup_closed hG)
    rho_cont
    (by
      rintro _ ⟨x, rfl⟩ _ ⟨g, _, rfl⟩
      exact rho_prod x g)
    (hHH k r') hBhaar
    (by
      rintro _ ⟨g, hg, rfl⟩
      exact hConjM k r' g hg)
  rw [← hStab] at key
  exact key

end Formalism.FourierDecayAlt.P.B2x9.S1

namespace Formalism.FourierDecayAlt.P.B2x9.S2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem cOf_meas (k r' : ℕ) :
    Measurable fun g : Mt k (1 + r') => herm (Hpk k (1 + r')) (Matrix.of g *ᵥ e0 k r') (e0 k r') := by
  exact ((herm_cont _).comp (evalE_cont.prodMk continuous_const)).measurable

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨@fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem oneStepNullFromInt : OneStepNullFromInt := by
  intro hInt hEx OM k r' μG hG
  obtain ⟨μG₁, h₁⟩ := hEx k r'
  haveI := sigmaFinite_of_haar h₁
  obtain ⟨C, _, hF⟩ := hInt k r' μG μG₁ hG h₁
  have hSm : MeasurableSet {g : Mt k (1 + r') | herm (Hpk k (1 + r')) (Matrix.of g *ᵥ e0 k r') (e0 k r') = 0} :=
    measurableSet_eq_fun (cOf_meas k r') measurable_const
  rw [← lintegral_indicator_one hSm, hF _ (measurable_one.indicator hSm)]
  refine mul_eq_zero_of_right _ ?_
  refine (lintegral_congr (fun c => ?_)).trans lintegral_zero
  try dsimp only
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero, zero_pow (by omega), ENNReal.ofReal_zero, zero_mul]
  · refine mul_eq_zero_of_right _ ?_
    have hae : ∀ᵐ p ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁), p.2 ∈ (GV k r' : Set (Mt k r')) := by
      rw [ae_iff]
      refine measure_mono_null (t := Set.univ ×ˢ {g : Mt k r' | g ∉ (GV k r' : Set (Mt k r'))})
        (fun p hp => ⟨Set.mem_univ _, hp⟩) ?_
      rw [Measure.prod_prod]
      exact mul_eq_zero_of_right _ h₁.conc
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae] with p hp
    have hv := (OM k r' p.1.1 p.1.2 c hc (Matrix.of p.2) hp).2
    refine Set.indicator_apply_eq_zero.2 (fun hn => ?_)
    have hn' : herm (Hpk k (1 + r')) (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2 *ᵥ e0 k r') (e0 k r') = 0 := hn
    exact absurd (hv.symm.trans hn') hc

end Formalism.FourierDecayAlt.P.B2x9.S2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.B2

theorem stabilizer_haar_of_parts : Formalism.FourierDecayAlt.B2.AssembleStab := by
  exact Formalism.FourierDecayAlt.P.B2x9.S1.assembleStab

theorem stabilizer_haar_measure : Formalism.FourierDecayAlt.B2.StabHaar := by
  exact stabilizer_haar_of_parts semidirect_product_haar levi_haar_measure_exists unitary_group_closed heisenberg_subgroup_closed
    heisenberg_haar_measure heisenberg_conjugation_by_levi heisenberg_levi_conjugation_measure stabilizer_factorization

theorem stabilizer_integration_of_parts : Formalism.FourierDecayAlt.B2.AssembleOneStep := by
  exact Formalism.FourierDecayAlt.P.B2x9.assembleOneStep

theorem stabilizer_integration_formula : Formalism.FourierDecayAlt.B2.OneStepInt := by
  exact stabilizer_integration_of_parts haar_measure_unique_up_to_scalar haar_measure_inversion unitary_group_closed heisenberg_action_formula
    heisenberg_inverse stabilizer_one_parameter_mem rank_one_coordinates_formula isotropic_cone_invariance isotropic_cone_finite_measure
    stabilizer_factorization stabilizer_haar_measure

theorem stabilizer_null_of_integrable : Formalism.FourierDecayAlt.B2.OneStepNullFromInt := by
  exact Formalism.FourierDecayAlt.P.B2x9.S2.oneStepNullFromInt

theorem stabilizer_null_set : Formalism.FourierDecayAlt.B2.OneStepNull := by
  exact stabilizer_null_of_integrable stabilizer_integration_formula unitary_group_haar_exists stabilizer_one_parameter_mem

end Formalism.FourierDecayAlt.P
