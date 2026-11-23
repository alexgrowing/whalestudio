import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKerOpRowFreqColGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

theorem conj_colGL_unipB {R : Type} [CommRing R] {n : ℕ} (ρ : Fin n) (hρ : (ρ : ℕ) + 1 < n) (g : GL (Fin n) R)
    (hg : ∀ i : Fin n, (ρ : ℕ) + 1 ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      (g : Matrix (Fin n) (Fin n) R) i i = 1)
    (hgi : ∀ i : Fin n, (ρ : ℕ) + 1 ≤ (i : ℕ) → (∀ j, j < i → ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1) (ξ : Fin n → R) :
    g * colGL (ρ + 1) ξ * g⁻¹ ∈ GlobalTheory.SmGL.unipB R (Fin n) ∧
      GlobalTheory.Whittaker.superDiag (g * colGL (ρ + 1) ξ * g⁻¹) =
        ∑ j, (if j ≤ ρ then (g : Matrix (Fin n) (Fin n) R) ρ j else 0) * ξ j := by
  let r : Fin n := ⟨ρ + 1, hρ⟩
  have hrv : (r : ℕ) = ρ + 1 := rfl
  let G : Matrix (Fin n) (Fin n) R := (g : Matrix (Fin n) (Fin n) R)
  let Gi : Matrix (Fin n) (Fin n) R := ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  let v : Fin n → R := fun a => if (a : ℕ) < ρ + 1 then ξ a else 0
  let e : Fin n → R := fun b => if (b : ℕ) = ρ + 1 then 1 else 0
  let p : Fin n → R := G.mulVec v
  let q : Fin n → R := Matrix.vecMul e Gi
  let u : GL (Fin n) R := g * colGL (ρ + 1) ξ * g⁻¹
  have hX : Matrix.of (fun i j : Fin n => if (j : ℕ) = ρ + 1 ∧ (i : ℕ) < ρ + 1 then ξ i else 0) =
      Matrix.vecMulVec v e := by
    ext i j
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, v, e]
    by_cases hj : (j : ℕ) = ρ + 1 <;> by_cases hi : (i : ℕ) < ρ + 1 <;> simp [hj, hi]
  have hu : (u : Matrix (Fin n) (Fin n) R) = 1 + Matrix.vecMulVec p q := by
    change G * (1 + Matrix.of (fun i j : Fin n => if (j : ℕ) = ρ + 1 ∧ (i : ℕ) < ρ + 1 then ξ i else 0)) * Gi = _
    rw [hX, mul_add, add_mul, mul_one, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    exact Units.mul_inv g
  have hp : ∀ i : Fin n, ρ + 1 ≤ (i : ℕ) → p i = 0 := by
    intro i hi
    simp only [p, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : (a : ℕ) < ρ + 1
    · have : G i a = 0 := (hg i hi).1 a (by rw [Fin.lt_def]; omega)
      rw [this, zero_mul]
    · simp only [v, ha, if_false, mul_zero]
  have hqe : ∀ l, q l = Gi r l := by
    intro l
    simp only [q, Matrix.vecMul, dotProduct, e]
    rw [Finset.sum_eq_single r]
    · simp [hrv]
    · intro b _ hb
      have : (b : ℕ) ≠ ρ + 1 := fun h' => hb (Fin.ext h')
      simp [this]
    · simp
  have hq : ∀ l : Fin n, (l : ℕ) < ρ + 1 → q l = 0 := fun l hl => by
    rw [hqe]; exact (hgi r le_rfl).1 l (by rw [Fin.lt_def]; omega)
  have hq1 : q r = 1 := by rw [hqe]; exact (hgi r le_rfl).2
  have huij : ∀ i j, (u : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j + p i * q j := by
    intro i j; rw [hu]; rfl
  have hmem : u ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i l hli => ?_, fun i => ?_⟩
    · rw [huij, Matrix.one_apply_ne (ne_of_lt hli).symm, zero_add]
      by_cases hi : ρ + 1 ≤ (i : ℕ)
      · rw [hp i hi, zero_mul]
      · rw [hq l (by rw [Fin.lt_def] at hli; omega), mul_zero]
    · rw [huij, Matrix.one_apply_eq]
      by_cases hi : ρ + 1 ≤ (i : ℕ)
      · rw [hp i hi, zero_mul, add_zero]
      · rw [hq i (by omega), mul_zero, add_zero]
  refine ⟨hmem, ?_⟩
  have hsd : GlobalTheory.Whittaker.superDiag u = p ρ := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single ρ]
    · rw [Finset.sum_eq_single_of_mem r (by simp [hrv])]
      · rw [huij, Matrix.one_apply_ne (fun h' => by have := congrArg Fin.val h'; simp [hrv] at this), zero_add, hq1,
          mul_one]
      · intro j hj hjr
        simp only [Finset.mem_filter] at hj
        exact absurd (Fin.ext (by rw [hj.2, hrv])) hjr
    · intro i _ hiρ
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_filter] at hj
      rw [huij, Matrix.one_apply_ne (fun h' => by have := congrArg Fin.val h'; omega), zero_add]
      by_cases hi : ρ + 1 ≤ (i : ℕ)
      · rw [hp i hi, zero_mul]
      · have : (i : ℕ) ≠ ρ := fun h' => hiρ (Fin.ext h')
        rw [hq j (by omega), mul_zero]
    · simp
  have hpρ : p ρ = ∑ j, (if j ≤ ρ then (g : Matrix (Fin n) (Fin n) R) ρ j else 0) * ξ j := by
    simp only [p, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [v, G]
    by_cases hj : j ≤ ρ
    · have : (j : ℕ) < ρ + 1 := by rw [Fin.le_def] at hj; omega
      simp [hj, this]
    · have : ¬ (j : ℕ) < ρ + 1 := by rw [Fin.le_def] at hj; omega
      simp [hj, this]
  exact hsd.trans hpρ

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem whitInf_colGL_levSet (ρ : Fin n) (hρ : (ρ : ℕ) + 1 < n) (W : GL (Fin n) (Cinf E) → ℂ) (hW : IsWhitInf W)
    (g : GL (Fin n) (Cinf E)) (hg : g ∈ levSetInf E n (ρ + 1)) (ξ : Fin n → Cinf E) (h : GL (Fin n) (Cinf E)) :
    W (g * (colGL (ρ + 1) ξ * h)) =
      (𝐞 (-∑ w, 2 * ((∑ j, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j * ξ j) w).re) : ℂ) * W (g * h) := by
  have hgi : g⁻¹ ∈ levSetInf E n (ρ + 1) := fun w => by
    rw [map_inv]; exact (levSet_closed_subgroup n (ρ + 1)).2.1 _ (hg w)
  obtain ⟨hmem, hsd⟩ := conj_colGL_unipB ρ hρ g (mem_levSetInf.1 hg) (mem_levSetInf.1 hgi) ξ
  have hgh : g * (colGL (ρ + 1) ξ * h) = (g * colGL (ρ + 1) ξ * g⁻¹) * (g * h) := by group
  rw [hgh, hW _ hmem, hsd]
  rfl

end GlobalTheory.JSW.MirCinf

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

open Classical in

def unitVecInf (j : Fin n) (w : InfinitePlace E) (z : ℂ) : Fin n → Cinf E := Pi.single j (Pi.single w z)

variable (E n) in

def dualVecInf : ((Fin n → Cinf E) →L[ℝ] ℝ) →L[ℝ] (Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ζ j w => (-(ζ (unitVecInf j w 1) : ℂ) + Complex.I * (ζ (unitVecInf j w Complex.I) : ℂ)) / 2
      map_add' := fun ζ ζ' => by
        funext j w
        simp only [ContinuousLinearMap.add_apply, Pi.add_apply, Complex.ofReal_add]
        ring
      map_smul' := fun c ζ => by
        funext j w
        simp only [ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
          RingHom.id_apply, Complex.real_smul]
        ring }

theorem dualVecInf_apply (ζ : (Fin n → Cinf E) →L[ℝ] ℝ) (j : Fin n) (w : InfinitePlace E) :
    dualVecInf E n ζ j w = (-(ζ (unitVecInf j w 1) : ℂ) + Complex.I * (ζ (unitVecInf j w Complex.I) : ℂ)) / 2 := rfl

theorem eq_sum_unitVecInf (v : Fin n → Cinf E) :
    v = ∑ j, ∑ w, ((v j w).re • unitVecInf j w 1 + (v j w).im • unitVecInf j w Complex.I) := by
  funext j' w'
  classical
  rw [Finset.sum_apply, Finset.sum_eq_single j']
  · rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single w']
    · simp only [Pi.add_apply, Pi.smul_apply, unitVecInf, Pi.single_eq_same, Complex.real_smul, mul_one]
      exact (Complex.re_add_im _).symm
    · intro w _ hw
      simp [unitVecInf, Pi.single_apply, Ne.symm hw]
    · simp
  · intro j _ hj
    simp [Finset.sum_apply, unitVecInf, Pi.single_apply, Ne.symm hj]
  · simp

theorem dualVecInf_spec (ζ : (Fin n → Cinf E) →L[ℝ] ℝ) (v : Fin n → Cinf E) :
    -∑ w, 2 * ((∑ j, v j * dualVecInf E n ζ j) w).re = ζ v := by
  have h1 : ζ v = ∑ j, ∑ w, ((v j w).re * ζ (unitVecInf j w 1) + (v j w).im * ζ (unitVecInf j w Complex.I)) := by
    calc ζ v = ζ (∑ j, ∑ w, ((v j w).re • unitVecInf j w 1 + (v j w).im • unitVecInf j w Complex.I)) :=
          congrArg ζ (eq_sum_unitVecInf v)
      _ = _ := by simp only [map_sum, map_add, map_smul, smul_eq_mul]
  rw [h1, Finset.sum_comm]
  simp only [Finset.sum_apply, Pi.mul_apply, Complex.re_sum, dualVecInf_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.div_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.neg_im, Complex.div_im]
  norm_num
  ring

theorem one_le_htInf_nf (y : GL (Fin n) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem compGL_colGL (w : InfinitePlace E) (r : ℕ) (ξ : Fin n → Cinf E) :
    compGL w (colGL r ξ) = colGL r (fun i => ξ i w) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [compGL_apply]
  rw [colGL_val_apply]
  change ((1 : Matrix (Fin n) (Fin n) (Cinf E)) + Matrix.of (fun i j : Fin n => if (j : ℕ) = r ∧ (i : ℕ) < r then ξ i else 0)) i j w = _
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, Pi.add_apply]
  split_ifs <;> simp

theorem htInf_colGL_le (r : ℕ) (ξ : Fin n → Cinf E) :
    htInf (colGL r ξ) ≤ (1 + 2 * (n : ℝ) ^ 2 * (1 + ‖ξ‖)) ^ Fintype.card (InfinitePlace E) := by
  unfold htInf
  rw [← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun w _ => (htGL_pos _).le) fun w _ => ?_
  change htGL (compGL w (colGL r ξ)) ≤ _
  rw [compGL_colGL]
  refine (htGL_colGL_le r _).trans ?_
  have : ‖(fun i => ξ i w : Fin n → ℂ)‖ ≤ ‖ξ‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg ξ)).2 fun i => (norm_le_pi_norm (ξ i) w).trans (norm_le_pi_norm ξ i)
  have h0 : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by positivity
  nlinarith

theorem measurable_htInf {X : Type} [MeasurableSpace X] {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => htInf (γ x) := by
  unfold htInf
  exact Finset.measurable_prod _ fun w _ =>
    measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

end GlobalTheory.JSW.MirCinf

namespace GlobalTheory.JSW.MirCinf

theorem exists_kerOpInf_rowFreq_colGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), (ρ : ℕ) + 1 < n →
    ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (T : (GL (Fin n) (Cinf E) → ℂ) → Z × (Fin n → Cinf E) → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T →
    ∃ T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T' ∧ ∀ W, IsModGrowthInf W →
      IsWhitInf W → ∀ z, ∀ g ∈ levSetInf E n (ρ + 1),
        T' W z g = T W (z, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) g := by
  intro E _ _ n ρ hρ Z _ _ _ T hT
  obtain ⟨X, _, ν, _, k, γ, η, hR, hTeq⟩ := hT
  set V := Fin n → Cinf E
  set Ξ := dualVecInf E n
  let ξ : X → V := fun x => Ξ ((η x).comp (ContinuousLinearMap.inr ℝ Z V))
  let γ' : X → GL (Fin n) (Cinf E) := fun x => colGL (ρ + 1) (ξ x) * γ x
  let η' : X → Z →L[ℝ] ℝ := fun x => (η x).comp (ContinuousLinearMap.inl ℝ Z V)
  refine ⟨fun W z g => ∫ x, k x * (𝐞 (η' x z) : ℂ) * W (g * γ' x) ∂ν, ⟨X, inferInstance, ν, inferInstance, k, γ', η', ?_,
    fun W _ z g => rfl⟩, ?_⟩
  ·
    have hηm : Measurable η := measurable_dual hR.2.2.1
    have hξm : Measurable ξ :=
      (Ξ.continuous.comp (continuous_id.clm_comp continuous_const)).measurable.comp hηm
    have hcol : ∀ i l, Measurable fun x => ((colGL (ρ + 1) (ξ x) : GL (Fin n) (Cinf E)) :
        Matrix (Fin n) (Fin n) (Cinf E)) i l := by
      intro i l
      change Measurable fun x => ((1 : Matrix (Fin n) (Fin n) (Cinf E)) + Matrix.of (fun i j : Fin n =>
        if (j : ℕ) = ρ + 1 ∧ (i : ℕ) < ρ + 1 then ξ x i else 0)) i l
      simp only [Matrix.add_apply, Matrix.of_apply]
      by_cases h : ((l : ℕ) = ρ + 1 ∧ (i : ℕ) < ρ + 1)
      · simp only [h, and_self, if_true]
        exact measurable_const.add ((measurable_pi_apply i).comp hξm)
      · simp only [h, if_false]
        exact measurable_const
    have hγ' : ∀ i j, Measurable fun x => (γ' x : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
      intro i j
      simp only [γ', Units.val_mul, Matrix.mul_apply]
      exact Finset.measurable_sum _ fun l _ => (hcol i l).mul (hR.2.1 l j)
    have hη' : ∀ z, Measurable fun x => η' x z := fun z => hR.2.2.1 (z, 0)
    refine ⟨hR.1, hγ', hη', fun N => ?_⟩
    set d := Fintype.card (InfinitePlace E)
    set C0 : ℝ := 1 + 2 * (n : ℝ) ^ 2 * (1 + ‖Ξ‖)
    have hC0 : 0 ≤ C0 := by positivity
    have hb : ∀ x, htInf (γ' x) * (1 + ‖η' x‖) ≤ C0 ^ d * (htInf (γ x) * (1 + ‖η x‖)) ^ (d + 1) := by
      intro x
      have e0 := norm_nonneg (η x)
      have e1 : ‖ξ x‖ ≤ ‖Ξ‖ * ‖η x‖ := by
        refine (Ξ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_of_le_one_right e0 (norm_inr_le_one' Z V))
      have e2 : ‖η' x‖ ≤ ‖η x‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_of_le_one_right e0 (norm_inl_le_one' Z V))
      have e3 : htInf (γ' x) ≤ htInf (colGL (ρ + 1) (ξ x)) * htInf (γ x) := htInf_mul_le _ _
      have e4 := htInf_colGL_le (E := E) (n := n) (ρ + 1) (ξ x)
      have e5 := one_le_htInf_nf (γ x)
      have hn : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by positivity
      have hΞ0 := norm_nonneg Ξ
      have e7 : 1 + 2 * (n : ℝ) ^ 2 * (1 + ‖ξ x‖) ≤ C0 * (1 + ‖η x‖) := by
        have : ‖ξ x‖ ≤ (1 + ‖Ξ‖) * (1 + ‖η x‖) := by nlinarith
        nlinarith
      have e8 : htInf (colGL (ρ + 1) (ξ x)) ≤ C0 ^ d * (1 + ‖η x‖) ^ d := by
        rw [← mul_pow]
        exact e4.trans (pow_le_pow_left₀ (by positivity) e7 d)
      have e9 : htInf (γ' x) ≤ C0 ^ d * (1 + ‖η x‖) ^ d * htInf (γ x) :=
        e3.trans (mul_le_mul_of_nonneg_right e8 (htInf_pos' _).le)
      have e10 : htInf (γ x) ≤ htInf (γ x) ^ (d + 1) := le_self_pow₀ e5 (Nat.succ_ne_zero d)
      calc htInf (γ' x) * (1 + ‖η' x‖) ≤ (C0 ^ d * (1 + ‖η x‖) ^ d * htInf (γ x)) * (1 + ‖η x‖) :=
            mul_le_mul e9 (by linarith) (by linarith [norm_nonneg (η' x)]) (by positivity)
        _ = C0 ^ d * (htInf (γ x) * (1 + ‖η x‖) ^ (d + 1)) := by ring
        _ ≤ C0 ^ d * (htInf (γ x) ^ (d + 1) * (1 + ‖η x‖) ^ (d + 1)) := by
            gcongr
        _ = C0 ^ d * (htInf (γ x) * (1 + ‖η x‖)) ^ (d + 1) := by rw [mul_pow]
    refine ((hR.2.2.2 ((d + 1) * N)).const_mul ((C0 ^ d) ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · refine Measurable.aestronglyMeasurable (hR.1.norm.mul (Measurable.pow_const ?_ N))
      exact (measurable_htInf hγ').mul (measurable_const.add (measurable_dual hη').norm)
    · have hB0 : 0 ≤ htInf (γ' x) * (1 + ‖η' x‖) := by
        have := htInf_pos' (γ' x); positivity
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖k x‖ * (htInf (γ' x) * (1 + ‖η' x‖)) ^ N
          ≤ ‖k x‖ * (C0 ^ d * (htInf (γ x) * (1 + ‖η x‖)) ^ (d + 1)) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 (hb x) N) (norm_nonneg _)
        _ = (C0 ^ d) ^ N * (‖k x‖ * (htInf (γ x) * (1 + ‖η x‖)) ^ ((d + 1) * N)) := by
            rw [mul_pow (C0 ^ d), ← pow_mul (htInf (γ x) * (1 + ‖η x‖))]; ring
  ·
    intro W hW hWh z g hg
    rw [hTeq W hW (z, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only [γ']
    rw [whitInf_colGL_levSet ρ hρ W hWh g hg (ξ x) (γ x), dualVecInf_spec]
    have hsplit : (z, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) =
        ContinuousLinearMap.inl ℝ Z V z +
          ContinuousLinearMap.inr ℝ Z V (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) := by
      simp
    rw [hsplit, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    simp only [η', ContinuousLinearMap.comp_apply]
    ring

example (E : Type) [Field E] [NumberField E] (n : ℕ) :
    IsKerOpInf (fun W (_ : ℝ × (Fin n → Cinf E)) g => W (g * (1 : GL (Fin n) (Cinf E)))) :=
  isKerOpInf_dirac (ℝ × (Fin n → Cinf E)) 1

end GlobalTheory.JSW.MirCinf
