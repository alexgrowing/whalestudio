import Formalism.PeriodIntegrals.AmpRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.SUpPowEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupJacobian.BlkLt

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI.AmpRootJacW

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

theorem rootPat_lt (p : Point ℂ (r + 1)) : ∀ q ∈ rootPat p, q.1 < q.2 := by
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

theorem mem_rootPat {p : Point ℂ (r + 1)} {i j : Fin (r + 1)} :
    (i, j) ∈ rootPat p ↔ i < j ∧ blockIdx p.1 i.val = blockIdx p.1 j.val := by
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]

theorem sum_pt (p : Point ℂ (r + 1)) : (p.1.map Prod.snd).sum = r + 1 := p.2.2

private theorem blockIdx_pv_eq : ∀ (bs : List (ℂ × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    blockIdx bs (pv bs i) = blockIdx bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · have h1 : s - 1 - i < s := by omega
      simp only [pv, blockIdx, hi, h1, ↓reduceIte]
    · have ih := blockIdx_pv_eq bs (i - s) (by omega)
      have h1 : ¬ (s + pv bs (i - s) < s) := by omega
      simp only [pv, blockIdx, hi, h1, ↓reduceIte, Nat.add_sub_cancel_left, ih]

private theorem pv_lt_pv_of_lt_of_blockIdx_eq : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i < j → blockIdx bs i = blockIdx bs j →
    j < (bs.map Prod.snd).sum → pv bs j < pv bs i
  | [], i, j, _, _, h => by simp at h
  | (t, s) :: bs, i, j, hij, hb, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hj : j < s
    · have hi : i < s := by omega
      simp only [pv, hi, hj, ↓reduceIte]
      omega
    · by_cases hi : i < s
      · simp only [blockIdx, hi, hj, ↓reduceIte] at hb
        omega
      · have hb' : blockIdx bs (i - s) = blockIdx bs (j - s) := by
          simp only [blockIdx, hi, hj, ↓reduceIte] at hb
          omega
        have ih := pv_lt_pv_of_lt_of_blockIdx_eq bs (i - s) (j - s) (by omega) hb' (by omega)
        simp only [pv, hi, hj, ↓reduceIte]
        omega

theorem tau_mem {p : Point ℂ (r + 1)} (q : rootPat p) : (ptσ p q.1.2, ptσ p q.1.1) ∈ rootPat p := by
  obtain ⟨hlt, hb⟩ := (mem_rootPat (i := q.1.1) (j := q.1.2)).mp q.2
  have hs : (p.1.map Prod.snd).sum = r + 1 := p.2.2
  have h1 := q.1.1.2
  have h2 := q.1.2.2
  rw [mem_rootPat]
  refine ⟨?_, ?_⟩
  · show pv p.1 q.1.2.val < pv p.1 q.1.1.val
    exact pv_lt_pv_of_lt_of_blockIdx_eq p.1 _ _ hlt hb (by omega)
  · show blockIdx p.1 (pv p.1 q.1.2.val) = blockIdx p.1 (pv p.1 q.1.1.val)
    rw [blockIdx_pv_eq p.1 _ (by omega), blockIdx_pv_eq p.1 _ (by omega)]
    exact hb.symm

def tauE (p : Point ℂ (r + 1)) : rootPat p ≃ rootPat p where
  toFun q := ⟨(ptσ p q.1.2, ptσ p q.1.1), tau_mem q⟩
  invFun q := ⟨(ptσ p q.1.2, ptσ p q.1.1), tau_mem q⟩
  left_inv q := by
    apply Subtype.ext
    simp only [ptσ_invol, Prod.mk.eta]
  right_inv q := by
    apply Subtype.ext
    simp only [ptσ_invol, Prod.mk.eta]

def cU (p : Point ℂ (r + 1)) (q : rootPat p) : ℂ := star (ptζ p q.1.2) / star (ptζ p q.1.1)

theorem norm_ptζ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) :
    ‖ptζ p i‖ = ‖ptEntry p.1 i.val (pv p.1 i.val)‖ := by
  simp only [ptζ, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rfl

private theorem ptEntry_pv_eq_of_blockIdx_eq : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), blockIdx bs i = blockIdx bs j →
    i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum → ptEntry bs i (pv bs i) = ptEntry bs j (pv bs j)
  | [], i, _, _, h, _ => by simp at h
  | (t, s) :: bs, i, j, hb, hi', hj' => by
    simp only [List.map_cons, List.sum_cons] at hi' hj'
    by_cases hi : i < s <;> by_cases hj : j < s
    · have e1 : i + (s - 1 - i) + 1 = s := by omega
      have e2 : j + (s - 1 - j) + 1 = s := by omega
      have l1 : s - 1 - i < s := by omega
      have l2 : s - 1 - j < s := by omega
      simp only [pv, ptEntry, hi, hj, l1, l2, e1, e2, and_self, ↓reduceIte]
    · simp only [blockIdx, hi, hj, ↓reduceIte] at hb
      omega
    · simp only [blockIdx, hi, hj, ↓reduceIte] at hb
      omega
    · have hb' : blockIdx bs (i - s) = blockIdx bs (j - s) := by
        simp only [blockIdx, hi, hj, ↓reduceIte] at hb
        omega
      have ih := ptEntry_pv_eq_of_blockIdx_eq bs (i - s) (j - s) hb' (by omega) (by omega)
      have g1 : s ≤ i := by omega
      have g2 : s ≤ j := by omega
      have g3 : s ≤ s + pv bs (i - s) := Nat.le_add_right _ _
      have g4 : s ≤ s + pv bs (j - s) := Nat.le_add_right _ _
      simp only [pv, ptEntry, hi, hj, g1, g2, g3, g4, false_and, and_self, ↓reduceIte,
        Nat.add_sub_cancel_left, ih]

theorem norm_cU (p : Point ℂ (r + 1)) (q : rootPat p) : ‖cU p q‖ = 1 := by
  obtain ⟨_, hb⟩ := (mem_rootPat (i := q.1.1) (j := q.1.2)).mp q.2
  have hs : (p.1.map Prod.snd).sum = r + 1 := p.2.2
  have h1 := q.1.1.2
  have h2 := q.1.2.2
  have e : ‖ptζ p q.1.2‖ = ‖ptζ p q.1.1‖ := by
    rw [norm_ptζ, norm_ptζ, ptEntry_pv_eq_of_blockIdx_eq p.1 q.1.2.val q.1.1.val hb.symm (by omega) (by omega)]
  have hne : ‖ptζ p q.1.1‖ ≠ 0 := norm_ne_zero_iff.mpr (ptζ_ne p _)
  simp only [cU, norm_div, norm_star, e]
  exact div_self hne

def phiR (p : Point ℂ (r + 1)) (v : rootPat p → ℂ) : rootPat p → ℂ :=
  fun q => cU p q * star (invC (rootPat p) v (tauE p q))

theorem phiR_mp (p : Point ℂ (r + 1)) : MeasurePreserving (phiR p) volume volume :=
  phi_mp _ (rootPat_lt p) (tauE p) (cU p) (norm_cU p)

theorem conj_back {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g₀ ∈ UH (Hpk k r))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : g₀⁻¹ * (g₀ * X * g₀⁻¹) * g₀ = X := by
  have hH : (Hpk k r).det ≠ 0 := by
    intro h0
    have h2 := congrArg Matrix.det (Hpk_mul_self (k := k) (r := r))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  have hdet := congrArg Matrix.det (show g₀ᴴ * Hpk k r * g₀ = Hpk k r from hg)
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hu : IsUnit g₀.det := isUnit_iff_ne_zero.mpr fun h0 => by
    rw [h0, mul_zero] at hdet
    exact hH hdet.symm
  have h1 : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul _ hu
  calc g₀⁻¹ * (g₀ * X * g₀⁻¹) * g₀ = (g₀⁻¹ * g₀) * X * (g₀⁻¹ * g₀) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem pv_lt_pv_of_lt_of_blockIdx_ne : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), i < j → blockIdx bs i ≠ blockIdx bs j →
    j < (bs.map Prod.snd).sum → pv bs i < pv bs j
  | [], i, j, _, _, h => by simp at h
  | (t, s) :: bs, i, j, hij, hb, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hj : j < s
    · have hi : i < s := by omega
      simp only [blockIdx, hi, hj, ↓reduceIte] at hb
      exact absurd rfl hb
    · by_cases hi : i < s
      · simp only [pv, hi, hj, ↓reduceIte]
        omega
      · have hb' : blockIdx bs (i - s) ≠ blockIdx bs (j - s) := by
          intro he
          apply hb
          simp only [blockIdx, hi, hj, ↓reduceIte, he]
        have ih := pv_lt_pv_of_lt_of_blockIdx_ne bs (i - s) (j - s) (by omega) hb' (by omega)
        simp only [pv, hi, hj, ↓reduceIte]
        omega

theorem flag_eq_one_add {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {p : Point ℂ (r + 1)}
    (hg : g₀ ∈ UH (Hpk k r)) (hP : ZhatO k r z z' g₀ = ptMat p)
    {x : Mt k r} (hx : Matrix.of x ∈ Rset k r g₀) :
    flagMat k r z' (Matrix.of x) = 1 + vM (rootPat p) (rootCoords k r z' p x) := by
  have hN : Matrix.of x ∈ Nset k r := hx.1
  have ha : g₀ * Matrix.of x * g₀⁻¹ ∈ RStab k r g₀ := ⟨hx.2, by rw [conj_back hg]; exact hx.1⟩
  have hs : (p.1.map Prod.snd).sum = r + 1 := p.2.2
  ext i j
  simp only [Matrix.add_apply, vM]
  by_cases hm : (i, j) ∈ rootPat p
  · rw [dif_pos hm]
    have hij : i ≠ j := ne_of_lt ((mem_rootPat.mp hm).1)
    rw [Matrix.one_apply_ne hij, zero_add]
    rfl
  · rw [dif_neg hm, add_zero]
    by_cases hji : j ≤ i
    · rw [flagMat_lower hN i j hji, Matrix.one_apply]
    · have hij : i < j := not_le.mp hji
      have hb : blockIdx p.1 i.val ≠ blockIdx p.1 j.val := fun h => hm (mem_rootPat.mpr ⟨hij, h⟩)
      have hj2 := j.2
      have hlt : (ptσ p i).val < (ptσ p j).val :=
        pv_lt_pv_of_lt_of_blockIdx_ne p.1 _ _ hij hb (by omega)
      have h0 := (flag_offblock hz hz' hg hP ha i j hlt).1
      rw [conj_back hg] at h0
      rw [h0, Matrix.one_apply_ne (ne_of_lt hij)]

theorem rootCoords_conj {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {p : Point ℂ (r + 1)}
    (hg : g₀ ∈ UH (Hpk k r)) (hP : ZhatO k r z z' g₀ = ptMat p)
    {x : Mt k r} (hx : Matrix.of x ∈ Rset k r g₀) :
    rootCoords k r z p (fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j) = phiR p (rootCoords k r z' p x) := by
  have hF' : flagMat k r z' (Matrix.of x) = 1 + vM (rootPat p) (rootCoords k r z' p x) :=
    flag_eq_one_add hz hz' hg hP hx
  have hG : (1 + vM (rootPat p) (rootCoords k r z' p x)) * gInv (vM (rootPat p) (rootCoords k r z' p x)) = 1 :=
    mul_gInv (sUp_vM (rootPat p) (rootPat_lt p) _)
  have hrel := flag_rel_Rset hz hz' hg hx
  rw [hF'] at hrel
  have key : (flagMat k r z (g₀ * Matrix.of x * g₀⁻¹))ᴴ * Zhat k r z z' g₀ =
      Zhat k r z z' g₀ * gInv (vM (rootPat p) (rootCoords k r z' p x)) := by
    calc _ = (flagMat k r z (g₀ * Matrix.of x * g₀⁻¹))ᴴ * Zhat k r z z' g₀ *
          ((1 + vM (rootPat p) (rootCoords k r z' p x)) * gInv (vM (rootPat p) (rootCoords k r z' p x))) := by
          rw [hG, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel]
  have inj : ∀ a b : Fin (r + 1), ptσ p a = ptσ p b ↔ a = b := fun a b =>
    ⟨fun h => by simpa only [ptσ_invol] using congrArg (ptσ p) h, fun h => h ▸ rfl⟩
  funext q
  have e := congrFun (congrFun key q.1.2) (ptσ p q.1.1)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, zhat_pt hP, inj, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at e
  have e2 := congrArg star e
  simp only [star_mul', star_star] at e2
  have hne : star (ptζ p q.1.1) ≠ 0 := star_ne_zero.mpr (ptζ_ne p _)
  show flagMat k r z (g₀ * Matrix.of x * g₀⁻¹) q.1.1 q.1.2 =
    star (ptζ p q.1.2) / star (ptζ p q.1.1) *
      star (gInv (vM (rootPat p) (rootCoords k r z' p x)) (ptσ p q.1.2) (ptσ p q.1.1))
  field_simp
  linear_combination e2

theorem measurable_conjM (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun x : Mt k r => fun i j => (a * Matrix.of x * b) i j) := by
  have hc : Continuous (fun x : Mt k r => fun i j => (a * Matrix.of x * b) i j) :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  exact hc.measurable

theorem continuous_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Continuous (rootCoords k r z p) := by
  refine continuous_pi fun q => ?_
  simp only [rootCoords, flagMat]
  by_cases hi : q.1.1.val < r
  · simp only [hi, ↓reduceDIte]
    fun_prop
  · simp only [hi, ↓reduceDIte]
    exact continuous_const

theorem cont_of : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
  continuous_id

theorem isClosed_N : IsClosed {x : Mt k r | Matrix.of x ∈ Nset k r} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    cont_of
  simp only [Nset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · exact isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc) continuous_const
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hc.matrix_elem _ _) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hc.matrix_elem _ _) continuous_const

theorem measurableSet_RStab (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ RStab k r g} := by
  have hf : Continuous (fun x : Mt k r => (fun i j => (g⁻¹ * Matrix.of x * g) i j : Mt k r)) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h2 : IsClosed {x : Mt k r | g⁻¹ * Matrix.of x * g ∈ Nset k r} := isClosed_N.preimage hf
  exact (isClosed_N.inter h2).measurableSet

theorem rootJac : PI.AmpRoot.RootJac := by
  intro k r L p g₀ μ₀ hrep _ hnull hmap
  obtain ⟨hg, hP⟩ := hrep
  have hz := L.hz.1
  have hz' := L.hz'.1
  have hf : Measurable (fun x : Mt k r => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j) := measurable_conjM _ _
  have hae : ∀ᵐ x ∂μ₀, Matrix.of x ∈ Rset k r g₀ := ae_iff.mpr hnull
  refine ⟨?_, ?_⟩
  · have hs : MeasurableSet {x : Mt k r | Matrix.of x ∉ RStab k r g₀} := (measurableSet_RStab g₀).compl
    rw [Measure.map_apply hf hs]
    refine measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hR
    exact hx ⟨hR.2, (show g₀⁻¹ * (g₀ * Matrix.of x * g₀⁻¹) * g₀ ∈ Nset k r by rw [conj_back hg]; exact hR.1)⟩
  · rw [Measure.map_map (continuous_rootCoords L.z p).measurable hf]
    have hcongr : (rootCoords k r L.z p ∘ fun x : Mt k r => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j)
        =ᵐ[μ₀] (phiR p ∘ rootCoords k r L.z' p) := by
      filter_upwards [hae] with x hx
      exact rootCoords_conj hz hz' hg hP hx
    rw [Measure.map_congr hcongr,
      ← Measure.map_map (phiR_mp p).measurable (continuous_rootCoords L.z' p).measurable, hmap,
      Measure.map_smul, (phiR_mp p).map_eq]

end PI.AmpRootJacW
