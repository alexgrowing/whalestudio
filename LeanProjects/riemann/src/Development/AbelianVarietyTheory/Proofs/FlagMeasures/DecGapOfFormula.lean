import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLeadMinorDecay
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DecGapBound

lemma det_exp_sq {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y) :
    (NormedSpace.exp Y).det * (NormedSpace.exp Y).det = 1 := by

  have hJY : Jm ε * Y * Jm ε = -Y := by
    rw [mul_assoc, h.2, mul_neg, ← mul_assoc, Jm_mul_self, one_mul]
  have hconj := exp_signature_conj ε Y
  rw [hJY] at hconj
  have hdetJ : (Jm ε).det * (Jm ε).det = 1 := by
    rw [← Matrix.det_mul, Jm_mul_self, Matrix.det_one]
  have h1 : (NormedSpace.exp (-Y)).det * (NormedSpace.exp Y).det = 1 := by
    rw [← Matrix.det_mul, matrix_exp_neg_mul_exp, Matrix.det_one]
  have h2 : (NormedSpace.exp (-Y)).det = (NormedSpace.exp Y).det := by
    rw [hconj, Matrix.det_mul, Matrix.det_mul]
    linear_combination (NormedSpace.exp Y).det * hdetJ
  rw [h2] at h1
  exact h1

lemma muInt_cast {n : ℕ} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (a : Fin n) :
    (muInt lam a : ℝ) = lam a + Formalism.QuantumDeterminants.rhoStd n a := by
  obtain ⟨m, hm⟩ := hlam.2 a
  have e : lam a + Formalism.QuantumDeterminants.rhoStd n a = ((m + (n : ℤ) - 1 - ((a : ℕ) : ℤ) : ℤ) : ℝ) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]
    push_cast
    linarith
  unfold GlobalTheory.Dec.muInt
  rw [e, Int.floor_intCast]

lemma norm_Phi_le {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {X km : Matrix (Fin n) (Fin n) ℂ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hX : inP ε X) (hk : km ∈ Kset ε) :
    ‖Phi lam (km⁻¹ * NormedSpace.exp X * km)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := by
  obtain ⟨hpos, hprod⟩ := GlobalTheory.MinorDecay.prod_leadMinor_decay n ε lam h X km hlam hgap hX hk
  set Z := km⁻¹ * NormedSpace.exp X * km with hZ
  have hR : decHS h (rkR ε) (Real.sqrt (hs X)) = Real.exp (-(h / 8) * min (hs X)
      (Real.sqrt (hs X) / Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
        (univ.filter fun a => ε a = false).card : ℕ) : ℝ)))) := by
    unfold GlobalTheory.Dec.decHS GlobalTheory.Count.rkR
    rw [Real.sq_sqrt (GlobalTheory.MinorDecay.hs_nonneg X)]
  rw [hR]
  refine le_trans (le_of_eq ?_) hprod

  have hre : ∀ (l : ℕ) (hl : l ≤ n), ‖leadMinor Z l hl‖ = (leadMinor Z l hl).re := by
    intro l hl
    obtain ⟨h1, h2⟩ := hpos l hl
    set z := leadMinor Z l hl
    have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h2])
    rw [e, Complex.norm_real, Real.norm_of_nonneg h1.le, Complex.ofReal_re]
  have hinv : km⁻¹ * km = 1 :=
    Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 hk.1))
  have hdet2 : Z.det = (NormedSpace.exp X).det := by
    rw [hZ, Matrix.det_mul, Matrix.det_mul, mul_comm (km⁻¹.det), mul_assoc, ← Matrix.det_mul, hinv,
      Matrix.det_one, mul_one]
  rcases n with _ | m
  · simp [GlobalTheory.Dec.Phi]
  · show ‖Phi lam Z‖ = ∏ i : Fin m, (leadMinor Z (i.val + 1) (by omega)).re ^
      (-(lam i.castSucc - lam i.succ + 1))

    have hlast : ∀ hl : m + 1 ≤ m + 1, ‖leadMinor Z (m + 1) hl‖ = 1 := by
      intro hl
      rw [hre]
      obtain ⟨h1, h2⟩ := hpos (m + 1) hl
      have hdet : leadMinor Z (m + 1) hl = Z.det := by
        unfold leadMinor
        congr 1
      have hsq := det_exp_sq hX
      rw [← hdet2, ← hdet] at hsq
      have h3 := congrArg Complex.re hsq
      simp only [Complex.mul_re, h2, mul_zero, sub_zero, Complex.one_re] at h3
      nlinarith
    unfold GlobalTheory.Dec.Phi
    rw [norm_prod, Fin.prod_univ_castSucc]
    simp only [norm_zpow, Fin.val_last, Fin.coe_castSucc]
    rw [hlast, _root_.one_zpow, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hre, ← Real.rpow_intCast]
    congr 1
    have hi : (i.castSucc : ℕ) + 1 < m + 1 := by simp
    have e : (⟨(i.castSucc : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := Fin.ext (by simp)
    simp only [GlobalTheory.Dec.sInt, dif_pos hi, e]
    push_cast
    rw [muInt_cast hlam, muInt_cast hlam]
    simp only [Formalism.QuantumDeterminants.rhoStd, Fin.coe_castSucc, Fin.val_succ]
    push_cast
    ring

lemma Phi_one' {n : ℕ} (lam : Fin n → ℝ) : Phi lam (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold GlobalTheory.Dec.Phi
  refine Finset.prod_eq_one fun i _ => ?_
  have e : leadMinor (1 : Matrix (Fin n) (Fin n) ℂ) (i.val + 1) i.isLt = 1 := by
    unfold leadMinor
    rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  rw [e, _root_.one_zpow]

lemma continuous_toMK {n : ℕ} (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) := by
  exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

lemma weighted_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (d : ℕ) (φ a b : α → ℂ)
    (M U V : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ M)
    (i1 : Integrable (fun x => ‖a x‖ ^ 2) μ) (i2 : Integrable (fun x => ‖b x‖ ^ 2) μ)
    (ha : (d : ℝ) * ∫ x, ‖a x‖ ^ 2 ∂μ = V ^ 2) (hb : (d : ℝ) * ∫ x, ‖b x‖ ^ 2 ∂μ = U ^ 2) :
    ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * U * V := by
  set A := ∫ x, ‖a x‖ ^ 2 ∂μ with hA
  set B := ∫ x, ‖b x‖ ^ 2 ∂μ with hB
  have ma : AEStronglyMeasurable (fun x => ‖a x‖) μ := by
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable i1.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (norm_nonneg _)
  have mb : AEStronglyMeasurable (fun x => ‖b x‖) μ := by
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable i2.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (norm_nonneg _)
  have La : MemLp (fun x => ‖a x‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq ma).2 i1
  have Lb : MemLp (fun x => ‖b x‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq mb).2 i2

  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => norm_nonneg (a x))
    (Filter.Eventually.of_forall fun x => norm_nonneg (b x)) La Lb
  simp only [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  have iab : Integrable (fun x => ‖a x‖ * ‖b x‖) μ := by
    refine Integrable.mono' ((i1.add i2).div_const 2) (ma.mul mb) (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have h1 : ‖∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * (Real.sqrt A * Real.sqrt B) := by
    calc ‖∫ x, φ x * (a x * b x) ∂μ‖ ≤ ∫ x, M * (‖a x‖ * ‖b x‖) ∂μ := by
          refine norm_integral_le_of_norm_le (iab.const_mul M) (Filter.Eventually.of_forall fun x => ?_)
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_right (hφ x) (by positivity)
      _ = M * ∫ x, ‖a x‖ * ‖b x‖ ∂μ := integral_const_mul M _
      _ ≤ M * (Real.sqrt A * Real.sqrt B) := mul_le_mul_of_nonneg_left hH hM
  have hVs : V = Real.sqrt ((d : ℝ) * A) := by rw [ha, Real.sqrt_sq hV]
  have hUs : U = Real.sqrt ((d : ℝ) * B) := by rw [hb, Real.sqrt_sq hU]
  have hdd := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) d)
  rw [norm_mul, Complex.norm_natCast, hVs, hUs, Real.sqrt_mul (Nat.cast_nonneg d),
    Real.sqrt_mul (Nat.cast_nonneg d)]
  refine le_trans (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) (le_of_eq ?_)
  linear_combination (-(M * Real.sqrt A * Real.sqrt B)) * hdd

lemma dec_exp (hF : FormulaGap) (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hlam : IsHCParam lam) (hDS : IsDS ε lam σ)
    (h : ℝ) (hgap : GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) (u : H) (hu : u ∈ lowKSub ε lam σ)
    (v : H) (hv : v ∈ lowKSub ε lam σ) :
    ‖⟪v, σ (NormedSpace.exp X) u⟫_ℂ‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖v‖ := by
  haveI : CompleteSpace H := hDS.1
  obtain ⟨w, hw⟩ := (GlobalTheory.LowKProj.lowK_projection n ε lam H σ hDS).1
  have hURep := hDS.2.2.1
  have hform := hF n ε lam H σ hlam hDS h hgap hh w hw
  have hK : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  have hUJ : ∀ k : KG ε, toMK k ∈ UJset ε := fun k => GlobalTheory.LowKProj.mem_UJset_of_Kset (hK k)
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ * toMK k = 1 := fun k =>
    Matrix.nonsing_inv_mul _
      (Matrix.isUnit_det_of_left_inverse ((Matrix.mem_unitaryGroup_iff').1 (hK k).1))
  have hcont : ∀ x : H, Continuous (fun k : KG ε => σ (toMK k) x) := fun x =>
    (hURep.2.2 x).comp_continuous (continuous_toMK ε) hUJ
  have hnorm : ∀ (k : KG ε) (x : H), ‖σ (toMK k) x‖ = ‖x‖ := fun k x => hURep.2.1 _ (hUJ k) x

  have hint : ∀ x : H, Integrable (fun k : KG ε => ‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε) := by
    intro x
    refine Integrable.of_bound ((continuous_const.inner (hcont w)).norm.pow 2).aestronglyMeasurable
      (‖x‖ ^ 2) (Filter.Eventually.of_forall fun k => ?_)
    have h1 : ‖⟪x, σ (toMK k) w⟫_ℂ‖ ≤ ‖x‖ := by
      calc ‖⟪x, σ (toMK k) w⟫_ℂ‖ ≤ ‖x‖ * ‖σ (toMK k) w‖ := norm_inner_le_norm _ _
        _ = ‖x‖ := by rw [hnorm, hw.1, mul_one]
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

  have h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inP, inG]
  have horth : ∀ x ∈ lowKSub ε lam σ, (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) *
      ∫ k, ‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) = ‖x‖ ^ 2 := by
    intro x hx
    have hpt : ∀ k : KG ε, ⟪x, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, x⟫_ℂ =
        ((‖⟪x, σ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [← inner_conj_symm (σ (toMK k) w) x, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have e := hform 0 h0 x hx x hx
    simp only [NormedSpace.exp_zero, hURep.1.1, ContinuousLinearMap.one_apply, mul_one, hinv,
      Phi_one', one_mul, hpt] at e
    rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at e
    apply Complex.ofReal_injective
    push_cast
    linear_combination -e
  have hsym : (fun k : KG ε => ‖⟪σ (toMK k) w, u⟫_ℂ‖ ^ 2) =
      (fun k : KG ε => ‖⟪u, σ (toMK k) w⟫_ℂ‖ ^ 2) := funext fun k => by rw [norm_inner_symm]
  have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := by
    unfold GlobalTheory.Dec.decHS
    positivity
  have hmain := weighted_bound (muK ε) (Module.finrank ℂ (lowKSub ε lam σ))
    (fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k))
    (fun k => ⟪v, σ (toMK k) w⟫_ℂ) (fun k => ⟪σ (toMK k) w, u⟫_ℂ)
    (decHS h (rkR ε) (Real.sqrt (hs X))) ‖u‖ ‖v‖ hM (norm_nonneg u) (norm_nonneg v)
    (fun k => norm_Phi_le hlam hgap hX (hK k)) (hint v) (by rw [hsym]; exact hint u)
    (horth v hv) (by rw [hsym]; exact horth u hu)
  rw [hform X hX u hu v hv]
  exact hmain

lemma decHS_le_decE {h d t : ℝ} (q : ℕ) (hh : 0 ≤ h) (hd : 0 ≤ d) (hdt : Real.sqrt 2 * d ≤ t) :
    decHS h q t ≤ decE q h d := by
  unfold GlobalTheory.Dec.decHS GlobalTheory.Count.decE
  apply Real.exp_le_exp.mpr
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have h1 : 2 * d ^ 2 ≤ t ^ 2 := by
    have e : (Real.sqrt 2 * d) ^ 2 = 2 * d ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [← e]
    exact pow_le_pow_left₀ (mul_nonneg hs2.le hd) hdt 2
  have h2 : d / Real.sqrt q ≤ t / Real.sqrt (2 * q) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← div_div]
    have hdt' : d ≤ t / Real.sqrt 2 := by
      rw [le_div_iff₀ hs2]
      linarith
    exact div_le_div_of_nonneg_right hdt' (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonpos_left (min_le_min h1 h2) (by linarith)

lemma dOp_facts {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    0 ≤ dOp g ∧ Real.sqrt 2 * dOp g ≤ dHS g := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : dOp g = 0 := by
      unfold GlobalTheory.Count.dOp
      have e : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g) = 0 := by
        ext x i
        exact i.elim0
      rw [e, norm_zero, Real.log_zero]
    have h1 : dHS g = 0 := by
      unfold GlobalTheory.Count.dHS
      simp
    rw [h0, h1]
    simp
  · have hg' : inUJ ε g := hg
    obtain ⟨h0, h1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn (mul_exp_neg_polarLog_mem_compact hg').1 (polarLog_mem_hermitian_part hg')
    rw [← polar_decomposition_eq] at h0 h1
    rw [GlobalTheory.Count.Cartan.dHS_eq_log hg']
    exact ⟨h0, h1⟩

end GlobalTheory.DecGapBound
