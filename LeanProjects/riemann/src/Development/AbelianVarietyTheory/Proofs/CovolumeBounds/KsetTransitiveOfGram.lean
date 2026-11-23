import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsConeMeasure
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsConeMeasurePosRank
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryOfGramEq
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.Poisson

theorem unitary_comm_of_gram {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  set P : Matrix (Fin n) (Fin n) ℂ := (2⁻¹ : ℂ) • (1 + H) with hP
  have hPh : Pᴴ = P := by
    simp [hP, conjTranspose_smul, conjTranspose_add, hH]
  have hPP : P * P = P := by
    simp only [hP, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hHH]
    module
  have hHP : H = (2 : ℂ) • P - 1 := by
    simp only [hP]
    module
  have hG : Aᴴ * P * A = Bᴴ * P * B := by
    simp only [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, h2]
  clear_value P
  have hQh : (1 - P)ᴴ = 1 - P := by simp [hPh]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hG' : Aᴴ * (1 - P) * A = Bᴴ * (1 - P) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, hG]
  have key : ∀ E : Matrix (Fin n) (Fin n) ℂ, Eᴴ = E → E * E = E → Aᴴ * E * A = Bᴴ * E * B →
      ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * (E * A) = E * B := by
    intro E hE hEE hg
    have e : ∀ C : Matrix (Fin n) (Fin m) ℂ, (E * C)ᴴ * (E * C) = Cᴴ * E * C := by
      intro C
      rw [conjTranspose_mul, hE, Matrix.mul_assoc, ← Matrix.mul_assoc E E, hEE, Matrix.mul_assoc]
    refine GlobalTheory.UnitaryExtension.exists_unitary_of_gram_eq n m E (E * A) (E * B) hE hEE ?_ ?_ ?_
    · rw [← Matrix.mul_assoc, hEE]
    · rw [← Matrix.mul_assoc, hEE]
    · rw [e, e, hg]
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := key P hPh hPP hG
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := key (1 - P) hQh hQQ hG'
  rw [sub_sub_cancel] at hV3
  have hV5 : V * P = P * V := by
    have := hV2
    simp only [mul_sub, sub_mul, one_mul, mul_one] at this
    exact sub_right_injective this
  refine ⟨U * V, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hV1]
  · have : U * V * P = P * (U * V) := by
      rw [mul_assoc, hV5, ← mul_assoc, hU2, mul_assoc]
    rw [hHP]
    simp only [mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, this]
  · have hA : A = P * A + (1 - P) * A := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    have hB : B = P * B + (1 - P) * B := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    calc U * V * A = U * (V * (P * A + (1 - P) * A)) := by rw [← hA, Matrix.mul_assoc]
      _ = U * (P * A + (1 - P) * B) := by
        rw [Matrix.mul_add, hV4, ← Matrix.mul_assoc V P, hV3]
      _ = P * B + (1 - P) * B := by
        rw [Matrix.mul_add, hU4, ← Matrix.mul_assoc U (1 - P), hU3]
      _ = B := hB.symm

theorem kset_transitive_of_gram : ∀ (k r m : ℕ) (A B : Matrix (Fin (2 * r + k + 1)) (Fin m) ℂ),
    Aᴴ * A = Bᴴ * B → Aᴴ * Hpk k r * A = Bᴴ * Hpk k r * B → ∃ κ ∈ Kset k r, κ * A = B := by
  intro k r m A B h1 h2
  have hF := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  obtain ⟨U, hU1, hU2, hU3⟩ := unitary_comm_of_gram (Hpk k r) hF.1 hF.2.1 A B h1 h2
  refine ⟨U, ⟨?_, hU1⟩, hU3⟩
  show Uᴴ * Hpk k r * U = Hpk k r
  rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, hU1, Matrix.one_mul]

lemma sqLen_nonneg' {n : ℕ} (v : Fin n → ℂ) : 0 ≤ sqLen v :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

lemma sqLen_pos' {n : ℕ} {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < sqLen v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

lemma sqLen_smul' {n : ℕ} (c : ℂ) (v : Fin n → ℂ) : sqLen (c • v) = Complex.normSq c * sqLen v := by
  simp [sqLen, Finset.mul_sum]

lemma star_dot_self {n : ℕ} (v : Fin n → ℂ) : star v ⬝ᵥ v = (sqLen v : ℂ) := by
  simp [sqLen, dotProduct, Complex.normSq_eq_conj_mul_self]

lemma continuous_sqLen' {n : ℕ} : Continuous (sqLen : (Fin n → ℂ) → ℝ) := by
  unfold sqLen
  exact continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

lemma mul_mem_GV {k r : ℕ} {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma mulVec_ne_zero {k r : ℕ} {a : Mat k r} (ha : a ∈ GV k r) {y : Fin (2 * r + k + 1) → ℂ}
    (hy : y ≠ 0) : a *ᵥ y ≠ 0 := by
  intro h
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hH : (Hpk k r)ᴴ * Hpk k r = 1 := (GlobalTheory.HCXi.KGroup.kset_facts k r).2.2.1.2
  apply hy
  calc y = ((Hpk k r)ᴴ * (aᴴ * Hpk k r * a)) *ᵥ y := by rw [ha', hH, Matrix.one_mulVec]
    _ = ((Hpk k r)ᴴ * (aᴴ * Hpk k r)) *ᵥ (a *ᵥ y) := by
        rw [Matrix.mulVec_mulVec]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

lemma exists_translate {k r : ℕ} {x v : Fin (2 * r + k + 1) → ℂ} (hx0 : herm (Hpk k r) x x = 0)
    (hx1 : sqLen x = 1) (hv0 : herm (Hpk k r) v v = 0) :
    ∃ κ ∈ Kset k r, ∃ c : ℂ, Complex.normSq c = sqLen v ∧ v = c • (κ *ᵥ x) := by
  set c : ℂ := ((Real.sqrt (sqLen v) : ℝ) : ℂ) with hc
  have hcn : Complex.normSq c = sqLen v := by
    rw [hc, Complex.normSq_ofReal, Real.mul_self_sqrt (sqLen_nonneg' v)]
  have key : ∀ (M : Mat k r) (y : Fin (2 * r + k + 1) → ℂ),
      (replicateCol (Fin 1) y)ᴴ * M * replicateCol (Fin 1) y = Matrix.of fun _ _ => star y ⬝ᵥ (M *ᵥ y) := by
    intro M y
    rw [Matrix.mul_assoc, ← replicateCol_mulVec, conjTranspose_replicateCol]
    ext i j
    simp [replicateRow_mul_replicateCol_apply]
  obtain ⟨κ, hκ, h⟩ := kset_transitive_of_gram k r 1 (replicateCol (Fin 1) (c • x)) (replicateCol (Fin 1) v)
    (by
      have h1 := key 1 (c • x)
      have h2 := key 1 v
      rw [Matrix.mul_one, Matrix.one_mulVec, star_dot_self] at h1 h2
      rw [h1, h2, sqLen_smul', hx1, hcn, mul_one])
    (by
      rw [key, key]
      have h1 : star v ⬝ᵥ (Hpk k r *ᵥ v) = 0 := hv0
      have h2 : star x ⬝ᵥ (Hpk k r *ᵥ x) = 0 := hx0
      rw [h1, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, h2, smul_zero, smul_zero])
  refine ⟨κ, hκ, c, hcn, ?_⟩
  rw [← replicateCol_mulVec] at h
  have := replicateCol_injective h
  rw [← this, Matrix.mulVec_smul]

lemma core (k r : ℕ) (μK : Measure (Mt k r)) (x : Fin (2 * r + k + 1) → ℂ) (hK : IsKMeas k r μK)
    (hx0 : herm (Hpk k r) x x = 0) (hx1 : sqLen x = 1) (g : Mat k r) (hg : g ∈ GV k r)
    (m : Measure (Fin (2 * r + k + 1) → ℂ)) [SFinite m] (d : ℝ)
    (hae : ∀ᵐ v ∂m, v ≠ 0 ∧ herm (Hpk k r) v v = 0)
    (hhom : ∀ s : ℝ, 0 < s → ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ v, f (s * sqLen v) ∂m) = ENNReal.ofReal (s ^ d) * ∫⁻ v, f (sqLen v) ∂m)
    (h0 : (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ 0)
    (htop : (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) ≠ ∞)
    (hinv : ∀ g ∈ GV k r, (∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ v))) ∂m) =
      ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m) :
    (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) ∂μK) = 1 := by
  haveI : IsProbabilityMeasure μK := ⟨hK.2⟩
  set Γ := ∫⁻ v, ENNReal.ofReal (Real.exp (-sqLen v)) ∂m with hΓ
  have hmem : ∀ᵐ κ : Mt k r ∂μK, Matrix.of κ ∈ Kset k r := hK.1.conc
  have hx : x ≠ 0 := by
    rintro rfl
    simp [sqLen] at hx1
  have hcg : Continuous fun κ : Mt k r => g * Matrix.of κ :=
    continuous_const.matrix_mul (continuous_id (X := Mat k r))
  have hcs : Continuous fun p : Mt k r × (Fin (2 * r + k + 1) → ℂ) =>
      sqLen ((g * Matrix.of p.1) *ᵥ p.2) :=
    continuous_sqLen'.comp ((hcg.comp continuous_fst).matrix_mulVec continuous_snd)
  have hcx : Continuous fun κ : Mt k r => sqLen ((g * Matrix.of κ) *ᵥ x) :=
    continuous_sqLen'.comp (hcg.matrix_mulVec continuous_const)
  have hm1 : Measurable fun p : Mt k r × (Fin (2 * r + k + 1) → ℂ) =>
      ENNReal.ofReal (Real.exp (-sqLen ((g * Matrix.of p.1) *ᵥ p.2))) :=
    (Real.continuous_exp.comp hcs.neg).measurable.ennreal_ofReal
  have hm2 : Measurable fun p : Mt k r × (Fin (2 * r + k + 1) → ℂ) =>
      ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of p.1) *ᵥ x) * sqLen p.2))) :=
    (Real.continuous_exp.comp ((hcx.comp continuous_fst).mul
      (continuous_sqLen'.comp continuous_snd)).neg).measurable.ennreal_ofReal
  have e1 : Γ = ∫⁻ κ : Mt k r, ∫⁻ v,
      ENNReal.ofReal (Real.exp (-sqLen ((g * Matrix.of κ) *ᵥ v))) ∂m ∂μK := by
    rw [lintegral_congr_ae (g := fun _ => Γ)]
    · simp
    · filter_upwards [hmem] with κ hκ using hinv _ (mul_mem_GV hg hκ.1)
  have e2 : ∀ᵐ v ∂m, (∫⁻ κ : Mt k r,
      ENNReal.ofReal (Real.exp (-sqLen ((g * Matrix.of κ) *ᵥ v))) ∂μK) =
      ∫⁻ κ : Mt k r, ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of κ) *ᵥ x) * sqLen v))) ∂μK := by
    filter_upwards [hae] with v hv
    obtain ⟨a, ha, c, hc, hv'⟩ := exists_translate hx0 hx1 hv.2
    have hr : Measurable (rmulF a) := by
      have : Continuous (rmulF a) := (continuous_id (X := Mat k r)).matrix_mul continuous_const
      exact this.measurable
    have hf : Measurable fun κ : Mt k r =>
        ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of κ) *ᵥ x) * sqLen v))) :=
      (Real.continuous_exp.comp (hcx.mul continuous_const).neg).measurable.ennreal_ofReal
    conv_rhs => rw [← hK.1.right a ha]
    rw [lintegral_map hf hr]
    refine lintegral_congr fun κ => ?_
    have : Matrix.of (rmulF a κ) = Matrix.of κ * a := rfl
    rw [this, ← hc, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec x _ a, mul_comm _ (Complex.normSq c), ← sqLen_smul',
      ← Matrix.mulVec_smul, ← hv']
  have e3 : ∀ᵐ κ : Mt k r ∂μK,
      (∫⁻ v, ENNReal.ofReal (Real.exp (-(sqLen ((g * Matrix.of κ) *ᵥ x) * sqLen v))) ∂m) =
      ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) * Γ := by
    filter_upwards [hmem] with κ hκ
    exact hhom _ (sqLen_pos' (mulVec_ne_zero (mul_mem_GV hg hκ.1) hx))
      (fun t => ENNReal.ofReal (Real.exp (-t)))
      (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal
  have e4 : Γ = (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) ∂μK) * Γ := by
    calc Γ = _ := e1
      _ = _ := lintegral_lintegral_swap hm1.aemeasurable
      _ = _ := lintegral_congr_ae e2
      _ = _ := (lintegral_lintegral_swap hm2.aemeasurable).symm
      _ = _ := lintegral_congr_ae e3
      _ = _ := lintegral_mul_const' _ _ htop
  have e5 : (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ d) ∂μK) * Γ = 1 * Γ := by
    rw [one_mul, ← e4]
  exact (ENNReal.mul_left_inj h0 htop).mp e5

theorem poisson_integral : ∀ (k r : ℕ) (μK : Measure (Mt k r)) (x : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → IsKMeas k r μK → herm (Hpk k r) x x = 0 → sqLen x = 1 → ∀ g ∈ GV k r, (∫⁻ κ : Mt k r, ENNReal.ofReal (sqLen ((g * Matrix.of κ) *ᵥ x) ^ (-((2 * r + k : ℕ) : ℝ))) ∂μK) = 1 := by
  intro k r μK x hk hK hx0 hx1 g hg
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · obtain ⟨m, hs, hae, hhom, h0, htop, hinv⟩ := GlobalTheory.HCXi.ConeZero.exists_coneMeasure k hk
    exact core k 0 μK x hK hx0 hx1 g hg m _ hae hhom h0 htop hinv
  · obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨m, hs, hae, hhom, h0, htop, hinv⟩ := GlobalTheory.HCXi.exists_cone_measure_pos_rank k r'
    exact core k _ μK x hK hx0 hx1 g hg m _ hae hhom h0 htop hinv

end GlobalTheory.HCXi.Poisson
