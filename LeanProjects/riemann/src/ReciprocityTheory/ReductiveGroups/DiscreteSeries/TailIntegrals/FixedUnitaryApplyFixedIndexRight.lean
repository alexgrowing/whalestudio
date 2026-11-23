import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def iW (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 0

def iK (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 (Fin.last k)

def Pk (k : ℕ) : Mat k 0 := Matrix.single (iK k) (iK k) 1

def U0 (k : ℕ) : Set (Mat k 0) := UWset k 0 (bvec (iK k))

lemma iW_ne_iK {k : ℕ} (hk : 1 ≤ k) : iW k ≠ iK k := by
  intro h
  have := congrArg Fin.val h
  simp [iW, iK, wI] at this
  omega

lemma hpk0 (k : ℕ) : Hpk k 0 = 1 - 2 • Pk k := by
  ext i j
  have hi := i.isLt
  have hle : i.val ≤ k := by omega
  by_cases hij : i = j
  · subst hij
    by_cases hik : i.val = k
    · simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik]
      norm_num
    · have hik' : k ≠ i.val := fun h => hik h.symm
      simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hik, hik', hle]
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [Hpk, Pk, iK, wI, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, hv]
    omega

lemma Pk_mul_self (k : ℕ) : Pk k * Pk k = Pk k := by
  simp [Pk]

lemma Pk_conjTranspose (k : ℕ) : (Pk k)ᴴ = Pk k := by
  simp [Pk]

lemma one_sub_mul_Pk (k : ℕ) : (1 - 2 • Pk k) * Pk k = -Pk k := by
  rw [sub_mul, one_mul, smul_mul_assoc, Pk_mul_self, two_smul]
  abel

lemma fixedUnitary_projection_identities {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) :
    hᴴ * h = 1 ∧ h * Pk k = Pk k ∧ hᴴ * Pk k = Pk k ∧ Pk k * h = Pk k := by
  obtain ⟨hU, -, hv⟩ := hh
  have hU' : hᴴ * Hpk k 0 * h = Hpk k 0 := hU
  have hcol : ∀ i, h i (iK k) = if i = iK k then 1 else 0 := by
    intro i
    have := congrFun hv i
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using this
  have hP : h * Pk k = Pk k := by
    ext i j
    by_cases hj : iK k = j
    · subst hj
      by_cases hi : i = iK k
      · subst hi
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol]
      · have hi' : iK k ≠ i := fun e => hi e.symm
        simp [Pk, Matrix.mul_apply, Matrix.single_apply, hcol, hi, hi']
    · simp [Pk, Matrix.mul_apply, Matrix.single_apply, hj]
  have hsP : hᴴ * Pk k = Pk k := by
    have e1 : hᴴ * Hpk k 0 * h * Pk k = Hpk k 0 * Pk k := by rw [hU']
    rw [Matrix.mul_assoc, hP, hpk0, Matrix.mul_assoc, one_sub_mul_Pk, Matrix.mul_neg] at e1
    exact neg_inj.mp e1
  have hPh : Pk k * h = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, hP, hsP, hPh⟩
  have e2 := hU'
  rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    hsP, hPh] at e2
  exact sub_left_inj.mp e2

lemma mem_fixedUnitary_of_unitary_fixes {k : ℕ} {R : Mat k 0} (hu : Rᴴ * R = 1) (hP : R * Pk k = Pk k) : R ∈ U0 k := by
  have hsP : Rᴴ * Pk k = Pk k := by
    calc Rᴴ * Pk k = Rᴴ * (R * Pk k) := by rw [hP]
      _ = Pk k := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hPR : Pk k * R = Pk k := by
    have := congrArg Matrix.conjTranspose hsP
    simpa [Matrix.conjTranspose_mul, Pk_conjTranspose] using this
  refine ⟨?_, fun a => a.elim0, ?_⟩
  · show Rᴴ * Hpk k 0 * R = Hpk k 0
    rw [hpk0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu, Matrix.mul_smul, Matrix.smul_mul,
      hsP, hPR]
  · ext i
    have := congrFun (congrFun hP i) (iK k)
    simpa [Pk, Matrix.mul_apply, Matrix.single_apply, Matrix.mulVec, dotProduct, bvec,
      Pi.single_apply, eq_comm] using this

lemma fixedUnitary_conjTranspose_mem {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) : hᴴ ∈ U0 k := by
  obtain ⟨hu, -, hsP, -⟩ := fixedUnitary_projection_identities hh
  refine mem_fixedUnitary_of_unitary_fixes ?_ hsP
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hu

lemma fixedUnitary_apply_fixedIndex_left {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (j : Fin (2 * 0 + k + 1)) :
    h (iK k) j = if j = iK k then 1 else 0 := by
  have := congrFun (congrFun (fixedUnitary_projection_identities hh).2.2.2 (iK k)) j
  simpa [Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm] using this

lemma fixedUnitary_apply_fixedIndex_right {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (i : Fin (2 * 0 + k + 1)) :
    h i (iK k) = if i = iK k then 1 else 0 := by
  have := congrFun (congrFun (fixedUnitary_projection_identities hh).2.1 i) (iK k)
  simpa [Pk, Matrix.mul_apply, Matrix.single_apply, eq_comm] using this

lemma fixedUnitary_mulVec_fixedIndex {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (y : Fin (2 * 0 + k + 1) → ℂ) :
    (h *ᵥ y) (iK k) = y (iK k) := by
  simp [Matrix.mulVec, dotProduct, fixedUnitary_apply_fixedIndex_left hh]

lemma fixedUnitary_preserves_normSq {k : ℕ} {h : Mat k 0} (hh : h ∈ U0 k) (y : Fin (2 * 0 + k + 1) → ℂ) :
    star (h *ᵥ y) ⬝ᵥ (h *ᵥ y) = star y ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (fixedUnitary_projection_identities hh).1,
    Matrix.one_mulVec]

lemma exists_fixedUnitary_sending_basis {k : ℕ} (hk : 1 ≤ k) (u : Fin (2 * 0 + k + 1) → ℂ) (hu0 : u (iK k) = 0)
    (hu1 : star u ⬝ᵥ u = 1) : ∃ R ∈ U0 k, R *ᵥ bvec (iW k) = u := by
  classical
  have hWK : iW k ≠ iK k := iW_ne_iK hk

  obtain ⟨μ, hμ1, hμr⟩ : ∃ μ : ℂ, star μ * μ = 1 ∧
      star (star μ * u (iW k)) = star μ * u (iW k) := by
    by_cases h0 : u (iW k) = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn : ((‖u (iW k)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      have hc : star (u (iW k)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      have hs : star ((‖u (iW k)‖ : ℝ) : ℂ) = ((‖u (iW k)‖ : ℝ) : ℂ) := Complex.conj_ofReal _
      have hval : star (u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ)) * u (iW k) = ((‖u (iW k)‖ : ℝ) : ℂ) := by
        rw [star_div₀, hs, div_mul_eq_mul_div, hc]
        field_simp
      refine ⟨u (iW k) / ((‖u (iW k)‖ : ℝ) : ℂ), ?_, ?_⟩
      · rw [star_div₀, hs, div_mul_div_comm, hc]
        field_simp
      · rw [hval, hs]

  obtain ⟨d, hd⟩ : ∃ d : Fin (2 * 0 + k + 1) → ℂ, d = Function.update (fun _ => 1) (iW k) μ :=
    ⟨_, rfl⟩
  have hdW : d (iW k) = μ := by simp [hd]
  have hdo : ∀ i, i ≠ iW k → d i = 1 := by
    intro i hi
    simp [hd, hi]
  have hDu : (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases hi : i = iW k
    · subst hi
      simp [hdW]
      exact hμ1
    · simp [hdo i hi]
  have hDP : Matrix.diagonal d * Pk k = Pk k := by
    ext i j
    by_cases hi : i = iK k
    · subst hi
      simp [Matrix.diagonal_mul, hdo _ (Ne.symm hWK)]
    · simp [Matrix.diagonal_mul, Pk, Matrix.single_apply, Ne.symm hi]
  have hDe : Matrix.diagonal d *ᵥ bvec (iW k) = μ • bvec (iW k) := by
    ext i
    by_cases hi : i = iW k
    · subst hi
      simp [Matrix.mulVec_diagonal, hdW, bvec]
    · simp [Matrix.mulVec_diagonal, bvec, Pi.single_apply, hi]
  obtain ⟨x, hx⟩ : ∃ x : Fin (2 * 0 + k + 1) → ℂ, x = μ • bvec (iW k) := ⟨_, rfl⟩
  by_cases hxu : x = u
  · refine ⟨Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes hDu hDP, ?_⟩
    rw [hDe, ← hx, hxu]

  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * 0 + k + 1) → ℂ, w = x - u := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    rw [hw]
    exact sub_ne_zero.mpr hxu
  have hn : star w ⬝ᵥ w ≠ 0 := fun h => hw0 (dotProduct_star_self_eq_zero.mp h)
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = 2 * (star w ⬝ᵥ w)⁻¹ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Mat k 0, W = Matrix.vecMulVec w (star w) := ⟨_, rfl⟩
  have hWv : ∀ v, W *ᵥ v = (star w ⬝ᵥ v) • w := by
    intro v
    ext i
    simp only [hW, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hWW : W * W = (star w ⬝ᵥ w) • W := by
    ext i j
    simp only [hW, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hWh : Wᴴ = W := by
    ext i j
    simp [hW, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  have hnr : star (star w ⬝ᵥ w) = star w ⬝ᵥ w := by
    simp [dotProduct, star_sum, mul_comm]
  have hsr : star s = s := by
    rw [hs, star_mul', star_inv₀, hnr, star_ofNat]
  obtain ⟨Hh, hHh⟩ : ∃ Hh : Mat k 0, Hh = 1 - s • W := ⟨_, rfl⟩
  have hHhs : Hhᴴ = Hh := by
    rw [hHh, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hsr, hWh]
  have hsn : s * (s * (star w ⬝ᵥ w)) = 2 * s := by
    rw [hs]
    field_simp
  have hHH : Hh * Hh = 1 := by
    rw [hHh]
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc, mul_smul_comm,
      hWW, smul_smul, smul_sub]
    have h2 : (s * (s * (star w ⬝ᵥ w))) • W = s • W + s • W := by
      rw [hsn, ← add_smul, ← two_mul]
    rw [h2]
    abel
  obtain ⟨α, hα⟩ : ∃ α : ℂ, α = star μ * u (iW k) := ⟨_, rfl⟩
  have hxv : ∀ v, star x ⬝ᵥ v = star μ * v (iW k) := by
    intro v
    rw [hx]
    simp only [dotProduct]
    rw [Finset.sum_eq_single (iW k)]
    · simp [bvec]
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hvx : ∀ v, star v ⬝ᵥ x = star (v (iW k)) * μ := by
    intro v
    rw [hx]
    simp only [dotProduct]
    rw [Finset.sum_eq_single (iW k)]
    · simp [bvec]
    · intro j _ hj
      simp [bvec, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hxx : star x ⬝ᵥ x = 1 := by
    rw [hvx, hx]
    simpa [bvec, mul_comm] using hμ1
  have hxu' : star x ⬝ᵥ u = α := by rw [hxv, hα]
  have hux : star u ⬝ᵥ x = α := by
    have h1 := hμr
    rw [star_mul, star_star] at h1
    rw [hvx, h1, ← hα]
  have hwx : star w ⬝ᵥ x = 1 - α := by
    rw [hw, star_sub, sub_dotProduct, hxx, hux]
  have hwn : star w ⬝ᵥ w = 2 - 2 * α := by
    rw [hw, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hxx, hxu', hux, hu1]
    ring
  have hn' : (2 - 2 * α : ℂ) ≠ 0 := hwn ▸ hn
  have hs1 : s * (1 - α) = 1 := by
    rw [hs, hwn]
    have : (1 - α : ℂ) ≠ 0 := by
      intro h
      apply hn'
      linear_combination 2 * h
    field_simp
  refine ⟨Hh * Matrix.diagonal d, mem_fixedUnitary_of_unitary_fixes ?_ ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hHhs, Matrix.mul_assoc, ← Matrix.mul_assoc Hh Hh, hHH,
      Matrix.one_mul, hDu]
  · have hwk : w (iK k) = 0 := by
      rw [hw, hx]
      simp [hu0, bvec, Pi.single_apply, Ne.symm hWK]
    have hWP : W * Pk k = 0 := by
      ext i j
      simp [hW, Pk, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.single_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      split_ifs with hl
      · rw [← hl.1, hwk]
        simp
      · rfl
    rw [Matrix.mul_assoc, hDP, hHh, sub_mul, Matrix.one_mul, smul_mul_assoc, hWP, smul_zero,
      sub_zero]
  · have hsm : (s • W) *ᵥ x = s • (W *ᵥ x) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [← Matrix.mulVec_mulVec, hDe, ← hx, hHh, Matrix.sub_mulVec, Matrix.one_mulVec, hsm, hWv, hwx, smul_smul, hs1, one_smul, hw, sub_sub_cancel]

end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
