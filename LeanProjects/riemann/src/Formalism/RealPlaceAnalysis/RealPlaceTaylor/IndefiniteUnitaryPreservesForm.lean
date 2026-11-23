import Formalism.RealPlaceAnalysis.Complexify

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace Formalism.REAL

variable {n : ℕ}

private lemma Jm_mul_Jm_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

lemma isUnit_signature_matrix (ε : Fin n → Bool) : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, Jm_mul_Jm_eq_one ε, Jm_mul_Jm_eq_one ε⟩, rfl⟩

lemma signature_matrix_inv_self (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_Jm_eq_one ε)

lemma exp_signature_conj (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε := by
  have h := Matrix.exp_conj (Jm ε) A (isUnit_signature_matrix ε)
  rwa [signature_matrix_inv_self] at h

lemma isSelfAdjoint_of_conjTranspose_eq {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) : IsSelfAdjoint A := by
  exact hA

lemma exp_injective_hermitian {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  have h1 := congrArg CFC.log h
  first
  | rwa [CFC.log_exp A (isSelfAdjoint_of_conjTranspose_eq hA), CFC.log_exp B (isSelfAdjoint_of_conjTranspose_eq hB)] at h1
  | rwa [CFC.log_exp A, CFC.log_exp B] at h1

lemma exp_conjTranspose_of_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) :
    (NormedSpace.exp A)ᴴ = NormedSpace.exp A := by
  rw [← Matrix.exp_conjTranspose, hA]

lemma matrix_exp_neg_mul_exp (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl A)), neg_add_cancel]
  first | exact Matrix.exp_zero | exact NormedSpace.exp_zero

lemma matrix_exp_mul_exp_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel]
  first | exact Matrix.exp_zero | exact NormedSpace.exp_zero

lemma exp_add_self (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (A + A) = NormedSpace.exp A * NormedSpace.exp A := Matrix.exp_add_of_commute _ _ (Commute.refl A)

lemma eq_of_add_self_eq_add_self {A B : Matrix (Fin n) (Fin n) ℂ} (h : A + A = B + B) : A = B := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.add_apply] at h1
  linear_combination (1 / 2 : ℂ) * h1

lemma spectrum_pos_of_posSemidef_unit {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) (hu : IsUnit P) :
    ∀ x ∈ spectrum ℝ P, 0 < x := by
  intro x hx
  have h0 : 0 ≤ x := by
    open scoped MatrixOrder in
    first
    | exact spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx
    | exact spectrum_nonneg_of_nonneg hP.nonneg hx
  have hne : x ≠ 0 := by
    rintro rfl
    first
    | exact (spectrum.zero_notMem_iff ℝ).mpr hu hx
    | exact (spectrum.zero_not_mem_iff ℝ).mpr hu hx
  exact lt_of_le_of_ne h0 (Ne.symm hne)

lemma exp_log_of_pos_spectrum {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsSelfAdjoint P)
    (hs : ∀ x ∈ spectrum ℝ P, 0 < x) : NormedSpace.exp (CFC.log P) = P := by
  have hl : IsSelfAdjoint (CFC.log P) := cfc_predicate Real.log P
  refine Eq.trans (CFC.real_exp_eq_normedSpace_exp hl).symm ?_
  unfold CFC.log
  rw [← cfc_comp Real.exp Real.log P hP Real.continuous_exp.continuousOn
    (Real.continuousOn_log.mono fun x hx => (hs x hx).ne')]
  conv_rhs => rw [← cfc_id ℝ P hP]
  exact cfc_congr fun x hx => Real.exp_log (hs x hx)

lemma indefinite_unitary_preserves_form {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * Jm ε * gᴴ = Jm ε ∧ IsUnit g := by
  unfold inUJ at hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [mul_assoc]
      _ = 1 := by rw [hg, Jm_mul_Jm_eq_one]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := by
    first
    | exact mul_eq_one_comm.mp h1
    | exact (Matrix.mul_eq_one_comm).mp h1
    | exact Matrix.mul_eq_one_comm.1 h1
  refine ⟨?_, ⟨⟨g, _, h2, h1⟩, rfl⟩⟩
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
    _ = Jm ε := by rw [h2, one_mul]

def polarLog (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℝ) • CFC.log (gᴴ * g)

lemma polar_log_hermitian (g : Matrix (Fin n) (Fin n) ℂ) : (polarLog g)ᴴ = polarLog g := by
  have h1 : IsSelfAdjoint (CFC.log (gᴴ * g)) := by
    first
    | exact cfc_predicate Real.log (gᴴ * g)
    | exact CFC.log_isSelfAdjoint
  have h2 : IsSelfAdjoint ((1 / 2 : ℝ) • CFC.log (gᴴ * g)) := IsSelfAdjoint.smul (IsSelfAdjoint.all _) h1
  exact h2

lemma polarLog_add_self_eq_log (g : Matrix (Fin n) (Fin n) ℂ) :
    polarLog g + polarLog g = CFC.log (gᴴ * g) := by
  unfold polarLog
  rw [← add_smul]
  norm_num

lemma conjTranspose_mul_self_pos_facts {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g) ∧ ∀ x ∈ spectrum ℝ (gᴴ * g), 0 < x := by
  have hu : IsUnit g := (indefinite_unitary_preserves_form hg).2
  refine ⟨Matrix.isHermitian_conjTranspose_mul_self g, ?_, ?_⟩
  · exact (IsUnit.star hu).mul hu
  · exact spectrum_pos_of_posSemidef_unit (Matrix.posSemidef_conjTranspose_mul_self g) ((IsUnit.star hu).mul hu)

lemma exp_polarLog_double {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    NormedSpace.exp (polarLog g + polarLog g) = gᴴ * g := by
  rw [polarLog_add_self_eq_log]
  obtain ⟨h1, -, h3⟩ := conjTranspose_mul_self_pos_facts hg
  exact exp_log_of_pos_spectrum h1 h3

private lemma Jm_conjTranspose_eq_self (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

lemma polar_log_anticommutes_signature {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Jm ε * polarLog g * Jm ε = -polarLog g := by
  set L := polarLog g with hL
  have hH : Lᴴ = L := polar_log_hermitian g
  have hP : NormedSpace.exp (L + L) = gᴴ * g := exp_polarLog_double hg
  have hgJ : g * Jm ε * gᴴ = Jm ε := (indefinite_unitary_preserves_form hg).1
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hX : (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = 1 := by
    calc (Jm ε * (gᴴ * g) * Jm ε) * (gᴴ * g) = Jm ε * gᴴ * (g * Jm ε * gᴴ) * g := by
          simp only [mul_assoc]
      _ = Jm ε * (gᴴ * Jm ε * g) := by rw [hgJ]; simp only [mul_assoc]
      _ = 1 := by rw [hg', Jm_mul_Jm_eq_one]
  have hE : NormedSpace.exp (-(L + L)) = Jm ε * (gᴴ * g) * Jm ε := by
    have h0 : NormedSpace.exp (-(L + L)) * (gᴴ * g) = 1 := by
      rw [← hP]
      exact matrix_exp_neg_mul_exp _
    have h2 : (gᴴ * g) * (Jm ε * (gᴴ * g) * Jm ε) = 1 := by
      have h1 := hX
      first
      | exact mul_eq_one_comm.mp h1
      | exact (Matrix.mul_eq_one_comm).mp h1
      | exact Matrix.mul_eq_one_comm.1 h1
    calc NormedSpace.exp (-(L + L))
        = NormedSpace.exp (-(L + L)) * ((gᴴ * g) * (Jm ε * (gᴴ * g) * Jm ε)) := by rw [h2, mul_one]
      _ = Jm ε * (gᴴ * g) * Jm ε := by rw [← mul_assoc, h0, one_mul]
  have hA : (Jm ε * (L + L) * Jm ε)ᴴ = Jm ε * (L + L) * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self, Matrix.conjTranspose_add, hH,
      mul_assoc]
  have hB : (-(L + L))ᴴ = -(L + L) := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_add, hH]
  have hEq : Jm ε * (L + L) * Jm ε = -(L + L) :=
    exp_injective_hermitian hA hB (by rw [exp_signature_conj, hP, hE])
  apply eq_of_add_self_eq_add_self
  rw [← neg_add, ← hEq]
  simp only [mul_add, add_mul]

lemma polarLog_mem_hermitian_part {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    inP ε (polarLog g) := by
  have hJ := polar_log_anticommutes_signature hg
  have h2 : polarLog g * Jm ε = -(Jm ε * polarLog g) := by
    calc polarLog g * Jm ε = Jm ε * (Jm ε * polarLog g * Jm ε) := by
          rw [← mul_assoc, ← mul_assoc, Jm_mul_Jm_eq_one, one_mul]
      _ = -(Jm ε * polarLog g) := by rw [hJ, mul_neg]
  refine ⟨?_, h2⟩
  unfold inG
  rw [polar_log_hermitian, h2, neg_add_cancel]

lemma mul_exp_neg_polarLog_mem_compact {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * NormedSpace.exp (-polarLog g) ∈ Kset ε := by
  set L := polarLog g with hL
  have hH : Lᴴ = L := polar_log_hermitian g
  have hFF : NormedSpace.exp L * NormedSpace.exp L = gᴴ * g := by
    rw [← exp_add_self]
    exact exp_polarLog_double hg
  have hEF : NormedSpace.exp (-L) * NormedSpace.exp L = 1 := matrix_exp_neg_mul_exp L
  have hFE : NormedSpace.exp L * NormedSpace.exp (-L) = 1 := matrix_exp_mul_exp_neg L
  have hEH : (NormedSpace.exp (-L))ᴴ = NormedSpace.exp (-L) :=
    exp_conjTranspose_of_hermitian (by rw [Matrix.conjTranspose_neg, hH])
  have hJE : NormedSpace.exp (-L) = Jm ε * NormedSpace.exp L * Jm ε := by
    rw [← exp_signature_conj, polar_log_anticommutes_signature hg]
  have hgJ : g * Jm ε * gᴴ = Jm ε := (indefinite_unitary_preserves_form hg).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    calc star (g * NormedSpace.exp (-L)) * (g * NormedSpace.exp (-L))
        = NormedSpace.exp (-L) * (gᴴ * g) * NormedSpace.exp (-L) := by
          rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hEH]
          simp only [mul_assoc]
      _ = 1 := by
          rw [← hFF]
          simp only [← mul_assoc]
          rw [hEF, one_mul, hFE]
  · have h4 : g * Jm ε * (NormedSpace.exp L * NormedSpace.exp L) = Jm ε * g := by
      rw [hFF, ← mul_assoc, hgJ]
    calc g * NormedSpace.exp (-L) * Jm ε = g * Jm ε * NormedSpace.exp L := by
          rw [hJE]
          simp only [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
      _ = Jm ε * (g * NormedSpace.exp (-L)) := by
          rw [← mul_assoc, ← h4]
          simp only [mul_assoc]
          rw [hFE, mul_one]

lemma polar_decomposition_eq {g : Matrix (Fin n) (Fin n) ℂ} :
    g = g * NormedSpace.exp (-polarLog g) * NormedSpace.exp (polarLog g) := by
  rw [mul_assoc, matrix_exp_neg_mul_exp, mul_one]

lemma hermitian_of_mem_hermitian_part {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by
  obtain ⟨h1, h2⟩ := hX
  unfold inG at h1
  have h3 : Xᴴ * Jm ε = X * Jm ε := by
    rw [h2]
    exact eq_neg_of_add_eq_zero_left h1
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, Jm_mul_Jm_eq_one, mul_one]
    _ = X * Jm ε * Jm ε := by rw [h3]
    _ = X := by rw [mul_assoc, Jm_mul_Jm_eq_one, mul_one]

lemma polar_decomposition_unique {ε : Fin n → Bool} (k k' X X' : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) (hX : inP ε X) (hX' : inP ε X')
    (h : k * NormedSpace.exp X = k' * NormedSpace.exp X') : k = k' ∧ X = X' := by
  have hXh := hermitian_of_mem_hermitian_part hX
  have hX'h := hermitian_of_mem_hermitian_part hX'
  have hk1 : k ∈ unitaryGroup (Fin n) ℂ := by
    unfold Kset at hk
    exact hk.1
  have hk1' : k' ∈ unitaryGroup (Fin n) ℂ := by
    unfold Kset at hk'
    exact hk'.1
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk1
  have hu' : star k' * k' = 1 := Matrix.mem_unitaryGroup_iff'.mp hk1'
  have key : ∀ (c Y : Matrix (Fin n) (Fin n) ℂ), star c * c = 1 →
      (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y →
      (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    intro c Y hc hY
    rw [Matrix.conjTranspose_mul, hY, exp_add_self]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (star c * c) * NormedSpace.exp Y := by
          rw [Matrix.star_eq_conjTranspose]
          simp only [mul_assoc]
      _ = _ := by rw [hc, mul_one]
  have h2 : NormedSpace.exp (X + X) = NormedSpace.exp (X' + X') := by
    rw [← key k X hu (exp_conjTranspose_of_hermitian hXh), ← key k' X' hu' (exp_conjTranspose_of_hermitian hX'h), h]
  have hXX : X = X' := eq_of_add_self_eq_add_self (exp_injective_hermitian (by rw [Matrix.conjTranspose_add, hXh])
    (by rw [Matrix.conjTranspose_add, hX'h]) h2)
  subst hXX
  refine ⟨?_, rfl⟩
  calc k = k * NormedSpace.exp X * NormedSpace.exp (-X) := by
        rw [mul_assoc, matrix_exp_mul_exp_neg, mul_one]
    _ = k' * NormedSpace.exp X * NormedSpace.exp (-X) := by rw [h]
    _ = k' := by rw [mul_assoc, matrix_exp_mul_exp_neg, mul_one]

lemma continuousOn_polarLog (ε : Fin n → Bool) : ContinuousOn (polarLog (n := n)) {g | inUJ ε g} := by
  have hc : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * g) {g | inUJ ε g} :=
    (continuous_star.mul continuous_id).continuousOn
  have hlog : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} :=
    CFC.continuousOn_log.comp hc (fun g hg => by
      show IsSelfAdjoint (gᴴ * g) ∧ IsUnit (gᴴ * g)
      exact ⟨(conjTranspose_mul_self_pos_facts hg).1, (conjTranspose_mul_self_pos_facts hg).2.1⟩)
  exact hlog.const_smul (1 / 2 : ℝ)

theorem polar_decomposition_holds : Polar := by
  intro n ε
  refine ⟨fun g hg => ⟨g * NormedSpace.exp (-polarLog g), polarLog g, mul_exp_neg_polarLog_mem_compact hg,
      polarLog_mem_hermitian_part hg, polar_decomposition_eq⟩,
    fun k k' X X' hk hk' hX hX' h => polar_decomposition_unique k k' X X' hk hk' hX hX' h,
    ⟨polarLog, continuousOn_polarLog ε, fun g hg => ⟨polarLog_mem_hermitian_part hg, mul_exp_neg_polarLog_mem_compact hg⟩⟩⟩

end Formalism.REAL
