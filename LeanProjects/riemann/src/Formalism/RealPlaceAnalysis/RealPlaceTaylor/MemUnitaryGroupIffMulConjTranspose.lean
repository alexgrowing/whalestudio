import Formalism.RealPlaceAnalysis.Complexify

open Matrix

noncomputable section

namespace Formalism.REAL

private lemma Jm_mul_self_eq_oneRealPlaceTaylor {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private lemma Jm_conjTranspose_eq {n : ℕ} (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

lemma f1alg_isUnit_J {n : ℕ} (ε : Fin n → Bool) : IsUnit (Jm ε) :=
  ⟨⟨Jm ε, Jm ε, Jm_mul_self_eq_oneRealPlaceTaylor ε, Jm_mul_self_eq_oneRealPlaceTaylor ε⟩, rfl⟩

lemma f1alg_inv_J {n : ℕ} (ε : Fin n → Bool) : (Jm ε)⁻¹ = Jm ε :=
  Matrix.inv_eq_left_inv (Jm_mul_self_eq_oneRealPlaceTaylor ε)

lemma f1alg_cancel {n : ℕ} (ε : Fin n → Bool) {A B : Matrix (Fin n) (Fin n) ℂ}
    (h : A * Jm ε = B * Jm ε) : A = B := by
  have h2 := congrArg (· * Jm ε) h
  simpa [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor] using h2

lemma f1alg_JJ_left {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.one_mul]

lemma f1alg_theta_mul {n : ℕ} (ε : Fin n → Bool) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (A * B) * Jm ε = (Jm ε * A * Jm ε) * (Jm ε * B * Jm ε) := by
  simp only [Matrix.mul_assoc, f1alg_JJ_left]

lemma f1alg_theta_theta {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A * Jm ε) * Jm ε = A := by
  simp only [Matrix.mul_assoc, f1alg_JJ_left, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]

lemma f1alg_comm_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = Jm ε * A ↔ Jm ε * A * Jm ε = A := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, f1alg_JJ_left]
  · intro h
    calc A * Jm ε = (Jm ε * A * Jm ε) * Jm ε := by rw [h]
      _ = Jm ε * A := by rw [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]

lemma f1alg_anti_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = -(Jm ε * A) ↔ Jm ε * A * Jm ε = -A := by
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.mul_neg, f1alg_JJ_left]
  · intro h
    calc A * Jm ε = -(Jm ε * A * Jm ε) * Jm ε := by rw [h, neg_neg]
      _ = -(Jm ε * A) := by rw [Matrix.neg_mul, Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]

lemma f1alg_inG_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ Xᴴ = -(Jm ε * X * Jm ε) := by
  unfold inG
  constructor
  · intro h
    have h' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h', Matrix.neg_mul]
  · intro h
    rw [h, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self_eq_oneRealPlaceTaylor, Matrix.mul_one, neg_add_cancel]

lemma f1alg_inK_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ Xᴴ = -X ∧ X * Jm ε = Jm ε * X := by
  unfold inK
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_comm_iff ε X).mp h2], h2⟩

lemma mem_cartanP_iff {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inP ε X ↔ Xᴴ = X ∧ X * Jm ε = -(Jm ε * X) := by
  unfold inP
  rw [f1alg_inG_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, (f1alg_anti_iff ε X).mp h2, neg_neg], h2⟩

lemma f1alg_exp_inUJ {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : inG ε Y) :
    inUJ ε (NormedSpace.exp Y) := by
  unfold inUJ
  have hY' : Yᴴ = Jm ε * (-Y) * Jm ε := by
    rw [(f1alg_inG_iff ε Y).mp hY, Matrix.mul_neg, Matrix.neg_mul]
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, Jm_mul_self_eq_oneRealPlaceTaylor ε, Jm_mul_self_eq_oneRealPlaceTaylor ε⟩
  have hconj : NormedSpace.exp (Jm ε * (-Y) * Jm ε) = Jm ε * NormedSpace.exp (-Y) * Jm ε :=
    Matrix.exp_units_conj U (-Y)
  have hinv : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hY', hconj]
  simp only [Matrix.mul_assoc]
  rw [f1alg_JJ_left, hinv, Matrix.mul_one]

theorem indefinite_unitary_closed : UJClosed := by
  intro n ε
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exp_indefinite_unitary_holds : ExpUJ := by
  intro n ε X hX t
  apply f1alg_exp_inUJ
  unfold inG at hX ⊢
  have hs : ((t : ℂ) • X)ᴴ = (t : ℂ) • Xᴴ := by
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem indefinite_unitary_inv_closed : UJInv := by
  intro n ε g h
  have h2 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_self_eq_oneRealPlaceTaylor]
  exact ⟨mul_eq_one_comm.mp h2, h2⟩

theorem one_parameter_subgroup_holds : OneParam := by
  intro n X s t
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

theorem parabolic_character_holds : PChar := by
  intro n ε X
  exact ⟨mem_cartanP_iff ε X, fun h => (f1alg_anti_iff ε X).mp h.2⟩

lemma f1alg_unit_iff {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ gᴴ * g = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

lemma mem_unitaryGroup_iff_mul_conjTranspose {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Matrix.unitaryGroup (Fin n) ℂ ↔ g * gᴴ = 1 := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]

theorem maximal_compact_facts : KFacts := by
  intro n ε

  have h1 : ∀ g ∈ Kset ε, inUJ ε g := by
    rintro g ⟨hu, hc⟩
    unfold inUJ
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, (f1alg_unit_iff g).mp hu, Matrix.one_mul]

  have h5 : ∀ g, g ∈ Kset ε ↔ (inUJ ε g ∧ g ∈ Matrix.unitaryGroup (Fin n) ℂ) := by
    intro g
    constructor
    · intro hg
      exact ⟨h1 g hg, hg.1⟩
    · rintro ⟨hJ, hu⟩
      refine ⟨hu, ?_⟩
      unfold inUJ at hJ
      calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [hJ]
        _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
        _ = Jm ε * g := by rw [(mem_unitaryGroup_iff_mul_conjTranspose g).mp hu, Matrix.one_mul]
  refine ⟨h1, ?_, ?_, ?_, h5⟩
  ·
    have hcl : IsClosed (Kset ε) := by
      have : Kset ε = {g | gᴴ * g = 1} ∩ {g | g * Jm ε = Jm ε * g} := by
        ext g
        simp only [Kset, Set.mem_setOf_eq, Set.mem_inter_iff, f1alg_unit_iff]
      rw [this]
      exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id))
    have hsub : Kset ε ⊆ Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
        (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) := by
      intro g hg i _ j _
      rw [Metric.mem_closedBall, dist_zero_right]
      exact entry_norm_bound_of_unitary hg.1 i j
    exact IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _) hcl hsub
  · refine ⟨?_, rfl⟩
    rw [f1alg_unit_iff, Jm_conjTranspose_eq, Jm_mul_self_eq_oneRealPlaceTaylor]
  · rintro X ⟨hG, hc⟩
    have hX : Xᴴ = -X := ((f1alg_inK_iff ε X).mp ⟨hG, hc⟩).1
    refine ⟨?_, ?_⟩
    · rw [f1alg_unit_iff, ← Matrix.exp_conjTranspose, hX,
        ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
        NormedSpace.exp_zero]
    · exact ((Commute.exp_right (show Commute (Jm ε) X from hc.symm)).symm).eq

lemma f1alg_ct_theta {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    (Jm ε * A * Jm ε)ᴴ = Jm ε * Aᴴ * Jm ε := by
  rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose_eq, Matrix.mul_assoc]

lemma f1alg_theta_comm {n : ℕ} (ε : Fin n → Bool) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (X * Y - Y * X) * Jm ε =
      (Jm ε * X * Jm ε) * (Jm ε * Y * Jm ε) - (Jm ε * Y * Jm ε) * (Jm ε * X * Jm ε) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, f1alg_theta_mul, f1alg_theta_mul]

lemma f1alg_ct_comm {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (X * Y - Y * X)ᴴ = Yᴴ * Xᴴ - Xᴴ * Yᴴ := by
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]

theorem lie_brackets_holds : Brackets := by
  intro n ε X Y

  have hK : ∀ Z, inK ε Z ↔ Zᴴ = -Z ∧ Jm ε * Z * Jm ε = Z := fun Z => by
    rw [f1alg_inK_iff, f1alg_comm_iff]
  have hP : ∀ Z, inP ε Z ↔ Zᴴ = Z ∧ Jm ε * Z * Jm ε = -Z := fun Z => by
    rw [mem_cartanP_iff, f1alg_anti_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hx hy
    rw [hK] at hx hy ⊢
    exact ⟨by rw [f1alg_ct_comm, hx.1, hy.1]; noncomm_ring, by rw [f1alg_theta_comm, hx.2, hy.2]⟩
  · intro hx hy
    rw [hK] at hx
    rw [hP] at hy ⊢
    exact ⟨by rw [f1alg_ct_comm, hx.1, hy.1]; noncomm_ring,
      by rw [f1alg_theta_comm, hx.2, hy.2]; noncomm_ring⟩
  · intro hx hy
    rw [hP] at hx hy
    rw [hK]
    exact ⟨by rw [f1alg_ct_comm, hx.1, hy.1]; noncomm_ring,
      by rw [f1alg_theta_comm, hx.2, hy.2]; noncomm_ring⟩
  · intro hX
    have hx := (f1alg_inG_iff ε X).mp hX
    have htt := f1alg_theta_theta ε X
    have hct := f1alg_ct_theta ε X
    have h2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
    refine ⟨(2 : ℂ)⁻¹ • (X + Jm ε * X * Jm ε), (2 : ℂ)⁻¹ • (X - Jm ε * X * Jm ε), ?_, ?_, ?_⟩
    · rw [hK]
      constructor
      · rw [conjTranspose_smul, conjTranspose_add, hct, hx, h2, Matrix.mul_neg, Matrix.neg_mul, htt]
        module
      · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, htt]
        module
    · rw [hP]
      constructor
      · rw [conjTranspose_smul, conjTranspose_sub, hct, hx, h2, Matrix.mul_neg, Matrix.neg_mul, htt]
        module
      · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, htt]
        module
    · module
  · intro hx hy
    rw [hK] at hx
    rw [hP] at hy
    have h : X = -X := hy.1.symm.trans hx.1
    ext i j
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.neg_apply] at hij
    rw [Matrix.zero_apply]
    linear_combination hij / 2

end Formalism.REAL
