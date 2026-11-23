import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomial

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.PolyGrowth

variable {n : ℕ} {ε : Fin n → Bool}

theorem wt_eq_sum (g : Matrix (Fin n) (Fin n) ℂ) : wt g = ∑ i, ∑ j, ‖g i j‖ ^ 2 := by
  unfold wt
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem entry_sq_le_wt (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ wt g := by
  rw [wt_eq_sum]
  calc ‖g i j‖ ^ 2 ≤ ∑ j, ‖g i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem one_le_wt {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (a : Fin n) : 1 ≤ wt g := by
  have h := congrFun (congrFun hg a) a
  have hd : ∀ i, ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := fun i => by split_ifs <;> simp
  have h1 : ‖Jm ε a a‖ = 1 := by
    rw [Jm, Matrix.diagonal_apply_eq]; exact hd a
  have e : (gᴴ * Jm ε * g) a a = ∑ i, star (g i a) * (if ε i = true then (1 : ℂ) else -1) * g i a := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Jm, Matrix.mul_diagonal, conjTranspose_apply]
  rw [← h1, ← h, e, wt_eq_sum]
  calc ‖∑ i, star (g i a) * (if ε i = true then (1 : ℂ) else -1) * g i a‖
      ≤ ∑ i, ‖star (g i a) * (if ε i = true then (1 : ℂ) else -1) * g i a‖ := norm_sum_le _ _
    _ = ∑ i, ‖g i a‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_mul, hd i, norm_star, mul_one, sq]
    _ ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)

theorem inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUJ ε a) (hb : inUJ ε b) : inUJ ε (a * b) := by
  unfold inUJ at *
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

theorem isUnit_of_inUJ' {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : IsUnit g := by
  have h : Jm ε * gᴴ * Jm ε * g = 1 := by
    calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Jm_mul_self]
  exact ⟨⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp h, h⟩, rfl⟩

theorem isCompact_wt_le (ε : Fin n → Bool) (R : ℝ) :
    IsCompact {h : Matrix (Fin n) (Fin n) ℂ | inUJ ε h ∧ wt h ≤ R} := by
  have hwt : Continuous (wt : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
    have : (wt : Matrix (Fin n) (Fin n) ℂ → ℝ) = fun g => ∑ i, ∑ j, ‖g i j‖ ^ 2 := funext wt_eq_sum
    rw [this]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_id.matrix_elem i j).norm).pow 2
  have hcl : IsClosed {h : Matrix (Fin n) (Fin n) ℂ | inUJ ε h ∧ wt h ≤ R} := by
    refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_le hwt continuous_const)
    exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) (R + 1)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 _
  refine IsCompact.of_isClosed_subset hK hcl ?_
  rintro h ⟨-, hR⟩ i - j -
  have h1 := (entry_sq_le_wt h i j).trans hR
  rw [mem_closedBall_zero_iff]
  nlinarith [sq_nonneg (‖h i j‖ - 1), norm_nonneg (h i j)]

section rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_bound_on_compact [CompleteSpace H] (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε))
    {S : Set (Matrix (Fin n) (Fin n) ℂ)} (hS : IsCompact S) (hSU : S ⊆ UJset ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ h ∈ S, ‖π h‖ ≤ B := by
  have hb : ∀ x : H, ∃ C, ∀ i : S, ‖π (i : Matrix (Fin n) (Fin n) ℂ) x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn ((hc x).mono hSU)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus (g := fun i : S => π (i : Matrix (Fin n) (Fin n) ℂ)) hb
  exact ⟨max C' 1, le_max_right _ _, fun h hh => (hC' ⟨h, hh⟩).trans (le_max_left _ _)⟩

theorem pow_bound (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) {h : Matrix (Fin n) (Fin n) ℂ} (hh : inUJ ε h)
    {B : ℝ} (hB : 0 ≤ B) (hb : ‖π h‖ ≤ B) (m : ℕ) :
    inUJ ε (h ^ m) ∧ ∀ x, ‖π (h ^ m) x‖ ≤ B ^ m * ‖x‖ := by
  induction m with
  | zero =>
    refine ⟨?_, fun x => ?_⟩
    · simp [inUJ]
    · simp [hrep.1]
  | succ m ih =>
    refine ⟨by rw [pow_succ]; exact inUJ_mul ih.1 hh, fun x => ?_⟩
    rw [pow_succ, hrep.2 _ ih.1 _ hh, ContinuousLinearMap.comp_apply]
    calc ‖π (h ^ m) (π h x)‖ ≤ B ^ m * ‖π h x‖ := ih.2 _
      _ ≤ B ^ m * (B * ‖x‖) := by
          gcongr
          exact ((π h).le_opNorm x).trans (by gcongr)
      _ = B ^ (m + 1) * ‖x‖ := by ring

end rep

theorem trace_exp_smul {L : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsHermitian) (t : ℝ) :
    (NormedSpace.exp (t • L)).trace.re = ∑ i, Real.exp (t * hL.eigenvalues i) := by
  set V : Matrix (Fin n) (Fin n) ℂ := (hL.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hV
  have h1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hL.eigenvectorUnitary.2
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hL.eigenvectorUnitary.2
  have hsp : L = V * diagonal (fun i => (hL.eigenvalues i : ℂ)) * Vᴴ := by
    have h0 := hL.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h0
    conv_lhs => rw [h0]
    simp only [Matrix.star_eq_conjTranspose]
    rfl
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨V, Vᴴ, h2, h1⟩
  have hd : diagonal (fun i => ((t * hL.eigenvalues i : ℝ) : ℂ)) =
      t • diagonal (fun i => (hL.eigenvalues i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  have hs : t • L = (U : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun i => ((t * hL.eigenvalues i : ℝ) : ℂ)) *
      ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    show t • L = V * _ * Vᴴ
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← hsp]
  rw [hs, Matrix.exp_units_conj, Matrix.trace_units_conj, Matrix.exp_diagonal, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_re]

theorem exp_smul_add (L : Matrix (Fin n) (Fin n) ℂ) (s r : ℝ) :
    NormedSpace.exp (s • L) * NormedSpace.exp (r • L) = NormedSpace.exp ((s + r) • L) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left s).smul_right r)]

theorem exp_smul_herm {L : Matrix (Fin n) (Fin n) ℂ} (hL : Lᴴ = L) (s : ℝ) :
    (NormedSpace.exp (s • L))ᴴ = NormedSpace.exp (s • L) := by
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hL, star_trivial]

theorem wt_exp_smul {L : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsHermitian) (s : ℝ) :
    wt (NormedSpace.exp (s • L)) = ∑ i, Real.exp (2 * s * hL.eigenvalues i) := by
  unfold wt
  rw [exp_smul_herm hL, exp_smul_add, show s + s = 2 * s by ring, trace_exp_smul hL]

theorem wt_root_le {g L : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsHermitian) (he : NormedSpace.exp L = gᴴ * g) {m : ℕ}
    (hm : 0 < m) (hw : 0 < wt g) (hlog : Real.log (wt g) ≤ m) :
    wt (NormedSpace.exp ((1 / (2 * (m : ℝ))) • L)) ≤ n * Real.exp 1 := by
  rw [wt_exp_smul hL]
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have key : ∀ i, Real.exp (2 * (1 / (2 * (m : ℝ))) * hL.eigenvalues i) ≤ Real.exp 1 := by
    intro i
    have h1 : Real.exp (hL.eigenvalues i) ≤ wt g := by
      have e : wt g = ∑ i, Real.exp (1 * hL.eigenvalues i) := by
        rw [← trace_exp_smul hL 1, one_smul, he]; rfl
      rw [e]
      simpa using Finset.single_le_sum (f := fun i => Real.exp (1 * hL.eigenvalues i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ i)
    have h2 : hL.eigenvalues i ≤ Real.log (wt g) := (Real.le_log_iff_exp_le hw).2 h1
    apply Real.exp_le_exp.2
    rw [show 2 * (1 / (2 * (m : ℝ))) * hL.eigenvalues i = hL.eigenvalues i / m by field_simp, div_le_one hmr]
    linarith
  calc ∑ i, Real.exp (2 * (1 / (2 * (m : ℝ))) * hL.eigenvalues i) ≤ ∑ _i : Fin n, Real.exp 1 :=
        Finset.sum_le_sum fun i _ => key i
    _ = n * Real.exp 1 := by simp

open scoped Matrix.Norms.L2Operator in
theorem herm_exp_injective {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  rw [← CFC.log_exp A hA, ← CFC.log_exp B hB, h]

def signUnit (ε : Fin n → Bool) : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩

theorem exp_sign_conj (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε :=
  Matrix.exp_units_conj' (signUnit ε) A

theorem sign_sign_mul (x : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * x) = x := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem left_inv_of_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Jm ε * gᴴ * Jm ε * g = 1 := by
  calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jm_mul_self]

theorem right_inv_of_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * (Jm ε * gᴴ * Jm ε) = 1 :=
  mul_eq_one_comm.mp (left_inv_of_inUJ hg)

theorem sign_conj_log {g L : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hL : Lᴴ = L)
    (he : NormedSpace.exp L = gᴴ * g) : Jm ε * L * Jm ε = -L := by
  refine herm_exp_injective ?_ ?_ ?_
  · rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, hL, Matrix.mul_assoc]
  · rw [conjTranspose_neg, hL]
  · rw [exp_sign_conj, he, Matrix.exp_neg, he]
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc Jm ε * (gᴴ * g) * Jm ε * (gᴴ * g) = (Jm ε * gᴴ) * (g * (Jm ε * gᴴ * Jm ε)) * (Jm ε * g) := by
          simp only [Matrix.mul_assoc, sign_sign_mul]
      _ = 1 := by rw [right_inv_of_inUJ hg, Matrix.mul_one, ← Matrix.mul_assoc]; exact left_inv_of_inUJ hg

theorem exp_log_inUJ {g L : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hL : Lᴴ = L)
    (he : NormedSpace.exp L = gᴴ * g) (s : ℝ) : inUJ ε (NormedSpace.exp (s • L)) := by
  unfold inUJ
  have hJE : Jm ε * NormedSpace.exp (s • L) * Jm ε = NormedSpace.exp ((-s) • L) := by
    rw [← exp_sign_conj, Matrix.mul_smul, Matrix.smul_mul, sign_conj_log hg hL he, smul_neg, neg_smul]
  rw [exp_smul_herm hL]
  calc NormedSpace.exp (s • L) * Jm ε * NormedSpace.exp (s • L)
      = Jm ε * (Jm ε * NormedSpace.exp (s • L) * Jm ε) * NormedSpace.exp (s • L) := by
        simp only [Matrix.mul_assoc, sign_sign_mul]
    _ = Jm ε := by
        rw [hJE, Matrix.mul_assoc, exp_smul_add, neg_add_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]

theorem mem_Kset_of_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) (hu : kᴴ * k = 1) : k ∈ Kset ε := by
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 hu, ?_⟩
  have h1 : k * kᴴ = 1 := mul_eq_one_comm.mp hu
  calc k * Jm ε = k * (kᴴ * Jm ε * k) := by rw [hk]
    _ = (k * kᴴ) * Jm ε * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * k := by rw [h1, Matrix.one_mul]

theorem polyGrowth_of_isometric_on_K : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε))
    (hK : ∀ k ∈ Kset ε, ∀ v, ‖π k v‖ = ‖v‖),
    ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖ := by
  intro n ε H _ _ _ π hrep hc hK
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, 0, one_pos, le_rfl, fun g _ x => ?_⟩
    have hg1 : g = 1 := Subsingleton.elim _ _
    rw [hg1, hrep.1]; simp
  obtain ⟨B, hB1, hB⟩ := exists_bound_on_compact (π := π) hc (isCompact_wt_le ε ((n : ℝ) * Real.exp 1))
    (fun h hh => hh.1)
  have hB0 : 0 < B := by linarith
  refine ⟨B ^ 2, Real.log B, by positivity, Real.log_nonneg hB1, fun g hg x => ?_⟩
  have hg' : inUJ ε g := hg
  have hw : 1 ≤ wt g := one_le_wt hg' ⟨0, hn⟩
  have hw0 : 0 < wt g := by linarith
  have hlog0 : 0 ≤ Real.log (wt g) := Real.log_nonneg hw
  obtain ⟨L, -, hLs, hLe, -⟩ := GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial n g (isUnit_of_inUJ' hg')
  have hLh : L.IsHermitian := hLs
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈Real.log (wt g)⌉₊ + 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hml : Real.log (wt g) ≤ m := by
    rw [hm]; push_cast; linarith [Nat.le_ceil (Real.log (wt g))]
  have hmu : (m : ℝ) ≤ Real.log (wt g) + 2 := by
    rw [hm]; push_cast; linarith [Nat.ceil_lt_add_one hlog0]
  obtain ⟨h, hh⟩ : ∃ h, h = NormedSpace.exp ((1 / (2 * (m : ℝ))) • L) := ⟨_, rfl⟩
  have hhU : inUJ ε h := hh ▸ exp_log_inUJ hg' hLs hLe _
  have hhS : ‖π h‖ ≤ B := hB h ⟨hhU, hh ▸ wt_root_le hLh hLe hm0 hw0 hml⟩
  obtain ⟨hPU, hPb⟩ := pow_bound hrep hhU hB0.le hhS m
  have hP : h ^ m = NormedSpace.exp ((1 / 2 : ℝ) • L) := by
    rw [hh, ← Matrix.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = NormedSpace.exp ((-(1 / 2) : ℝ) • L) := ⟨_, rfl⟩
  have hQU : inUJ ε Q := hQ ▸ exp_log_inUJ hg' hLs hLe _
  have hk : inUJ ε (g * Q) := inUJ_mul hg' hQU
  have hku : (g * Q)ᴴ * (g * Q) = 1 := by
    have hQh : Qᴴ = Q := by rw [hQ]; exact exp_smul_herm hLs _
    rw [conjTranspose_mul, hQh]
    calc Q * gᴴ * (g * Q) = Q * (gᴴ * g) * Q := by simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp ((-(1 / 2) : ℝ) • L) * NormedSpace.exp ((1 : ℝ) • L) * NormedSpace.exp ((-(1 / 2) : ℝ) • L) := by
          rw [one_smul, hLe, hQ]
      _ = 1 := by
          rw [exp_smul_add, exp_smul_add, show (-(1 / 2) + 1 + -(1 / 2) : ℝ) = 0 by norm_num, zero_smul,
            NormedSpace.exp_zero]
  have hgk : (g * Q) * h ^ m = g := by
    rw [hP, hQ, Matrix.mul_assoc, exp_smul_add, show (-(1 / 2) + 1 / 2 : ℝ) = 0 by norm_num, zero_smul,
      NormedSpace.exp_zero, Matrix.mul_one]
  have e1 : π g x = π (g * Q) (π (h ^ m) x) := by
    calc π g x = π ((g * Q) * h ^ m) x := by rw [hgk]
      _ = _ := by rw [hrep.2 _ hk _ hPU]; rfl
  rw [e1, hK _ (mem_Kset_of_unitary hk hku)]
  refine (hPb x).trans ?_
  have hfin : B ^ m ≤ B ^ 2 * wt g ^ Real.log B := by
    rw [← Real.rpow_natCast B m]
    calc B ^ (m : ℝ) ≤ B ^ (Real.log (wt g) + 2) := Real.rpow_le_rpow_of_exponent_le hB1 hmu
      _ = B ^ 2 * wt g ^ Real.log B := by
          rw [add_comm, Real.rpow_add hB0, Real.rpow_two, Real.rpow_def_of_pos hB0 (Real.log (wt g)),
            Real.rpow_def_of_pos hw0 (Real.log B), mul_comm (Real.log B)]
  exact mul_le_mul_of_nonneg_right hfin (norm_nonneg x)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.PolyGrowth

end
