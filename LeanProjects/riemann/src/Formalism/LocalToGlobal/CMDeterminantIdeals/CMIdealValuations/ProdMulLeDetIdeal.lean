import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementA

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

namespace A2

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_pos' {I : FractionalIdeal (𝓞 K)⁰ K} (h : I ≠ 0) : 0 < FractionalIdeal.absNorm I :=
  lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I) (fun e => h (FractionalIdeal.absNorm_eq_zero_iff.1 e.symm))

theorem absNorm_anti' {I J : FractionalIdeal (𝓞 K)⁰ K} (hIJ : I ≤ J) (hI : I ≠ 0) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact hI (FractionalIdeal.le_zero_iff.1 hIJ)
  have hX : I * J⁻¹ ≤ 1 := by
    calc I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hIJ le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : I = J * (I * J⁻¹) := by
    rw [mul_comm I, ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  have hIJ0 : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have hX0 : X ≠ ⊥ := by
    rintro rfl
    apply hIJ0
    rw [← hX']
    exact FractionalIdeal.coeIdeal_bot
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹) := by
    rw [← hX', FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm X ≠ 0 := fun e => hX0 (Ideal.absNorm_eq_zero_iff.1 e)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  calc FractionalIdeal.absNorm J = FractionalIdeal.absNorm J * 1 := (mul_one _).symm
    _ ≤ FractionalIdeal.absNorm J * FractionalIdeal.absNorm (I * J⁻¹) :=
        mul_le_mul_of_nonneg_left hN (FractionalIdeal.absNorm_nonneg _)
    _ = FractionalIdeal.absNorm I := by rw [← map_mul, ← hdec]

theorem abs_norm_eq_prod (x : K) : ((|Algebra.norm ℚ x| : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h2 := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => ‖σ x‖) (fun τ => ‖τ x‖) (fun _ => rfl), ← h2]
  simp

theorem absNorm_span_real (x : K) :
    ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℚ) : ℝ) = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [FractionalIdeal.absNorm_span_singleton (𝓞 K), abs_norm_eq_prod]

theorem det_re_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : A.PosDef) : 0 < A.det.re := by
  simpa using (Complex.lt_def.1 h.det_pos).1

theorem exists_den {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K)) (hM : M.FG) :
    ∃ a ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (a • x i) := by
  have hc : ∀ i : Fin m, ∃ a ∈ (𝓞 K)⁰, ∀ b ∈ M.map (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K),
      IsLocalization.IsInteger (𝓞 K) (a • b) :=
    fun i => FractionalIdeal.isFractional_of_fg (hM.map _)
  choose a ha hb using hc
  refine ⟨∏ i, a i, prod_mem fun i _ => ha i, fun x hx i => ?_⟩
  have hxi := hb i (x i) (Submodule.mem_map_of_mem (f := (LinearMap.proj i : (Fin m → K) →ₗ[𝓞 K] K)) hx)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul]
  exact IsLocalization.isInteger_smul hxi

theorem isInteger_det {m : ℕ} (x : Fin m → Fin m → K) (hx : ∀ i j, IsLocalization.IsInteger (𝓞 K) (x i j)) :
    IsLocalization.IsInteger (𝓞 K) (Matrix.of x).det := by
  have hx' : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i j := fun i j => hx i j
  choose y hy using hx'
  refine ⟨(Matrix.of y).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hy]

theorem detSub_isFractional {m : ℕ} (L : MLat K m) (hM : L.M.FG) : IsFractional (𝓞 K)⁰ L.detSub := by
  obtain ⟨a, ha, hint⟩ := exists_den L.M hM
  refine ⟨a ^ m, pow_mem ha m, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ m) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 K) K a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

theorem detIdeal_coe {m : ℕ} (L : MLat K m) (h : IsFractional (𝓞 K)⁰ L.detSub) :
    (L.detIdeal : Submodule (𝓞 K) K) = L.detSub := by
  have e : L.detIdeal = ⟨L.detSub, h⟩ := dif_pos h
  rw [e]
  rfl

theorem det_mem {m : ℕ} (L : MLat K m) (x : Fin m → Fin m → K) (hx : ∀ i, x i ∈ L.M) :
    (Matrix.of x).det ∈ L.detSub :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem exists_det_ne {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K))
    (hM : Submodule.span K (M : Set (Fin m → K)) = ⊤) :
    ∃ x : Fin m → Fin m → K, (∀ i, x i ∈ M) ∧ (Matrix.of x).det ≠ 0 := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (M : Set (Fin m → K))
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hspan, hM]))
  let e := B.indexEquiv (Pi.basisFun K (Fin m))
  refine ⟨fun i => (e.symm i : Fin m → K), fun i => hs (e.symm i).2, ?_⟩
  have hli' : LinearIndependent K (fun i => (e.symm i : Fin m → K)) := hli.comp _ e.symm.injective
  have : IsUnit (Matrix.of fun i => (e.symm i : Fin m → K)) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

theorem detIdeal_ne_zero {m : ℕ} (L : MLat K m) (hL : L.Good) : L.detIdeal ≠ 0 := by
  have hf := detSub_isFractional L hL.1
  obtain ⟨x, hx, hd⟩ := exists_det_ne L.M hL.2.1
  intro h0
  have hmem : (Matrix.of x).det ∈ (L.detIdeal : Submodule (𝓞 K) K) := by
    rw [detIdeal_coe L hf]; exact det_mem L x hx
  rw [h0] at hmem
  exact hd ((FractionalIdeal.mem_zero_iff _).1 hmem)

theorem deg_detLine {m : ℕ} (L : MLat K m) : L.detLine.deg =
    -Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) - ∑ σ, Real.log (Real.sqrt (L.H σ).det.re) := rfl

end A2

open A2 in
theorem detLineAdmissible : DetGood := by
  intro K _ _ m L hL
  refine ⟨detSub_isFractional L hL.1, ?_⟩
  show L.detIdeal ≠ 0 ∧ ∀ σ, 0 < Real.sqrt (L.H σ).det.re
  exact ⟨detIdeal_ne_zero L hL, fun σ => Real.sqrt_pos.2 (det_re_pos (hL.2.2 σ))⟩

namespace A2
variable {K : Type} [Field K] [NumberField K]

theorem detSub_mono {m : ℕ} {L L' : MLat K m} (h : L'.M ≤ L.M) : L'.detSub ≤ L.detSub :=
  Submodule.span_mono fun _ ⟨x, hx, hd⟩ => ⟨x, fun i => h (hx i), hd⟩

end A2

open A2 in
theorem detLineMono : DetMono := by
  intro K _ _ m L L' hL hL' hH hM
  have hf := detSub_isFractional L hL.1
  have hf' := detSub_isFractional L' hL'.1
  have hle : L'.detIdeal ≤ L.detIdeal := by
    rw [← FractionalIdeal.coe_le_coe, detIdeal_coe L hf, detIdeal_coe L' hf']
    exact detSub_mono hM
  have hN := absNorm_anti' hle (detIdeal_ne_zero L' hL')
  have hpos := absNorm_pos' (detIdeal_ne_zero L hL)
  rw [deg_detLine, deg_detLine, hH]
  have : Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤
      Real.log ((FractionalIdeal.absNorm L'.detIdeal : ℚ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hN)
  linarith

namespace A2
variable {K : Type} [Field K] [NumberField K]

theorem detSub_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detSub = Submodule.span (𝓞 K) {(Matrix.of b).det} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro d ⟨x, hx, rfl⟩
    have : ∀ i, ∃ c : Fin m → 𝓞 K, ∑ j, c j • b j = x i := fun i => by
      have := hx i
      rw [hb] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using this
    have hx' : Matrix.of x = (Matrix.of c).map (algebraMap (𝓞 K) K) * Matrix.of b := by
      ext i j
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
      rw [← hc i]
      simp [Finset.sum_apply, Algebra.smul_def]
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨(Matrix.of c).det, ?_⟩
    rw [Algebra.smul_def, RingHom.map_det, hx', Matrix.det_mul]
    rfl
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨b, fun i => ?_, rfl⟩
    rw [hb]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem detIdeal_free {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K) (hL : L.Good)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detIdeal = FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det := by
  apply FractionalIdeal.coeToSubmodule_injective
  show (L.detIdeal : Submodule (𝓞 K) K) = (FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of b).det : Submodule (𝓞 K) K)
  rw [detIdeal_coe L (detSub_isFractional L hL.1), FractionalIdeal.coe_spanSingleton, detSub_free L b hb]

theorem gramC_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC H σ b = ((Matrix.of b).map σ).transpose.conjTranspose * H * ((Matrix.of b).map σ).transpose := by
  ext i j
  simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, Matrix.mul_apply, dotProduct,
    Matrix.mulVec, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem gramC_det {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    (ReciprocityTheory.MultiplicativeHeights.gramC H σ b).det = (Complex.normSq (σ (Matrix.of b).det) : ℂ) * H.det := by
  rw [gramC_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_transpose,
    RingHom.map_det σ (Matrix.of b), Complex.normSq_eq_conj_mul_self]
  simp only [RingHom.mapMatrix_apply, Complex.star_def]
  ring

end A2

open A2 in
theorem detLineFree : DetFree := by
  intro K _ _ m L b hL hb
  have hI := detIdeal_free L b hL hb
  have hne : (Matrix.of b).det ≠ 0 := by
    intro h
    apply detIdeal_ne_zero L hL
    rw [hI, h, FractionalIdeal.spanSingleton_zero]
  have hσ : ∀ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ b).det.re =
      2 * Real.log ‖σ (Matrix.of b).det‖ + 2 * Real.log (Real.sqrt (L.H σ).det.re) := by
    intro σ
    have hD := det_re_pos (hL.2.2 σ)
    have hn : 0 < ‖σ (Matrix.of b).det‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hne)
    rw [gramC_det, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, Real.log_mul (by positivity) hD.ne',
      Real.log_pow, Real.log_sqrt hD.le]
    push_cast
    ring
  rw [deg_detLine, hI, absNorm_span_real,
    Real.log_prod (fun σ _ => (norm_pos_iff.2 ((map_ne_zero σ).2 hne)).ne')]
  simp_rw [hσ, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem hadamardInequality : HadamardPD := by
  intro m A hA
  have hdpos : ∀ i, 0 < (A i i).re := fun i => by
    simpa using (Complex.lt_def.1 (hA.diag_pos (i := i))).1
  have hdiag : ∀ i, A i i = ((A i i).re : ℂ) := fun i => (hA.isHermitian.coe_re_apply_self i).symm
  set s : Fin m → ℝ := fun i => (Real.sqrt (A i i).re)⁻¹ with hs
  have hspos : ∀ i, 0 < s i := fun i => inv_pos.2 (Real.sqrt_pos.2 (hdpos i))
  have hs2 : ∀ i, s i ^ 2 * (A i i).re = 1 := fun i => by
    rw [hs]; simp only
    rw [inv_pow, Real.sq_sqrt (hdpos i).le, inv_mul_cancel₀ (hdpos i).ne']
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i => (s i : ℂ) with hD
  have hDh : D.conjTranspose = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have hDdet : D.det = ∏ i, (s i : ℂ) := by rw [hD, Matrix.det_diagonal]
  have hDu : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det, hDdet]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hspos i).ne')
  have hC : (D.conjTranspose * A * D).PosDef := hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.2 hDu)
  set C := D.conjTranspose * A * D with hCdef
  have hCii : ∀ i, C i i = 1 := fun i => by
    rw [hCdef, hDh, hD]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hdiag i]
    rw [show (s i : ℂ) * ((A i i).re : ℂ) * (s i : ℂ) = ((s i ^ 2 * (A i i).re : ℝ) : ℂ) by push_cast; ring, hs2 i]
    simp
  have hCdet : C.det = A.det * ∏ i, ((s i ^ 2 : ℝ) : ℂ) := by
    rw [hCdef, Matrix.det_mul, Matrix.det_mul, hDh, hDdet]
    push_cast
    rw [Finset.prod_pow]
    ring
  have hev := hC.isHermitian.det_eq_prod_eigenvalues
  have htr := hC.isHermitian.trace_eq_sum_eigenvalues
  set ev := hC.isHermitian.eigenvalues with hev_def
  have hevpos : ∀ i, 0 < ev i := hC.eigenvalues_pos
  have hsum : ∑ i, ev i = m := by
    have : C.trace = (m : ℂ) := by
      simp [Matrix.trace, hCii]
    rw [this] at htr
    apply Complex.ofReal_injective
    push_cast
    exact htr.symm
  have hprod : ∏ i, ev i ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 : ℝ)) ev
      (fun _ _ => zero_le_one) (by simp [hmR]) (fun i _ => (hevpos i).le)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, hsum, div_self hmR.ne'] at amgm
    by_contra hlt
    push Not at hlt
    have := Real.one_lt_rpow hlt (inv_pos.2 hmR)
    linarith
  have hA' : A.det = (∏ i, ev i : ℝ) * ∏ i, (((A i i).re : ℝ) : ℂ) := by
    have h1 : C.det = ((∏ i, ev i : ℝ) : ℂ) := by rw [hev]; push_cast; rfl
    have h2 : (∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rw [← Complex.ofReal_mul, hs2 i, Complex.ofReal_one]
    calc A.det = A.det * ((∏ i, ((s i ^ 2 : ℝ) : ℂ)) * ∏ i, (((A i i).re : ℝ) : ℂ)) := by rw [h2, mul_one]
      _ = C.det * ∏ i, (((A i i).re : ℝ) : ℂ) := by rw [hCdet]; ring
      _ = _ := by rw [h1]
  rw [hA', ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
  calc (∏ i, ev i) * ∏ i, (A i i).re ≤ 1 * ∏ i, (A i i).re :=
        mul_le_mul_of_nonneg_right hprod (Finset.prod_nonneg fun i _ => (hdpos i).le)
    _ = _ := one_mul _

namespace A2
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise

theorem coe_prod_fi {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ j ∈ s, I j : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = ∏ j ∈ s, (I j : Submodule (𝓞 K) K) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FractionalIdeal.coe_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coe_mul, ih]

theorem prod_mul_le_detIdeal {m : ℕ} (L : MLat K m) (hL : L.Good) (ℓ : Fin m → MLine K)
    (u : Fin m → Fin m → K) (hu : ∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ L.M) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of u).det ≤ L.detIdeal := by
  rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
    detIdeal_coe L (detSub_isFractional L hL.1), coe_prod_fi, Submodule.mul_le]
  intro p hp q hq
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq
  rw [mul_smul_comm]
  apply Submodule.smul_mem
  have hspan : ∏ j, ((ℓ j).I : Submodule (𝓞 K) K) =
      Submodule.span (𝓞 K) (∏ j, (((ℓ j).I : Submodule (𝓞 K) K) : Set K)) := by
    rw [← Submodule.prod_span]
    simp only [Submodule.span_eq]
  rw [hspan] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetProd _ _ _).1 hp
    have : (∏ j, g j) * (Matrix.of u).det = (Matrix.of fun j k => g j * u j k).det := by
      exact (Matrix.det_mul_column g (Matrix.of u)).symm
    rw [this]
    exact det_mem L _ fun j => by
      have := hu j (g j) (hg (Finset.mem_univ j))
      simpa [Pi.smul_def, smul_eq_mul] using this
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

end A2

open A2 in
theorem hadamardIdeals : HadamardIdeals := by
  intro K _ _ m L ℓ u La hL hℓ hli hu hLa hsq
  set d := (Matrix.of u).det with hd
  have hdne : d ≠ 0 := by
    have : IsUnit (Matrix.of u) := Matrix.linearIndependent_rows_iff_isUnit.1 hli
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => (hℓ j).1)
      (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
  have hN := absNorm_anti' (prod_mul_le_detIdeal L hL ℓ u hu) hX0
  have hposI : ∀ j, (0 : ℝ) < ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) := fun j => by
    exact_mod_cast absNorm_pos' (hℓ j).1
  have hposd : ∀ σ : K →+* ℂ, 0 < ‖σ d‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hdne)
  have hposD := absNorm_pos' (detIdeal_ne_zero L hL)
  have hNX : ((FractionalIdeal.absNorm ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) : ℚ) : ℝ) =
      (∏ j, ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ)) * ∏ σ : K →+* ℂ, ‖σ d‖ := by
    rw [map_mul, map_prod, Rat.cast_mul, Rat.cast_prod, absNorm_span_real]
  have hlogN : Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤
      ∑ j, Real.log ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log ‖σ d‖ := by
    rw [← Real.log_prod (fun j _ => (hposI j).ne'), ← Real.log_prod (fun σ _ => (hposd σ).ne'),
      ← Real.log_mul (Finset.prod_pos fun j _ => hposI j).ne' (Finset.prod_pos fun σ _ => hposd σ).ne', ← hNX]
    exact Real.log_le_log (by exact_mod_cast hposD) (by exact_mod_cast hN)
  have hσ : ∀ σ : K →+* ℂ, Real.log ‖σ d‖ + Real.log (Real.sqrt (L.H σ).det.re) ≤
      ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
    intro σ
    have hD := det_re_pos (hL.2.2 σ)
    have hGpd : (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u).PosDef := by
      rw [gramC_eq]
      apply (hL.2.2 σ).conjTranspose_mul_mul_same
      apply Matrix.mulVec_injective_iff_isUnit.2
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact IsUnit.mk0 _ ((map_ne_zero σ).2 hdne)
    have hdiagpos : ∀ j, 0 < (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re := fun j => by
      simpa using (Complex.lt_def.1 (hGpd.diag_pos (i := j))).1
    have hH := hadamardInequality m _ hGpd
    rw [gramC_det, Complex.re_ofReal_mul] at hH
    have hbound : ∏ j, (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      apply Finset.prod_le_prod
      · intro j _
        exact (hdiagpos j).le
      · intro j _
        exact hsq σ j
    have key : ‖σ d‖ ^ 2 * (L.H σ).det.re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hH.trans hbound
    have hpos' : 0 < ‖σ d‖ ^ 2 * (L.H σ).det.re := by
      have := hposd σ
      positivity
    have hlog := Real.log_le_log hpos' key
    have hnpos : ∀ j, 0 < (ℓ j).n σ := fun j => (hℓ j).2 σ
    rw [Real.log_mul (by have := hposd σ; positivity) hD.ne', Real.log_pow,
      Real.log_prod (fun j _ => by have := hnpos j; positivity)] at hlog
    have hs : ∑ j, Real.log ((La * (ℓ j).n σ) ^ 2) = 2 * ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_pow, Real.log_mul hLa.ne' (hnpos j).ne']
      push_cast
      ring
    rw [hs] at hlog
    rw [Real.log_sqrt hD.le]
    push_cast at hlog
    linarith
  have hsumσ := Finset.sum_le_sum fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hσ σ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumσ
  have hc : ∑ σ : K →+* ℂ, ∑ j, Real.log ((ℓ j).n σ) = ∑ j, ∑ σ : K →+* ℂ, Real.log ((ℓ j).n σ) :=
    Finset.sum_comm
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ
  rw [hc, hcard] at hsumσ
  rw [deg_detLine]
  simp only [MLine.deg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linarith

end Formalism.L2.LamCM
