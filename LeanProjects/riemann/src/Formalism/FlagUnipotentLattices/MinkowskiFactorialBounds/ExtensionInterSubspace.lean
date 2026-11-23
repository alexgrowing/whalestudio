import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.LogSumExpBounds.IsoTransfer
import Formalism.GelfandTransference.HadamardGelfand.Transference
import Formalism.HarderNarasimhan.ShiftInvariance

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix

namespace Formalism.HermitianLatticeCounting.P

lemma hs_nonneg {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ hs Y := Real.sqrt_nonneg _

lemma hs_sq {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) : hs Y ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by
  unfold hs; exact Real.sq_sqrt (by positivity)

lemma hs_sq_trace {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    ((hs Y ^ 2 : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  rw [hs_sq, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [Complex.star_def, Complex.conj_mul']

lemma hs_of_gram_eq {N : ℕ} {Y Z : Matrix (Fin N) (Fin N) ℂ}
    (h : (Yᴴ * Y).trace = (Zᴴ * Z).trace) : hs Y = hs Z := by
  rw [← hs_sq_trace, ← hs_sq_trace] at h
  have h2 : hs Y ^ 2 = hs Z ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (hs_nonneg _) (hs_nonneg _)).mp h2

lemma unitary_left {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    kᴴ * k = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hk
  rwa [Matrix.star_eq_conjTranspose] at this

lemma unitary_right {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    k * kᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp hk
  rwa [Matrix.star_eq_conjTranspose] at this

lemma hs_unitary_mul {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) (Y : Matrix (Fin N) (Fin N) ℂ) : hs (k * Y) = hs Y := by
  apply hs_of_gram_eq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ, unitary_left hk,
    Matrix.one_mul]

lemma hs_mul_unitary {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) (Y : Matrix (Fin N) (Fin N) ℂ) : hs (Y * k) = hs Y := by
  apply hs_of_gram_eq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, unitary_right hk, Matrix.mul_one]

section Frob
open scoped Matrix.Norms.Frobenius

lemma norm_exp_sub_one_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (x : A) :
    ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have h1 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • x ^ n) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have h2 : HasSum (fun n : ℕ => ‖x‖ ^ n / (n.factorial : ℝ)) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ‖x‖
  have h1' := (hasSum_nat_add_iff' 1).mpr h1
  have h2' := (hasSum_nat_add_iff' 1).mpr h2
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    div_one] at h1' h2'
  refine h1'.norm_le_of_bounded h2' (fun n => ?_)
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  gcongr
  exact norm_pow_le' x (Nat.succ_pos n)

end Frob

lemma unitary_conj {N : ℕ} {k : Matrix (Fin N) (Fin N) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    kᴴ ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  exact unitary_left hk

theorem conjugation_invariant_measure : ConjInv := by
  intro N ep k X hk hkb hX hXb
  have hu : IsUnit k := ⟨⟨k, kᴴ, unitary_right hk, unitary_left hk⟩, rfl⟩
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (unitary_left hk)
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul k hX, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero; intro d _
    by_cases hd : ep d = ep b
    · have : ∑ c, star (k c a) * X c d = 0 := by
        apply Finset.sum_eq_zero; intro c _
        by_cases hc : ep c = ep a
        · rw [hXb c d (by rw [hc, hab, hd]), mul_zero]
        · rw [hkb c a hc, star_zero, zero_mul]
      rw [this, zero_mul]
    · rw [hkb d b hd, mul_zero]
  · rw [hs_mul_unitary hk, hs_unitary_mul (unitary_conj hk)]
  · rw [← hinv]; exact (Matrix.exp_conj' k X hu).symm

theorem decay_assembly_holds : DecAssembly := by
  intro hDecay hRes hConj hGap N ep lam h Ω T _ μ _ _ κ v X A hlam hgap hκ hX hXb hres hA
  apply hRes Ω T μ v (fun k => ∏ i ∈ Ico 1 N,
    (lead ((κ k).conjTranspose * NormedSpace.exp X * κ k) i).re ^ (-(lam i - lam (i + 1) + 1)))
    _ A (Real.exp_pos _).le hres ?_ hA
  intro k
  obtain ⟨hY, hYb, hYs, hYe⟩ := hConj N ep (κ k) X (hκ k).1 (hκ k).2 hX hXb
  simp only [hYe]
  generalize (κ k).conjTranspose * X * κ k = Y at *
  have hpos : ∀ i, 0 ≤ (lead (NormedSpace.exp Y) i).re := by
    intro i
    by_cases hi : i ≤ N
    · obtain ⟨w, hw0, _, hlead, _⟩ := Formalism.NuclearRankWeightBounds.P.cb_weights N Y hY i hi
      rw [hlead, Complex.ofReal_re]
      exact Finset.sum_nonneg fun J _ => mul_nonneg (hw0 J) (Real.exp_pos _).le
    · simp [lead, hi]
  rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpos i) _)]
  have hs0 : ∀ i, 0 ≤ (if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0) := by
    intro i
    split_ifs with hi
    · have := hlam i hi.1 hi.2; linarith
    · exact le_rfl
  have hD := hDecay N (fun i => if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0) ep h Y hs0 hY hYb (by
    intro a b hba hab
    have hba' : b.val < a.val := hba
    have hsum : ∑ i ∈ Ico (b.val+1) (a.val+1), (if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0)
        = ∑ i ∈ Ico (b.val+1) (a.val+1), (lam i - lam (i+1) + 1) := by
      apply Finset.sum_congr rfl; intro i hi
      have := Finset.mem_Ico.mp hi
      rw [if_pos ⟨by omega, by have := a.isLt; omega⟩]
    rw [hsum, hGap lam (a.val+1) (b.val+1) (by omega)]
    have h1 := hgap a b hba hab
    have h2 : (b.val:ℝ) < a.val := by exact_mod_cast hba'
    push_cast; linarith)
  have hprod : ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re ^ (-(lam i - lam (i+1) + 1))
      = ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re
        ^ (-(if 1 ≤ i ∧ i < N then lam i - lam (i+1) + 1 else 0)) := by
    apply Finset.prod_congr rfl; intro i hi
    have := Finset.mem_Ico.mp hi
    rw [if_pos ⟨this.1, this.2⟩]
  rw [hprod]
  refine hD.trans (le_of_eq ?_)
  rw [hYs]; unfold decExp; congr 1; ring

theorem decay_right_side_bound : DecayRightSide :=
  decay_assembly_holds Formalism.NuclearRankWeightBounds.Top.decay resolution_norm_bound conjugation_invariant_measure gap_sum_bound

noncomputable def n2 {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

theorem coverRadius_sq (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (M : Submodule ℤ V) (hMd : DiscreteTopology M)
    (hspan : Submodule.span ℝ (M : Set V) = ⊤) (κ : ℝ) (hκ : 0 < κ)
    (hdual : ∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) (x : V) :
    ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) ^ 2 / (2 * κ) := by
  have := hMd
  obtain ⟨b, t, hbM, hli, ht0, -, hWs, hcov⟩ :=
    Formalism.HadamardInequality.P.tr_chain M hspan (Module.finrank ℝ V) le_rfl
  have hbspan : Submodule.span ℝ (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  obtain ⟨z, hz, hzx⟩ := hcov x (by rw [hbspan]; trivial)
  have hzM : z ∈ M :=
    (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbM i)) hz
  refine ⟨z, hzM, ?_⟩
  have ht : ∀ i, t i ≤ (Module.finrank ℝ V : ℝ) ^ ((3:ℝ)/2) / κ := by
    intro i
    obtain ⟨W, hWr, hWm⟩ := hWs i
    obtain ⟨y, hyD, hyli, hyn⟩ := Formalism.HadamardInequality.P.tr_dual M hspan W (ht0 i) hWm
    have hfr : Module.finrank ℝ W + Module.finrank ℝ Wᗮ = Module.finrank ℝ V :=
      Submodule.finrank_add_finrank_orthogonal W
    have hpos : 0 < Module.finrank ℝ Wᗮ := by have := i.2; omega
    have hy0 : y ⟨0, hpos⟩ ≠ 0 := hyli.ne_zero _
    have h1 := hdual _ (hyD ⟨0, hpos⟩) hy0
    have h2 := hyn ⟨0, hpos⟩
    have h3 : (Module.finrank ℝ Wᗮ : ℝ) ^ ((3:ℝ)/2) ≤ (Module.finrank ℝ V : ℝ) ^ ((3:ℝ)/2) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast (by omega : Module.finrank ℝ Wᗮ ≤ Module.finrank ℝ V)) (by norm_num)
    have h4 : κ ≤ (Module.finrank ℝ V : ℝ) ^ ((3:ℝ)/2) / t i :=
      h1.trans (h2.trans (div_le_div_of_nonneg_right h3 (ht0 i).le))
    rw [le_div_iff₀ (ht0 i)] at h4
    rw [le_div_iff₀ hκ]; linarith
  generalize Module.finrank ℝ V = N at *
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have h32 : ((N:ℝ) ^ ((3:ℝ)/2)) ^ 2 = (N:ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; norm_num
  have hsum : ∑ l, t l ^ 2 ≤ (N:ℝ) * ((N:ℝ) ^ 3 / κ ^ 2) := by
    calc ∑ l, t l ^ 2 ≤ ∑ _l : Fin N, ((N:ℝ) ^ ((3:ℝ)/2) / κ) ^ 2 :=
          Finset.sum_le_sum fun l _ => pow_le_pow_left₀ (ht0 l).le (ht l) 2
      _ = _ := by simp [div_pow, h32]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have e : ((N:ℝ) ^ 2 / (2 * κ)) ^ 2 = (N:ℝ) ^ 4 / κ ^ 2 / 4 := by
    field_simp; ring
  have e2 : (N:ℝ) * ((N:ℝ) ^ 3 / κ ^ 2) = (N:ℝ) ^ 4 / κ ^ 2 := by ring
  rw [e]
  linarith

theorem covering_radius_bound : CoverRadius := by
  intro V _ _ _ M hMd hspan κ hκ hdual x
  obtain ⟨y, hy, hxy⟩ := coverRadius_sq V M hMd hspan κ hκ hdual x
  refine ⟨y, hy, hxy.trans ?_⟩
  have h23 : (Module.finrank ℝ V : ℝ) ^ 2 ≤ (Module.finrank ℝ V : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with h0 | hN
    · rw [h0]; simp
    · exact pow_le_pow_right₀ (by exact_mod_cast hN) (by norm_num)
  gcongr

lemma hsG_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) : 0 ≤ hsG Y := Real.sqrt_nonneg _

lemma hsG_sq {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) : hsG Y ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by
  unfold hsG; exact Real.sq_sqrt (by positivity)

lemma unitary_leftG {ι : Type} [Fintype ι] [DecidableEq ι] {k : Matrix ι ι ℂ} (hk : k ∈ Matrix.unitaryGroup ι ℂ) :
    kᴴ * k = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hk
  rwa [Matrix.star_eq_conjTranspose] at this

section FrobG
open scoped Matrix.Norms.Frobenius

lemma hsG_eq_norm {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) : hsG Y = ‖Y‖ := by
  rw [Matrix.frobenius_norm_def, hsG, Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]

lemma hsG_exp_sub_one_le {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    hsG (NormedSpace.exp X - 1) ≤ Real.exp (hsG X) - 1 := by
  rw [hsG_eq_norm, hsG_eq_norm]
  exact norm_exp_sub_one_le X

end FrobG

noncomputable def n2G {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

lemma euclNorm_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : 0 ≤ n2G v := Real.sqrt_nonneg _

lemma euclNorm_sq_eq_sum_sq {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : n2G v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  unfold n2G; exact Real.sq_sqrt (by positivity)

lemma euclNorm_eq_euclideanSpace_norm {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    n2G v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

lemma euclNorm_add_le {ι : Type} [Fintype ι] [DecidableEq ι] (v w : ι → ℂ) : n2G (v + w) ≤ n2G v + n2G w := by
  simp only [euclNorm_eq_euclideanSpace_norm, WithLp.toLp_add]; exact norm_add_le _ _

lemma euclNorm_sq_eq_star_dotProduct {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) : ((n2G v ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  rw [euclNorm_sq_eq_sum_sq, dotProduct]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']

lemma euclNorm_mulVec_le_frobenius {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    n2G (A *ᵥ v) ≤ hsG A * n2G v := by
  apply (sq_le_sq₀ (euclNorm_nonneg _) (mul_nonneg (hsG_nonneg _) (euclNorm_nonneg _))).mp
  rw [mul_pow, euclNorm_sq_eq_sum_sq, hsG_sq, euclNorm_sq_eq_sum_sq, Finset.sum_mul]
  apply Finset.sum_le_sum; intro a _
  calc ‖(A *ᵥ v) a‖ ^ 2 ≤ (∑ b, ‖A a b‖ * ‖v b‖) ^ 2 := by
        gcongr
        rw [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma euclNorm_unitary_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {k : Matrix ι ι ℂ} (hk : k ∈ Matrix.unitaryGroup ι ℂ)
    (v : ι → ℂ) : n2G (k *ᵥ v) = n2G v := by
  have h : ((n2G (k *ᵥ v) ^ 2 : ℝ) : ℂ) = ((n2G v ^ 2 : ℝ) : ℂ) := by
    rw [euclNorm_sq_eq_star_dotProduct, euclNorm_sq_eq_star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, unitary_leftG hk, Matrix.one_mulVec]
  have h2 : n2G (k *ᵥ v) ^ 2 = n2G v ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (euclNorm_nonneg _) (euclNorm_nonneg _)).mp h2

lemma opnorm_unitary_exp_le {ι : Type} [Fintype ι] [DecidableEq ι] {k : Matrix ι ι ℂ}
    (hk : k ∈ Matrix.unitaryGroup ι ℂ) (Y : Matrix ι ι ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (k * NormedSpace.exp Y))‖
      ≤ Real.exp (hsG Y) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro w
  have e1 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (k * NormedSpace.exp Y))) w
      = WithLp.toLp 2 ((k * NormedSpace.exp Y) *ᵥ WithLp.ofLp w) := rfl
  have e2 : ‖w‖ = n2G (WithLp.ofLp w) := by rw [euclNorm_eq_euclideanSpace_norm]
  rw [e1, ← euclNorm_eq_euclideanSpace_norm, e2]
  generalize WithLp.ofLp w = v
  rw [← Matrix.mulVec_mulVec, euclNorm_unitary_mulVec hk]
  have e : NormedSpace.exp Y *ᵥ v = v + (NormedSpace.exp Y - 1) *ᵥ v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [e]
  calc n2G (v + (NormedSpace.exp Y - 1) *ᵥ v) ≤ n2G v + n2G ((NormedSpace.exp Y - 1) *ᵥ v) :=
        euclNorm_add_le _ _
    _ ≤ n2G v + (Real.exp (hsG Y) - 1) * n2G v := by
        gcongr
        refine (euclNorm_mulVec_le_frobenius _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (hsG_exp_sub_one_le Y) (euclNorm_nonneg _)
    _ = _ := by ring

open NumberField in
theorem tau_lipschitz_bound : TauLip := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X k Y hX hk hY L hL hL0
  have hX'u : ∀ v, IsUnit (X v * (k v * NormedSpace.exp (Y v))).det := by
    intro v
    rw [Matrix.det_mul, Matrix.det_mul]
    refine (hX v).mul (IsUnit.mul ?_ ?_)
    · have h1 := unitary_leftG (hk v)
      have h2 := congrArg Matrix.det h1
      rw [Matrix.det_mul, Matrix.det_one] at h2
      exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h2)
    · exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  have hop : ∀ v, Formalism.HN.opNormAt b (fun v => X v * (k v * NormedSpace.exp (Y v))) b X v
      (LinearMap.id : V →ₗ[K] V) ≤ Real.exp (hsG (Y v)) := by
    intro v
    unfold Formalism.HN.opNormAt
    have e : (X v)⁻¹ * (LinearMap.toMatrix b b (LinearMap.id : V →ₗ[K] V)).map v.embedding
        * (X v * (k v * NormedSpace.exp (Y v))) = k v * NormedSpace.exp (Y v) := by
      rw [LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hX v), Matrix.one_mul]
    rw [e]
    exact opnorm_unitary_exp_le (hk v) (Y v)
  have hop0 : ∀ v, 0 ≤ Formalism.HN.opNormAt b (fun v => X v * (k v * NormedSpace.exp (Y v))) b X v
      (LinearMap.id : V →ₗ[K] V) := fun v => norm_nonneg _
  have hht : Formalism.HN.htMap b (fun v => X v * (k v * NormedSpace.exp (Y v))) b X
      (LinearMap.id : V →ₗ[K] V) ≤ 2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, hsG (Y v)) := by
    unfold Formalism.HN.htMap
    rw [show 2 * ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, hsG (Y v))
      = (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, 2 * hsG (Y v) by rw [← Finset.mul_sum]; ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro v _
    have h1 := hop v
    have h0 := hop0 v
    generalize Formalism.HN.opNormAt b (fun v => X v * (k v * NormedSpace.exp (Y v))) b X v
      (LinearMap.id : V →ₗ[K] V) = o at *
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
      exact hsG_nonneg _
    · rw [Real.log_le_iff_le_exp (by positivity), two_mul, Real.exp_add, sq]
      exact mul_le_mul h1 h1 h0 (Real.exp_pos _).le
  have s1 := Formalism.HN.sizeMu K V ι b X hX L hL hL0
  have s2 := Formalism.HN.sizeMu K V ι b (fun v => X v * (k v * NormedSpace.exp (Y v))) hX'u L hL hL0
  dsimp only at s1 s2
  obtain ⟨-, -, -, hl, -, -⟩ := s1
  obtain ⟨-, -, -, hl', -, -⟩ := s2
  have hmap : L.map ((LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)) = L := by
    ext x; simp
  obtain ⟨-, hB⟩ := Formalism.HN.slopeIneqMean K V ι V ι b
    (fun v => X v * (k v * NormedSpace.exp (Y v))) b X hX'u hX LinearMap.id L hL
    (by rw [hmap]; exact hL0)
  have h3 := (hB L hL (by rw [hmap])).2 (fun x _ y _ h => h)
  unfold Formalism.HN.muMaxDef at h3
  rw [hl, hl', ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Formalism.HermitianLatticeCounting.P
