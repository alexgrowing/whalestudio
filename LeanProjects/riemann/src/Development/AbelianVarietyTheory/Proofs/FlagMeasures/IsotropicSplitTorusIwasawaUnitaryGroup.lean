import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.IsoTorus

variable {n : ℕ}

private lemma conjTranspose_mul_self_apply_eq_inner {m r : ℕ} (B : Matrix (Fin m) (Fin r) ℂ) (j k : Fin r) :
    (Bᴴ * B) j k = ⟪WithLp.toLp 2 (fun i => B i j), WithLp.toLp 2 (fun i => B i k)⟫_ℂ := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [Matrix.mul_apply, dotProduct, mul_comm]

theorem exists_frame (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℂ), Bᴴ * B = 1 ∧ ∀ x, x ∈ W ↔ (B * Bᴴ) *ᵥ x = x := by
  classical
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    W.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ K
  let B : Matrix (Fin n) (Fin (Module.finrank ℂ K)) ℂ :=
    Matrix.of fun i j => (b j : EuclideanSpace ℂ (Fin n)) i
  have hcol : ∀ j, WithLp.toLp 2 (fun i => B i j) = (b j : EuclideanSpace ℂ (Fin n)) := fun j => rfl
  have hmul : ∀ x : Fin n → ℂ, (B * Bᴴ) *ᵥ x = WithLp.ofLp (∑ j, ⟪(b j : EuclideanSpace ℂ (Fin n)),
      WithLp.toLp 2 x⟫_ℂ • (b j : EuclideanSpace ℂ (Fin n))) := by
    intro x
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, B, Matrix.of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.star_apply]
    ring
  refine ⟨_, B, ?_, fun x => ?_⟩
  · ext j k
    rw [conjTranspose_mul_self_apply_eq_inner, hcol, hcol, ← Submodule.coe_inner, b.inner_eq_ite]
    simp [Matrix.one_apply]
  · rw [hmul]
    constructor
    · intro hx
      have h1 := b.sum_repr' ⟨WithLp.toLp 2 x, hx⟩
      have h2 := congrArg (fun v : K => WithLp.ofLp (v : EuclideanSpace ℂ (Fin n))) h1
      simpa [Submodule.coe_inner] using h2
    · intro hx
      have h3 : (∑ j, ⟪(b j : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 x⟫_ℂ •
          (b j : EuclideanSpace ℂ (Fin n))) ∈ K :=
        K.sum_mem fun j _ => K.smul_mem _ (b j).2
      have h4 : WithLp.ofLp (∑ j, ⟪(b j : EuclideanSpace ℂ (Fin n)), WithLp.toLp 2 x⟫_ℂ •
          (b j : EuclideanSpace ℂ (Fin n))) ∈ W := h3
      rwa [hx] at h4

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) ℂ} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simpa [Matrix.toLin'_apply] using h x

theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, Pᴴ = P ∧ P * P = P ∧ ∀ x, x ∈ W ↔ P *ᵥ x = x := by
  obtain ⟨r, B, h1, h2⟩ := exists_frame W
  refine ⟨B * Bᴴ, by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], ?_, h2⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ B Bᴴ, h1, Matrix.one_mul]

theorem proj_frame {P : Matrix (Fin n) (Fin n) ℂ} (h : Pᴴ = P) (h' : P * P = P) :
    ∃ (r : ℕ) (B : Matrix (Fin n) (Fin r) ℂ), Bᴴ * B = 1 ∧ B * Bᴴ = P := by
  obtain ⟨r, B, h1, h2⟩ := exists_frame (LinearMap.ker (Matrix.toLin' (P - 1)))
  have memP : ∀ x, x ∈ LinearMap.ker (Matrix.toLin' (P - 1)) ↔ P *ᵥ x = x := by
    intro x
    simp [Matrix.toLin'_apply, Matrix.sub_mulVec, sub_eq_zero]
  have hRR : (B * Bᴴ) * (B * Bᴴ) = B * Bᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ B Bᴴ, h1, Matrix.one_mul]
  have hPR : P * (B * Bᴴ) = B * Bᴴ := ext_mulVec fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (memP _).1 ((h2 _).2 (by rw [Matrix.mulVec_mulVec, hRR]))
  have hRP : (B * Bᴴ) * P = P := ext_mulVec fun x => by
    rw [← Matrix.mulVec_mulVec]
    exact (h2 _).1 ((memP _).2 (by rw [Matrix.mulVec_mulVec, h']))
  have hRs : (B * Bᴴ)ᴴ = B * Bᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine ⟨r, B, h1, ?_⟩
  calc B * Bᴴ = (P * (B * Bᴴ))ᴴ := by rw [hPR, hRs]
    _ = (B * Bᴴ) * P := by rw [Matrix.conjTranspose_mul, hRs, h]
    _ = P := hRP

theorem exp_idem {P : Matrix (Fin n) (Fin n) ℂ} (h : P * P = P) (c : ℂ) :
    NormedSpace.exp (c • P) = 1 + (Complex.exp c - 1) • P := by
  have e0 : NormedSpace.exp c = Complex.exp c := (congr_fun Complex.exp_eq_exp_ℂ c).symm
  have hS : HasSum (fun k : ℕ => (((Nat.factorial k : ℂ)⁻¹ * c ^ k) • P + if k = 0 then 1 - P else 0))
      (Complex.exp c • P + (1 - P)) := by
    refine HasSum.add ?_ (hasSum_ite_eq 0 (1 - P))
    have h0 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c
    rw [e0] at h0
    simpa only [smul_eq_mul] using h0.smul_const P
  have hT := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • P)
  have heq : (fun k : ℕ => ((Nat.factorial k : ℂ)⁻¹) • (c • P) ^ k) =
      fun k : ℕ => (((Nat.factorial k : ℂ)⁻¹ * c ^ k) • P + if k = 0 then 1 - P else 0) := by
    funext k
    rcases k with _ | m
    · simp
    · rw [smul_pow, IsIdempotentElem.pow_succ_eq m h, smul_smul]
      simp
  rw [heq] at hT
  rw [hT.unique hS]
  module

def tor (P Q : Matrix (Fin n) (Fin n) ℂ) (c d : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (c - 1) • P + (d - 1) • Q

section Tor

variable {P Q : Matrix (Fin n) (Fin n) ℂ}

theorem tor_P (hP : P * P = P) (hQP : Q * P = 0) (c d : ℂ) : tor P Q c d * P = c • P := by
  simp only [tor, add_mul, one_mul, smul_mul_assoc, hP, hQP, smul_zero, add_zero]
  module

theorem Q_tor (hQ : Q * Q = Q) (hQP : Q * P = 0) (c d : ℂ) : Q * tor P Q c d = d • Q := by
  simp only [tor, mul_add, mul_one, mul_smul_comm, hQ, hQP, smul_zero, add_zero]
  module

theorem tor_tor (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0) (c d c' d' : ℂ) :
    tor P Q c d * tor P Q c' d' = tor P Q (c * c') (d * d') := by
  simp only [tor, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, hP, hQ,
    hPQ, hQP, smul_zero, add_zero]
  module

theorem tor_one : tor P Q 1 1 = 1 := by
  simp [tor]

private theorem norm_le_one_of_isStarProjection {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 := by
  have h1 : Pᴴ = P := hP.isSelfAdjoint
  have h2 : P * P = P := hP.isIdempotentElem
  have h3 := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [h1, h2] at h3
  nlinarith [norm_nonneg P]

theorem norm_tor_le (hP : IsStarProjection P) (hQ : IsStarProjection Q) {c d : ℝ} (hc : 1 ≤ c) (hd : d ≤ 1)
    (hd' : 0 ≤ d) : ‖tor P Q c d‖ ≤ c := by
  have e : tor P Q (c : ℂ) (d : ℂ) = (d : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + ((1 - d : ℝ) : ℂ) • (1 - Q) +
      ((c - 1 : ℝ) : ℂ) • P := by
    simp only [tor]
    push_cast
    module
  have hn : ∀ r : ℝ, 0 ≤ r → ∀ A : Matrix (Fin n) (Fin n) ℂ, ‖A‖ ≤ 1 → ‖(r : ℂ) • A‖ ≤ r := by
    intro r hr A hA
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr]
    exact mul_le_of_le_one_right hr hA
  rw [e]
  calc _ ≤ _ := norm_add₃_le
    _ ≤ d + (1 - d) + (c - 1) :=
        add_le_add (add_le_add (hn d hd' 1 (norm_le_one_of_isStarProjection (IsStarProjection.one _)))
          (hn _ (by linarith) _ (norm_le_one_of_isStarProjection hQ.one_sub))) (hn _ (by linarith) _ (norm_le_one_of_isStarProjection hP))
    _ = c := by ring

theorem tor_symm (c d : ℂ) : tor P Q c d = tor Q P d c := by
  simp only [tor]
  abel

theorem exp_tor (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0) (s : ℂ) :
    NormedSpace.exp (s • (P - Q)) = tor P Q (Complex.exp s) (Complex.exp (-s)) := by
  have hc : Commute (s • P) ((-s) • Q) := by
    show (s • P) * ((-s) • Q) = ((-s) • Q) * (s • P)
    simp only [smul_mul_assoc, mul_smul_comm, hPQ, hQP, smul_zero]
  rw [show s • (P - Q) = s • P + (-s) • Q by module, Matrix.exp_add_of_commute _ _ hc,
    exp_idem hP, exp_idem hQ]
  simp only [tor, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPQ,
    smul_zero, add_zero]

theorem tor_conj (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (h1 : X * P = 0) (h2 : Q * X = 0) (h3 : (1 - P) * X * (1 - Q) = 0)
    (c d : ℂ) : tor P Q c d * X * tor P Q d c =
      c • (P * X + X * Q - (2 : ℂ) • (P * X * Q)) + (c ^ 2) • (P * X * Q) := by
  have hXP : P * X * P = 0 := by rw [mul_assoc, h1, mul_zero]
  have hL : tor P Q c d * X = X + (c - 1) • (P * X) := by
    simp only [tor, add_mul, one_mul, smul_mul_assoc, h2, smul_zero, add_zero]
  have h3' : X - P * X - X * Q + P * X * Q = 0 := by
    rw [← h3]; simp only [sub_mul, mul_sub, one_mul, mul_one]; abel
  rw [hL]
  simp only [tor, add_mul, mul_add, mul_one, smul_mul_assoc, mul_smul_comm, h1, hXP, smul_zero, add_zero]
  linear_combination (norm := module) h3'

end Tor

theorem mem_NW {ε : Fin n → Bool} {W : Submodule ℂ (Fin n → ℂ)} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Pᴴ = P) (h' : P * P = P) (hW : ∀ x, x ∈ W ↔ P *ᵥ x = x) (m : UJ ε) :
    m ∈ NW ε W ↔ (umat m - 1) * P = 0 ∧ (Jm ε * P * Jm ε) * (umat m - 1) = 0 ∧
      (1 - P) * (umat m - 1) * (1 - Jm ε * P * Jm ε) = 0 := by
  have memnw1 : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ),
      (∀ v, star y ⬝ᵥ (M *ᵥ v) = 0) ↔ Mᴴ *ᵥ y = 0 := by
    intro M y
    have e : ∀ v, star y ⬝ᵥ (M *ᵥ v) = star (Mᴴ *ᵥ y) ⬝ᵥ v := by
      intro v
      rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    constructor
    · intro hv
      have hself := hv (Mᴴ *ᵥ y)
      rw [e] at hself
      exact dotProduct_star_self_eq_zero.1 hself
    · intro hz v
      simp [e, hz]
  have memnw2 : ∀ (M : Matrix (Fin n) (Fin n) ℂ), M = 0 ↔ ∀ v, M *ᵥ v = 0 := fun M =>
    ⟨fun hM v => by rw [hM, Matrix.zero_mulVec], fun hv => ext_mulVec fun v => by rw [hv, Matrix.zero_mulVec]⟩
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  have hQ : (Jm ε * P * Jm ε) * (Jm ε * P * Jm ε) = Jm ε * P * Jm ε := by
    calc (Jm ε * P * Jm ε) * (Jm ε * P * Jm ε) = Jm ε * P * (Jm ε * Jm ε) * P * Jm ε := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε * P * Jm ε := by rw [hJJ, Matrix.mul_one, Matrix.mul_assoc (Jm ε) P P, h']
  have hQQ0 : (Jm ε * P * Jm ε) * (1 - Jm ε * P * Jm ε) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hQ, sub_self]

  have ko : ∀ y, (∀ x ∈ W, star y ⬝ᵥ (Jm ε *ᵥ x) = 0) ↔ (Jm ε * P * Jm ε) *ᵥ y = 0 := by
    intro y
    have hr : (∀ x ∈ W, star y ⬝ᵥ (Jm ε *ᵥ x) = 0) ↔ ∀ v, star y ⬝ᵥ ((Jm ε * P) *ᵥ v) = 0 := by
      constructor
      · intro hy v
        rw [← Matrix.mulVec_mulVec]
        exact hy _ ((hW _).2 (by rw [Matrix.mulVec_mulVec, h']))
      · intro hv x hx
        have hx' := hv x
        rwa [← Matrix.mulVec_mulVec, (hW x).1 hx] at hx'
    have e2 : P * Jm ε = Jm ε * (Jm ε * P * Jm ε) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    rw [hr, memnw1, Matrix.conjTranspose_mul, h, hJh]
    constructor
    · intro hz
      rw [Matrix.mul_assoc (Jm ε) P (Jm ε), ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
    · intro hz
      rw [e2, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  simp only [NW, Set.mem_setOf_eq]
  unfold herm
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · refine (memnw2 _).2 fun v => ?_
      rw [← Matrix.mulVec_mulVec]
      exact h1 _ ((hW _).2 (by rw [Matrix.mulVec_mulVec, h']))
    · refine (memnw2 _).2 fun v => ?_
      rw [← Matrix.mulVec_mulVec]
      exact (ko _).1 (fun x hx => h3 v x hx)
    · refine (memnw2 _).2 fun v => ?_
      have hy : (Jm ε * P * Jm ε) *ᵥ ((1 - Jm ε * P * Jm ε) *ᵥ v) = 0 := by
        rw [Matrix.mulVec_mulVec, hQQ0, Matrix.zero_mulVec]
      have hin := h2 _ ((ko _).2 hy)
      rw [hW] at hin
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hin, sub_self]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [← (hW x).1 hx, Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec]
    · intro y hy
      have hQy : (Jm ε * P * Jm ε) *ᵥ y = 0 := (ko y).1 hy
      have e3 := congrArg (fun M => M *ᵥ y) h3
      simp only [Matrix.zero_mulVec] at e3
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hQy, sub_zero, ← Matrix.mulVec_mulVec,
        Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at e3
      rw [hW]
      exact e3.symm
    · intro y x hx
      have hz : (Jm ε * P * Jm ε) *ᵥ ((umat m - 1) *ᵥ y) = 0 := by
        rw [Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec]
      exact (ko _).2 hz x hx

def mid (J P : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • ((1 + J) * (1 - P - J * P * J))

theorem mid_facts {J P : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hJ' : Jᴴ = J)
    (h : Pᴴ = P) (h' : P * P = P) (hi : P * J * P = 0) :
    (mid J P)ᴴ = mid J P ∧ mid J P * mid J P = mid J P ∧ J * mid J P = mid J P ∧ mid J P * J = mid J P ∧
      P * mid J P = 0 ∧ mid J P * P = 0 ∧
      (mid J P).trace = (1 / 2 : ℂ) * (1 + J).trace - P.trace := by
  have hJJ : ∀ x : Matrix (Fin n) (Fin n) ℂ, J * (J * x) = x := fun x => by rw [← mul_assoc, hJ, one_mul]
  have hPP : ∀ x : Matrix (Fin n) (Fin n) ℂ, P * (P * x) = P * x := fun x => by rw [← mul_assoc, h']
  have hi' : P * (J * P) = 0 := by rw [← mul_assoc, hi]
  have hi'' : ∀ x : Matrix (Fin n) (Fin n) ℂ, P * (J * (P * x)) = 0 := fun x => by
    rw [← mul_assoc, ← mul_assoc, hi, zero_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have htr1 : (J * (P * J)).trace = P.trace := by rw [Matrix.trace_mul_comm, mul_assoc, hJ, mul_one]
  have htr2 : (J * P).trace = 0 := by
    calc (J * P).trace = (J * P * P).trace := by rw [mul_assoc, h']
      _ = (P * (J * P)).trace := Matrix.trace_mul_comm (J * P) P
      _ = 0 := by rw [hi', Matrix.trace_zero]
  have htr3 : (P * J).trace = 0 := by rw [Matrix.trace_mul_comm]; exact htr2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mid, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_add, Matrix.conjTranspose_one, hJ', h, hs]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_assoc, hJJ, hJ]
    module
  · simp only [mid, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_assoc, hJJ, hJ, hPP, h', hi', hi'',
      mul_zero, sub_zero, add_zero]
    module
  · simp only [mid, mul_smul_comm]
    simp only [mul_sub, mul_add, add_mul, mul_one, one_mul, mul_assoc, hJJ, hJ]
    module
  · simp only [mid, smul_mul_assoc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_assoc, hJJ, hJ]
    module
  · simp only [mid, mul_smul_comm]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_assoc, hJJ, hJ, hPP, h', hi', hi'',
      mul_zero, zero_mul, sub_zero, add_zero]
    module
  · simp only [mid, smul_mul_assoc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_assoc, hJJ, hJ, hPP, h', hi', hi'',
      mul_zero, zero_mul, sub_zero, add_zero]
    module
  · simp only [mid, Matrix.trace_smul, mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_assoc, hJJ,
      hPP, hi', hi'', Matrix.trace_sub, Matrix.trace_add, htr1, htr2, htr3, smul_eq_mul]
    ring

private theorem mul_mul_right_of_mul_eq {l m p q : Type*} [Fintype m] [Fintype p] {A : Matrix l m ℂ} {B : Matrix m p ℂ}
    {C : Matrix l p ℂ} (h : A * B = C) (W : Matrix p q ℂ) : A * (B * W) = C * W := by
  rw [← Matrix.mul_assoc, h]

private theorem mul_mul_mul_right_of_mul_mul_eq {l m p q s : Type*} [Fintype m] [Fintype p] [Fintype q] {A : Matrix l m ℂ}
    {B : Matrix m p ℂ} {C : Matrix p q ℂ} {D : Matrix l q ℂ} (h : A * B * C = D) (W : Matrix q s ℂ) :
    A * (B * (C * W)) = D * W := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

private theorem conjTranspose_mul_mul_eq_zero_of_proj {r s : ℕ} {X : Matrix (Fin n) (Fin r) ℂ} {Y : Matrix (Fin n) (Fin s) ℂ}
    {M N A : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * X = 1) (hXM : X * Xᴴ = M) (hY : Yᴴ * Y = 1)
    (hYN : Y * Yᴴ = N) (h : M * A * N = 0) : Xᴴ * A * Y = 0 := by
  calc Xᴴ * A * Y = (Xᴴ * X) * Xᴴ * A * (Y * (Yᴴ * Y)) := by
        rw [hX, hY, Matrix.one_mul, Matrix.mul_one]
    _ = Xᴴ * (X * Xᴴ * A * (Y * Yᴴ)) * Y := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hXM, hYN, h, Matrix.mul_zero, Matrix.zero_mul]

private theorem mul_eq_smul_of_mul_proj_eq_smul {r : ℕ} {X : Matrix (Fin n) (Fin r) ℂ} {M A : Matrix (Fin n) (Fin n) ℂ} {c : ℂ}
    (hX : Xᴴ * X = 1) (hXM : X * Xᴴ = M) (h : A * M = c • M) : A * X = c • X := by
  calc A * X = A * (X * Xᴴ) * X := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hX, Matrix.mul_one]
    _ = c • X := by rw [hXM, h, Matrix.smul_mul, ← hXM, Matrix.mul_assoc, hX, Matrix.mul_one]

private theorem eq_zero_of_eq_neg_flag_measures {x : Matrix (Fin n) (Fin n) ℂ} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    nth_rw 2 [h]
    exact add_neg_cancel _
  calc x = (1 / 2 : ℂ) • ((2 : ℂ) • x) := by rw [smul_smul]; norm_num
    _ = 0 := by rw [h2, smul_zero]

private theorem frame_decomposition_of_projection_J {J P : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hJ' : Jᴴ = J) (h : Pᴴ = P)
    (h' : P * P = P) (hi : P * J * P = 0) :
    ∃ (r s t : ℕ) (B : Matrix (Fin n) (Fin r) ℂ) (D : Matrix (Fin n) (Fin s) ℂ) (E : Matrix (Fin n) (Fin t) ℂ),
      (r : ℂ) = P.trace ∧ (s : ℂ) = (1 / 2 : ℂ) * (1 + J).trace - P.trace ∧
      (t : ℂ) = (1 / 2 : ℂ) * (1 + -J).trace - P.trace ∧
      Bᴴ * B = 1 ∧ Dᴴ * D = 1 ∧ Eᴴ * E = 1 ∧ B * Bᴴ = P ∧ Bᴴ * J * B = 0 ∧ Bᴴ * D = 0 ∧ Bᴴ * E = 0 ∧
      Dᴴ * B = 0 ∧ Eᴴ * B = 0 ∧ Dᴴ * E = 0 ∧ Eᴴ * D = 0 ∧ J * D = D ∧ J * E = -E ∧ Dᴴ * J = Dᴴ ∧
      Eᴴ * J = -Eᴴ ∧ B * Bᴴ + J * (B * (Bᴴ * J)) + D * Dᴴ + E * Eᴴ = 1 := by
  have hJ2 : (-J) * (-J) = 1 := by rw [neg_mul_neg, hJ]
  have hJ2' : (-J)ᴴ = -J := by rw [conjTranspose_neg, hJ']
  have hi2 : P * (-J) * P = 0 := by rw [mul_neg, neg_mul, hi, neg_zero]
  obtain ⟨hMs, hMM, hJM, hMJ, hPM, hMP, hMt⟩ := mid_facts hJ hJ' h h' hi
  obtain ⟨hNs, hNN, hJN, hNJ, hPN, hNP, hNt⟩ := mid_facts hJ2 hJ2' h h' hi2
  obtain ⟨r, B, hBB, hBP⟩ := proj_frame h h'
  obtain ⟨s, D, hDD, hDM⟩ := proj_frame hMs hMM
  obtain ⟨t, E, hEE, hEN⟩ := proj_frame hNs hNN
  have hJN' : J * mid (-J) P = -mid (-J) P := neg_eq_iff_eq_neg.mp (by rw [← neg_mul]; exact hJN)
  have hNJ' : mid (-J) P * J = -mid (-J) P := neg_eq_iff_eq_neg.mp (by rw [← mul_neg]; exact hNJ)
  have hMN : mid J P * mid (-J) P = 0 := eq_zero_of_eq_neg_flag_measures (by
    calc mid J P * mid (-J) P = mid J P * J * mid (-J) P := by rw [hMJ]
      _ = -(mid J P * mid (-J) P) := by rw [Matrix.mul_assoc, hJN', Matrix.mul_neg])
  have hNM : mid (-J) P * mid J P = 0 := eq_zero_of_eq_neg_flag_measures (by
    calc mid (-J) P * mid J P = mid (-J) P * (J * mid J P) := by rw [hJM]
      _ = -(mid (-J) P * mid J P) := by rw [← Matrix.mul_assoc, hNJ', Matrix.neg_mul])
  have hJD : J * D = D := by
    have := mul_eq_smul_of_mul_proj_eq_smul (A := J) (c := 1) hDD hDM (by rw [one_smul, hJM])
    rwa [one_smul] at this
  have hJE : J * E = -E := by
    have := mul_eq_smul_of_mul_proj_eq_smul (A := J) (c := -1) hEE hEN (by rw [neg_one_smul, hJN'])
    rwa [neg_one_smul] at this
  have hsum : mid J P + mid (-J) P = 1 - P - J * P * J := by
    simp only [mid, neg_mul, mul_neg, neg_neg, add_mul, one_mul]
    module
  refine ⟨r, s, t, B, D, E, ?_, ?_, ?_, hBB, hDD, hEE, hBP, conjTranspose_mul_mul_eq_zero_of_proj hBB hBP hBB hBP hi, ?_, ?_, ?_, ?_, ?_, ?_,
    hJD, hJE, ?_, ?_, ?_⟩
  · rw [← hBP, Matrix.trace_mul_comm, hBB, Matrix.trace_one, Fintype.card_fin]
  · rw [← hMt, ← hDM, Matrix.trace_mul_comm, hDD, Matrix.trace_one, Fintype.card_fin]
  · rw [← hNt, ← hEN, Matrix.trace_mul_comm, hEE, Matrix.trace_one, Fintype.card_fin]
  · have := conjTranspose_mul_mul_eq_zero_of_proj (A := 1) hBB hBP hDD hDM (by rw [Matrix.mul_one, hPM])
    rwa [Matrix.mul_one] at this
  · have := conjTranspose_mul_mul_eq_zero_of_proj (A := 1) hBB hBP hEE hEN (by rw [Matrix.mul_one, hPN])
    rwa [Matrix.mul_one] at this
  · have := conjTranspose_mul_mul_eq_zero_of_proj (A := 1) hDD hDM hBB hBP (by rw [Matrix.mul_one, hMP])
    rwa [Matrix.mul_one] at this
  · have := conjTranspose_mul_mul_eq_zero_of_proj (A := 1) hEE hEN hBB hBP (by rw [Matrix.mul_one, hNP])
    rwa [Matrix.mul_one] at this
  · have := conjTranspose_mul_mul_eq_zero_of_proj (A := 1) hDD hDM hEE hEN (by rw [Matrix.mul_one, hMN])
    rwa [Matrix.mul_one] at this
  · have := conjTranspose_mul_mul_eq_zero_of_proj (A := 1) hEE hEN hDD hDM (by rw [Matrix.mul_one, hNM])
    rwa [Matrix.mul_one] at this
  · have := congrArg Matrix.conjTranspose hJD
    rwa [conjTranspose_mul, hJ'] at this
  · have := congrArg Matrix.conjTranspose hJE
    rwa [conjTranspose_mul, hJ', conjTranspose_neg] at this
  · rw [hDM, hEN, ← Matrix.mul_assoc B, hBP, ← Matrix.mul_assoc, add_assoc (P + J * P * J), hsum]
    abel

theorem exists_K {J P P' : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hJ' : Jᴴ = J)
    (h : Pᴴ = P) (h' : P * P = P) (hi : P * J * P = 0)
    (g : P'ᴴ = P') (g' : P' * P' = P') (gi : P' * J * P' = 0) (ht : P.trace = P'.trace) :
    ∃ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * k = 1 ∧ k * J = J * k ∧ k * P' = P * k := by
  obtain ⟨r, s, t, B, D, E, hr, hs, htt, hBB, hDD, hEE, hBP, hBJB, hBD, hBE, hDB, hEB, hDE, hED, hJD, hJE,
    hDJ, hEJ, hC⟩ := frame_decomposition_of_projection_J hJ hJ' h h' hi
  obtain ⟨r', s', t', C, D', E', hr', hs', ht', hCC, hDD', hEE', hCP, hCJC, hCD, hCE, hDC, hEC, hDE', hED',
    hJD', hJE', hDJ', hEJ', hC'⟩ := frame_decomposition_of_projection_J hJ hJ' g g' gi
  have e1 : r' = r := Nat.cast_injective (R := ℂ) (by rw [hr', hr, ht])
  have e2 : s' = s := Nat.cast_injective (R := ℂ) (by rw [hs', hs, ht])
  have e3 : t' = t := Nat.cast_injective (R := ℂ) (by rw [ht', htt, ht])
  subst e1 e2 e3
  have hBJB' : Bᴴ * (J * B) = 0 := by rw [← Matrix.mul_assoc]; exact hBJB
  have hCJC' : Cᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCJC
  refine ⟨B * Cᴴ + J * (B * (Cᴴ * J)) + D * D'ᴴ + E * E'ᴴ, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ',
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, neg_zero, Matrix.mul_one, Matrix.one_mul, hJ, mul_mul_right_of_mul_eq hJ,
      hBB, mul_mul_right_of_mul_eq hBB, hDD, mul_mul_right_of_mul_eq hDD, hEE, mul_mul_right_of_mul_eq hEE, hBJB', mul_mul_mul_right_of_mul_mul_eq hBJB, hBD, mul_mul_right_of_mul_eq hBD, hBE,
      mul_mul_right_of_mul_eq hBE, hDB, mul_mul_right_of_mul_eq hDB, hEB, mul_mul_right_of_mul_eq hEB, hDE, mul_mul_right_of_mul_eq hDE, hED, mul_mul_right_of_mul_eq hED, hJD, mul_mul_right_of_mul_eq hJD,
      hJE, mul_mul_right_of_mul_eq hJE, hDJ, mul_mul_right_of_mul_eq hDJ, hEJ, mul_mul_right_of_mul_eq hEJ]
    first | exact hC' | (rw [← hC']; abel)
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.mul_one, Matrix.one_mul, hJ, mul_mul_right_of_mul_eq hJ, hJD, mul_mul_right_of_mul_eq hJD, hJE, mul_mul_right_of_mul_eq hJE, hDJ', hEJ']
    abel
  · rw [← hCP, ← hBP]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, neg_zero, Matrix.mul_one, Matrix.one_mul, hJ,
      mul_mul_right_of_mul_eq hJ, hBB, mul_mul_right_of_mul_eq hBB, hCC, mul_mul_right_of_mul_eq hCC, hBJB', mul_mul_mul_right_of_mul_mul_eq hBJB, hCJC', mul_mul_mul_right_of_mul_mul_eq hCJC, hBD, mul_mul_right_of_mul_eq hBD,
      hBE, mul_mul_right_of_mul_eq hBE, hDC, mul_mul_right_of_mul_eq hDC, hEC, mul_mul_right_of_mul_eq hEC]

theorem tor_comm {P Q p q : Matrix (Fin n) (Fin n) ℂ} (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0)
    (hQP : Q * P = 0) (hpq : p * q = 1) (h1 : P * (p * P) = p * P) (h2 : P * (q * P) = q * P)
    (h3 : Q * p * Q = Q * p) (h4 : Q * q * Q = Q * q) {c d : ℂ} (hcd : c * d = 1) :
    (tor P Q c d * p * tor P Q d c * q - 1) * P = 0 ∧ Q * (tor P Q c d * p * tor P Q d c * q - 1) = 0 ∧
      (1 - P) * (tor P Q c d * p * tor P Q d c * q - 1) * (1 - Q) = 0 := by
  have e1 : tor P Q d c * (q * P) = d • (q * P) := by
    calc tor P Q d c * (q * P) = tor P Q d c * P * (q * P) := by rw [mul_assoc, h2]
      _ = d • (q * P) := by rw [tor_P hP hQP, smul_mul_assoc, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_mul, one_mul]
    simp only [mul_assoc]
    rw [e1, mul_smul_comm, mul_smul_comm, ← mul_assoc p q P, hpq, one_mul, tor_P hP hQP, smul_smul,
      mul_comm d c, hcd, one_smul, sub_self]
  · calc Q * (tor P Q c d * p * tor P Q d c * q - 1)
        = Q * tor P Q c d * p * tor P Q d c * q - Q := by simp only [mul_sub, mul_one, mul_assoc]
      _ = (d • Q) * p * tor P Q d c * q - Q := by rw [Q_tor hQ hQP]
      _ = d • (Q * p * Q * tor P Q d c * q) - Q := by rw [h3]; simp only [smul_mul_assoc]
      _ = d • (Q * p * (Q * tor P Q d c) * q) - Q := by simp only [mul_assoc]
      _ = d • (Q * p * (c • Q) * q) - Q := by rw [Q_tor hQ hQP]
      _ = (d * c) • (Q * p * Q * q) - Q := by rw [mul_smul_comm, smul_mul_assoc, smul_smul]
      _ = 0 := by rw [mul_comm d c, hcd, one_smul, h3, mul_assoc, hpq, mul_one, sub_self]
  · have f1 : (1 - P) * tor P Q c d = 1 - P + (d - 1) • Q := by
      simp only [tor, mul_add, sub_mul, one_mul, mul_one, mul_smul_comm, hP, hPQ, sub_self, smul_zero,
        add_zero, sub_zero] <;> module
    have f2 : tor P Q d c * (1 - Q) = 1 - Q + (d - 1) • P := by
      simp only [tor, mul_sub, add_mul, one_mul, mul_one, smul_mul_assoc, hPQ, hQ, smul_zero, add_zero] <;>
        module
    have f3 : q * (1 - Q) = (1 - Q) * (q * (1 - Q)) := by
      have : Q * (q * (1 - Q)) = 0 := by simp only [mul_sub, mul_one, ← mul_assoc, h4, sub_self]
      rw [sub_mul, one_mul, this, sub_zero]
    have f4 : p * (1 - Q) = (1 - Q) * (p * (1 - Q)) := by
      have : Q * (p * (1 - Q)) = 0 := by simp only [mul_sub, mul_one, ← mul_assoc, h3, sub_self]
      rw [sub_mul, one_mul, this, sub_zero]
    have g1 : (1 - P + (d - 1) • Q) * (1 - Q) = (1 - P) * (1 - Q) := by
      rw [add_mul, smul_mul_assoc, mul_sub Q, mul_one, hQ, sub_self, smul_zero, add_zero]
    have g2 : (1 - P + (d - 1) • Q) * P = 0 := by
      rw [add_mul, smul_mul_assoc, hQP, smul_zero, add_zero, sub_mul, one_mul, hP, sub_self]
    have g3 : (1 - Q) * (1 - Q) = 1 - Q := by
      rw [sub_mul, one_mul, mul_sub, mul_one, hQ, sub_self, sub_zero]
    have main : (1 - P) * (tor P Q c d * p * tor P Q d c * q) * (1 - Q) = (1 - P) * (1 - Q) := by
      calc (1 - P) * (tor P Q c d * p * tor P Q d c * q) * (1 - Q)
          = (1 - P) * tor P Q c d * p * tor P Q d c * ((1 - Q) * (q * (1 - Q))) := by
            rw [← f3]; simp only [mul_assoc]
        _ = (1 - P) * tor P Q c d * p * (tor P Q d c * (1 - Q)) * (q * (1 - Q)) := by
            simp only [mul_assoc]
        _ = (1 - P) * tor P Q c d * p * (1 - Q + (d - 1) • P) * (q * (1 - Q)) := by rw [f2]
        _ = (1 - P) * tor P Q c d * (p * (1 - Q) + (d - 1) • (p * P)) * (q * (1 - Q)) := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
        _ = (1 - P) * tor P Q c d * ((1 - Q) * (p * (1 - Q)) + (d - 1) • (P * (p * P))) * (q * (1 - Q)) := by
            rw [← f4, h1]
        _ = (1 - P + (d - 1) • Q) * ((1 - Q) * (p * (1 - Q)) + (d - 1) • (P * (p * P))) * (q * (1 - Q)) := by
            rw [f1]
        _ = (1 - P) * (1 - Q) * (p * (1 - Q)) * (q * (1 - Q)) := by
            rw [mul_add, ← mul_assoc (1 - P + (d - 1) • Q) (1 - Q), g1, mul_smul_comm,
              ← mul_assoc (1 - P + (d - 1) • Q) P, g2, zero_mul, smul_zero, add_zero]
        _ = (1 - P) * (1 - Q) * (p * ((1 - Q) * (q * (1 - Q)))) := by simp only [mul_assoc]
        _ = (1 - P) * (1 - Q) * (p * (q * (1 - Q))) := by rw [← f3]
        _ = (1 - P) * (1 - Q) * (1 - Q) := by rw [← mul_assoc p q, hpq, one_mul]
        _ = (1 - P) * (1 - Q) := by rw [mul_assoc, g3]
    rw [mul_sub (1 - P), mul_one, sub_mul, main, sub_self]

theorem tendsto_UJ {ε : Fin n → Bool} {α : Type} {l : Filter α} {f : α → UJ ε} {g : UJ ε}
    (h : Filter.Tendsto (fun s => umat (f s)) l (nhds (umat g))) : Filter.Tendsto f l (nhds g) := by
  have hinv : ∀ x : UJ ε, (((x : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ) = Jm ε * (umat x)ᴴ * Jm ε := by
    intro x
    apply Units.inv_eq_of_mul_eq_one_left
    have hx : (umat x)ᴴ * Jm ε * umat x = Jm ε := x.2
    calc Jm ε * (umat x)ᴴ * Jm ε * umat x = Jm ε * ((umat x)ᴴ * Jm ε * umat x) := by
          simp only [mul_assoc]
      _ = 1 := by rw [hx, Jm_mul_self]
  rw [tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply]
  refine h.prodMk_nhds ?_
  simp only [hinv]
  have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => MulOpposite.op (Jm ε * Mᴴ * Jm ε) :=
    MulOpposite.continuous_op.comp ((continuous_const.mul continuous_id.matrix_conjTranspose).mul
      continuous_const)
  exact (hc.tendsto _).comp h

theorem le_dOp {g P : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} (hP : P ≠ 0)
    (h : g * P = Complex.exp s • P ∨ P * g = Complex.exp s • P) : s ≤ dOp g := by
  have hPn : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have he : ‖Complex.exp (s : ℂ)‖ = Real.exp s := by rw [Complex.norm_exp, Complex.ofReal_re]
  have key : Real.exp s * ‖P‖ ≤ ‖g‖ * ‖P‖ := by
    rcases h with h | h
    · calc Real.exp s * ‖P‖ = ‖Complex.exp (s : ℂ) • P‖ := by rw [norm_smul, he]
        _ = ‖g * P‖ := by rw [h]
        _ ≤ ‖g‖ * ‖P‖ := norm_mul_le _ _
    · calc Real.exp s * ‖P‖ = ‖Complex.exp (s : ℂ) • P‖ := by rw [norm_smul, he]
        _ = ‖P * g‖ := by rw [h]
        _ ≤ ‖P‖ * ‖g‖ := norm_mul_le _ _
        _ = ‖g‖ * ‖P‖ := mul_comm _ _
  have hle : Real.exp s ≤ ‖g‖ := le_of_mul_le_mul_right key hPn
  have hg : 0 < ‖g‖ := lt_of_lt_of_le (Real.exp_pos s) hle
  show s ≤ Real.log ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖
  exact (Real.le_log_iff_exp_le hg).mpr hle

theorem isotropic_proj {ε : Fin n → Bool} {W : Submodule ℂ (Fin n → ℂ)} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Pᴴ = P) (h' : P * P = P) (hW : ∀ x, x ∈ W ↔ P *ᵥ x = x)
    (hi : ∀ x ∈ W, ∀ y ∈ W, herm (Jm ε) x y = 0) : P * Jm ε * P = 0 := by
  have key : ∀ x y, star y ⬝ᵥ ((P * Jm ε * P) *ᵥ x) = herm (Jm ε) (P *ᵥ x) (P *ᵥ y) := by
    intro x y
    rw [herm, Matrix.star_mulVec, h, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have memP : ∀ x, P *ᵥ x ∈ W := fun x => (hW _).2 (by rw [Matrix.mulVec_mulVec, h'])
  refine ext_mulVec fun x => ?_
  ext i
  have := key x (Pi.single i 1)
  rw [hi _ (memP x) _ (memP _)] at this
  simpa using this

private lemma mul_inv_mul_proj_of_ker_iff {n : ℕ} {P G Gi P' : Matrix (Fin n) (Fin n) ℂ} (hP : P * P = P) (hG : G * Gi = 1)
    (hW : ∀ x, x ∈ LinearMap.ker (Matrix.toLin' (P * G - G)) ↔ P' *ᵥ x = x) :
    P' * Gi * P = Gi * P := by
  apply ext_mulVec
  intro v
  have hx : (Gi * P) *ᵥ v ∈ LinearMap.ker (Matrix.toLin' (P * G - G)) := by
    have e : G * (Gi * P) = P := by rw [← Matrix.mul_assoc, hG, Matrix.one_mul]
    have h0 : (P * G - G) * (Gi * P) = 0 := by
      rw [sub_mul, Matrix.mul_assoc, e, hP, sub_self]
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  exact (hW _).1 hx

private lemma proj_mul_mul_proj_of_ker_iff {n : ℕ} {P G P' : Matrix (Fin n) (Fin n) ℂ} (hP' : P' * P' = P')
    (hW : ∀ x, x ∈ LinearMap.ker (Matrix.toLin' (P * G - G)) ↔ P' *ᵥ x = x) :
    P * G * P' = G * P' := by
  apply ext_mulVec
  intro v
  have hx : P' *ᵥ v ∈ LinearMap.ker (Matrix.toLin' (P * G - G)) :=
    (hW _).2 (by rw [Matrix.mulVec_mulVec, hP'])
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_mulVec, sub_mul, Matrix.sub_mulVec,
    sub_eq_zero] at hx
  exact hx

theorem exists_iwasawa {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Pᴴ = P) (h' : P * P = P) (hi : P * Jm ε * P = 0) (g : UJ ε) :
    ∃ k : UJ ε, umat k ∈ Kset ε ∧ P * (umat (g * k⁻¹) * P) = umat (g * k⁻¹) * P ∧
      P * (umat (g * k⁻¹)⁻¹ * P) = umat (g * k⁻¹)⁻¹ * P := by
  have hG : umat g * umat g⁻¹ = 1 := by simp only [umat, Subgroup.coe_inv, Units.mul_inv]
  have hGi : umat g⁻¹ * umat g = 1 := by simp only [umat, Subgroup.coe_inv, Units.inv_mul]
  obtain ⟨P', hP'h, hP'i, hW⟩ := exists_proj (LinearMap.ker (Matrix.toLin' (P * umat g - umat g)))
  have ha : P' * umat g⁻¹ * P = umat g⁻¹ * P := mul_inv_mul_proj_of_ker_iff h' hG hW
  have hb : P * umat g * P' = umat g * P' := proj_mul_mul_proj_of_ker_iff hP'i hW

  have htr : P.trace = P'.trace := by
    have hAP : umat g * (P' * umat g⁻¹ * P) = P := by rw [ha, ← Matrix.mul_assoc, hG, Matrix.one_mul]
    calc P.trace = (umat g * (P' * umat g⁻¹ * P)).trace := by rw [hAP]
      _ = ((umat g * P' * umat g⁻¹) * P).trace := by simp only [Matrix.mul_assoc]
      _ = (P * (umat g * P' * umat g⁻¹)).trace := Matrix.trace_mul_comm _ _
      _ = (umat g * P' * umat g⁻¹).trace := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb]
      _ = (umat g⁻¹ * (umat g * P')).trace := Matrix.trace_mul_comm _ _
      _ = P'.trace := by rw [← Matrix.mul_assoc, hGi, Matrix.one_mul]

  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have hiso : P' * Jm ε * P' = 0 := by
    calc P' * Jm ε * P' = P'ᴴ * ((umat g)ᴴ * Jm ε * umat g) * P' := by rw [hg, hP'h]
      _ = (P * umat g * P')ᴴ * Jm ε * (P * umat g * P') := by
          rw [hb]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = P'ᴴ * (umat g)ᴴ * (Pᴴ * Jm ε * P) * (umat g * P') := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [h, hi]; simp
  obtain ⟨k0, hk0u, hk0J, hk0P⟩ :=
    exists_K (Formalism.REAL.Jm_mul_self ε) (Formalism.REAL.Jm_conjTranspose ε) h h' hi hP'h hP'i hiso htr
  have hk0u' : k0 * k0ᴴ = 1 := mul_eq_one_comm.mp hk0u
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨k0, k0ᴴ, hk0u', hk0u⟩
  have hu : u ∈ UJ ε := by
    show k0ᴴ * Jm ε * k0 = Jm ε
    rw [Matrix.mul_assoc, ← hk0J, ← Matrix.mul_assoc, hk0u, Matrix.one_mul]
  have hk0P' : P' * k0ᴴ = k0ᴴ * P := by
    have := congrArg Matrix.conjTranspose hk0P
    simpa [Matrix.conjTranspose_mul, h, hP'h] using this
  refine ⟨⟨u, hu⟩, ?_, ?_, ?_⟩
  · show k0 ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k0 * Jm ε = Jm ε * k0
    exact ⟨Matrix.mem_unitaryGroup_iff.mpr (by rw [Matrix.star_eq_conjTranspose]; exact hk0u'), hk0J⟩
  · show P * (umat g * k0ᴴ * P) = umat g * k0ᴴ * P
    calc P * (umat g * k0ᴴ * P) = P * umat g * P' * k0ᴴ := by
          rw [Matrix.mul_assoc (umat g), ← hk0P']; simp only [Matrix.mul_assoc]
      _ = umat g * P' * k0ᴴ := by rw [hb]
      _ = umat g * k0ᴴ * P := by rw [Matrix.mul_assoc (umat g), hk0P', ← Matrix.mul_assoc]
  · show P * (k0 * umat g⁻¹ * P) = k0 * umat g⁻¹ * P
    have e : k0 * umat g⁻¹ * P = P * (k0 * umat g⁻¹ * P) := by
      calc k0 * umat g⁻¹ * P = k0 * (P' * umat g⁻¹ * P) := by rw [ha, Matrix.mul_assoc]
        _ = P * k0 * umat g⁻¹ * P := by rw [← hk0P]; simp only [Matrix.mul_assoc]
        _ = P * (k0 * umat g⁻¹ * P) := by simp only [Matrix.mul_assoc]
    rw [e, ← Matrix.mul_assoc P P, h']

private lemma mul_inv_one_mul_inv_eq_mul_inv {ε : Fin n → Bool} (p : UJ ε) :
    umat p⁻¹ = Jm ε * (umat p)ᴴ * Jm ε := by
  have hm : (umat p)ᴴ * Jm ε * umat p = Jm ε := p.2
  have hl : Jm ε * (umat p)ᴴ * Jm ε * umat p = 1 := by
    rw [show Jm ε * (umat p)ᴴ * Jm ε * umat p = Jm ε * ((umat p)ᴴ * Jm ε * umat p) by
      simp only [mul_assoc], hm, Jm_mul_self]
  have hr : umat p * umat p⁻¹ = 1 := by
    simp [umat]
  calc umat p⁻¹ = (Jm ε * (umat p)ᴴ * Jm ε * umat p) * umat p⁻¹ := by rw [hl, one_mul]
    _ = Jm ε * (umat p)ᴴ * Jm ε * (umat p * umat p⁻¹) := by rw [mul_assoc]
    _ = Jm ε * (umat p)ᴴ * Jm ε := by rw [hr, mul_one]

theorem perp_stable {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ} (h : Pᴴ = P) (p : UJ ε)
    (hp : P * (umat p⁻¹ * P) = umat p⁻¹ * P) :
    (Jm ε * P * Jm ε) * umat p * (Jm ε * P * Jm ε) = (Jm ε * P * Jm ε) * umat p := by
  have hJ := Jm_mul_self ε
  have hJh := Jm_conjTranspose ε
  have e := congrArg Matrix.conjTranspose hp
  rw [mul_inv_one_mul_inv_eq_mul_inv] at e
  simp only [Matrix.conjTranspose_mul, h, hJh, Matrix.conjTranspose_conjTranspose] at e
  calc Jm ε * P * Jm ε * umat p * (Jm ε * P * Jm ε)
      = Jm ε * (P * (Jm ε * (umat p * Jm ε)) * P) * Jm ε := by simp only [mul_assoc]
    _ = Jm ε * (P * (Jm ε * (umat p * Jm ε))) * Jm ε := by rw [e]
    _ = Jm ε * P * Jm ε * umat p * (Jm ε * Jm ε) := by simp only [mul_assoc]
    _ = Jm ε * P * Jm ε * umat p := by rw [hJ, mul_one]

private theorem tor_conjTranspose_of_hermitian {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : Pᴴ = P) (hQ : Qᴴ = Q) (c d : ℝ) :
    (tor P Q (c : ℂ) (d : ℂ))ᴴ = tor P Q c d := by
  simp [tor, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hP, hQ]

private theorem J_mul_tor_eq_tor_swap_mul_J {J P Q : Matrix (Fin n) (Fin n) ℂ} (hJP : J * P = Q * J) (hJQ : J * Q = P * J)
    (c d : ℂ) : J * tor P Q c d = tor P Q d c * J := by
  simp only [tor, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hJP, hJQ]
  abel

private theorem dOp_eq_log_norm (g : Matrix (Fin n) (Fin n) ℂ) : dOp g = Real.log ‖g‖ := rfl

private theorem log_le_of_le_exp' {x t : ℝ} (hx : 0 ≤ x) (hxt : x ≤ Real.exp t) (ht : 0 ≤ t) : Real.log x ≤ t := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; exact ht
  · exact (Real.log_le_log h hxt).trans (Real.log_exp t).le

theorem split_torus : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W → ∃ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm ∧ (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) ∧ (∀ s, dOp (umat (a s)) ≤ |s|) ∧ (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W ∧ |s| ≤ dOp (umat (m * a s))) ∧ (∀ m ∈ NW ε W, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) ∧ ∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W := by
  intro n ε W hW
  obtain ⟨hW0, hiso⟩ := hW
  obtain ⟨P, hPh, hPP, hPW⟩ := exists_proj W
  have hPJP : P * Jm ε * P = 0 := isotropic_proj hPh hPP hPW hiso
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Jm ε * P * Jm ε := ⟨_, rfl⟩
  have hQh : Qᴴ = Q := by
    rw [hQ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh, hPh, Matrix.mul_assoc]
  have hPQ : P * Q = 0 := by
    rw [hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPJP, Matrix.zero_mul]
  have hQP : Q * P = 0 := by
    rw [hQ, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPJP, Matrix.mul_zero]
  have hJP : Jm ε * P = Q * Jm ε := by
    rw [hQ, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hJQ : Jm ε * Q = P * Jm ε := by
    rw [hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hQQ : Q * Q = Q := by
    nth_rewrite 1 [hQ]
    rw [Matrix.mul_assoc, hJQ, Matrix.mul_assoc, ← Matrix.mul_assoc P P, hPP, hQ, Matrix.mul_assoc]
  have hPs : IsStarProjection P := ⟨hPP, hPh⟩
  have hQs : IsStarProjection Q := ⟨hQQ, hQh⟩
  have e1 : ∀ s : ℝ, Complex.exp (s : ℂ) = ((Real.exp s : ℝ) : ℂ) := fun s => (Complex.ofReal_exp s).symm
  have e2 : ∀ s : ℝ, Complex.exp (-(s : ℂ)) = ((Real.exp (-s) : ℝ) : ℂ) := fun s => by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have hcd : ∀ s : ℝ, Complex.exp (s : ℂ) * Complex.exp (-(s : ℂ)) = 1 := fun s => by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hdc : ∀ s : ℝ, Complex.exp (-(s : ℂ)) * Complex.exp (s : ℂ) = 1 := fun s => by
    rw [mul_comm, hcd]
  have hunit1 : ∀ s : ℝ, tor P Q (Complex.exp s) (Complex.exp (-s)) *
      tor P Q (Complex.exp (-s)) (Complex.exp s) = 1 := fun s => by
    rw [tor_tor hPP hQQ hPQ hQP, hcd, hdc, tor_one]
  have hunit2 : ∀ s : ℝ, tor P Q (Complex.exp (-s)) (Complex.exp s) *
      tor P Q (Complex.exp s) (Complex.exp (-s)) = 1 := fun s => by
    rw [tor_tor hPP hQQ hPQ hQP, hcd, hdc, tor_one]
  have hmem : ∀ s : ℝ, inUJ ε (tor P Q (Complex.exp s) (Complex.exp (-s))) := fun s => by
    show (tor P Q _ _)ᴴ * Jm ε * tor P Q _ _ = Jm ε
    rw [e1, e2, tor_conjTranspose_of_hermitian hPh hQh, Matrix.mul_assoc, J_mul_tor_eq_tor_swap_mul_J hJP hJQ, ← Matrix.mul_assoc,
      tor_tor hPP hQQ hPQ hQP, ← e1, ← e2, hcd, hdc, tor_one, Matrix.one_mul]
  obtain ⟨a, ha, hai⟩ : ∃ a : ℝ → UJ ε, (∀ s, umat (a s) = tor P Q (Complex.exp s) (Complex.exp (-s))) ∧
      ∀ s, umat (a s)⁻¹ = tor P Q (Complex.exp (-s)) (Complex.exp s) :=
    ⟨fun s => ⟨⟨_, _, hunit1 s, hunit2 s⟩, hmem s⟩, fun _ => rfl, fun _ => rfl⟩
  have hmul : ∀ x y : UJ ε, umat (x * y) = umat x * umat y := fun _ _ => rfl
  have hone : umat (1 : UJ ε) = 1 := rfl
  have hP0 : P ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hx' := (hPW x).1 hx
    rw [h, Matrix.zero_mulVec] at hx'
    exact hx0 hx'.symm
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hP0
    have hJQJ : Jm ε * Q * Jm ε = P := by
      rw [hJQ, Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← hJQJ, h, Matrix.mul_zero, Matrix.zero_mul]

  have hconj : ∀ s : ℝ, ∀ m ∈ NW ε W, umat (a s * m * (a s)⁻¹) - 1 =
      Complex.exp (s : ℂ) • (P * (umat m - 1) + (umat m - 1) * Q - (2 : ℂ) • (P * (umat m - 1) * Q)) +
        Complex.exp (s : ℂ) ^ 2 • (P * (umat m - 1) * Q) := by
    intro s m hm
    obtain ⟨h1, h2, h3⟩ := (mem_NW hPh hPP hPW m).1 hm
    rw [← hQ] at h2 h3
    rw [hmul, hmul, ha, hai, ← tor_conj hPP hQQ hPQ hQP h1 h2 h3 _ (Complex.exp (-(s : ℂ))),
      mul_sub, sub_mul, mul_one, hunit1]
  refine ⟨a, P - Q, ⟨?_, ?_⟩, fun s => ?_, fun s => ?_, fun s m hm => ⟨?_, ?_⟩, fun m hm => ?_, fun g => ?_⟩
  · show (P - Q)ᴴ * Jm ε + Jm ε * (P - Q) = 0
    rw [Matrix.conjTranspose_sub, hPh, hQh, sub_mul, mul_sub, hJP, hJQ]
    abel
  · rw [sub_mul, mul_sub, hJP, hJQ]
    abel
  · rw [ha]
    exact (exp_tor hPP hQQ hPQ hQP (s : ℂ)).symm
  · rw [dOp_eq_log_norm, ha, e1, e2]
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs]
      exact log_le_of_le_exp' (norm_nonneg _) (norm_tor_le hPs hQs (Real.one_le_exp hs)
        (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _).le) hs
    · rw [abs_of_neg hs, tor_symm]
      exact log_le_of_le_exp' (norm_nonneg _) (norm_tor_le hQs hPs (Real.one_le_exp (by linarith))
        (Real.exp_le_one_iff.mpr hs.le) (Real.exp_pos _).le) (by linarith)
  · rw [mem_NW hPh hPP hPW, ← hQ]
    obtain ⟨h1, h2, h3⟩ := (mem_NW hPh hPP hPW m).1 hm
    rw [← hQ] at h2 h3
    rw [hconj s m hm]
    generalize umat m - 1 = X at h1 h2 h3
    have hPP' : ∀ Y, P * (P * Y) = P * Y := fun Y => by rw [← Matrix.mul_assoc, hPP]
    have hQQ' : ∀ Y, Q * (Q * Y) = Q * Y := fun Y => by rw [← Matrix.mul_assoc, hQQ]
    have hPQ' : ∀ Y, P * (Q * Y) = 0 := fun Y => by rw [← Matrix.mul_assoc, hPQ, Matrix.zero_mul]
    have hQP' : ∀ Y, Q * (P * Y) = 0 := fun Y => by rw [← Matrix.mul_assoc, hQP, Matrix.zero_mul]
    have h1' : ∀ Y, X * (P * Y) = 0 := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.zero_mul]
    have h2' : ∀ Y, Q * (X * Y) = 0 := fun Y => by rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, one_mul,
        mul_one, h1, h1', h2, h2', hPP, hQQ, hPQ, hQP, hPP', hQQ', hPQ', hQP', Matrix.mul_zero, Matrix.zero_mul,
        smul_zero, add_zero, zero_add, sub_zero, zero_sub, sub_self, neg_zero] <;>
      module
  · obtain ⟨h1, h2, -⟩ := (mem_NW hPh hPP hPW m).1 hm
    rw [← hQ] at h2
    have hmP : umat m * P = P := by rwa [sub_mul, one_mul, sub_eq_zero] at h1
    have hQm : Q * umat m = Q := by rwa [mul_sub, mul_one, sub_eq_zero] at h2
    rw [hmul, ha]
    rcases le_or_gt 0 s with hs | hs
    · rw [abs_of_nonneg hs]
      exact le_dOp hP0 (Or.inl (by rw [Matrix.mul_assoc, tor_P hPP hQP, mul_smul_comm, hmP]))
    · rw [abs_of_neg hs]
      refine le_dOp (s := -s) hQ0 (Or.inr ?_)
      rw [← Matrix.mul_assoc, hQm, Q_tor hQQ hQP, Complex.ofReal_neg]
  · apply tendsto_UJ
    rw [hone]
    have hc : Filter.Tendsto (fun s : ℝ => Complex.exp (s : ℂ)) Filter.atBot (nhds 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_atBot
      simpa [Function.comp_def, Complex.ofReal_exp] using this
    have hlim := (tendsto_const_nhds (x := (1 : Matrix (Fin n) (Fin n) ℂ))).add
      ((hc.smul_const (P * (umat m - 1) + (umat m - 1) * Q - (2 : ℂ) • (P * (umat m - 1) * Q))).add
        ((hc.pow 2).smul_const (P * (umat m - 1) * Q)))
    simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hlim
    refine hlim.congr fun s => ?_
    rw [← hconj s m hm, add_sub_cancel]
  · obtain ⟨k, hk, hp1, hp2⟩ := exists_iwasawa hPh hPP hPJP g
    refine ⟨k, hk, fun s => ?_⟩
    have hgrp : a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ = a s * (g * k⁻¹) * (a s)⁻¹ * (g * k⁻¹)⁻¹ := by group
    have hq1 := perp_stable hPh (g * k⁻¹) hp2
    have hq2 := perp_stable hPh (g * k⁻¹)⁻¹ (by rw [inv_inv]; exact hp1)
    rw [← hQ] at hq1 hq2
    have hpq : umat (g * k⁻¹) * umat (g * k⁻¹)⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    rw [hgrp, mem_NW hPh hPP hPW, ← hQ, hmul, hmul, hmul, ha, hai]
    exact tor_comm hPP hQQ hPQ hQP hpq hp1 hp2 hq1 hq2 (hcd s)

end GlobalTheory.IsoTorus
