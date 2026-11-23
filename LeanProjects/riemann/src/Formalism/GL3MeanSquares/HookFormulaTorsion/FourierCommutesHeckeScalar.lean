import Mathlib
import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset

theorem odd_half_shift_sign_dichotomy_bound : OddHalfShiftSignDichotomyBound := by
  intro t _ ht ε hε v W C N hv
  have ht' : (0:ℝ) ≤ t := by exact_mod_cast ht
  rcases hε with rfl | rfl
  · refine ⟨Or.inr (by push_cast; ring), ?_⟩
    push_cast
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1, hv.2]
  · refine ⟨Or.inl (by push_cast; ring), ?_⟩
    push_cast
    rw [abs_le] at hv ⊢
    constructor <;> linarith [hv.1, hv.2]

theorem exponent_loss_per_embedding : ExponentLossPerEmbedding := by
  intro ι Ψ p _ W nu C N t hW ht htN hnu
  have : ∑ τ ∈ Ψ, (2 * W τ + C * N + if p τ then nu τ else 0) ≤ ∑ τ ∈ Ψ, (4 * W τ + (C+1) * N) := by
    apply Finset.sum_le_sum
    intro τ hτ
    split_ifs with h
    · linarith [hnu τ hτ h, hW τ hτ]
    · linarith [hW τ hτ]
  refine this.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring

theorem interlacing_degree_difference : InterlacingDegreeDifference := by
  intro n lam sg h
  have e1 : ∑ i, lam i - ∑ i, sg i = lam 0 + ∑ i : Fin n, (lam i.succ - sg i) := by
    rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]; ring
  have e2 : ∑ i, lam i - ∑ i, sg i = lam (Fin.last n) + ∑ i : Fin n, (lam i.castSucc - sg i) := by
    rw [Fin.sum_univ_castSucc, Finset.sum_sub_distrib]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    have : ∑ i : Fin n, (lam i.succ - sg i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [(h i).2])
    linarith
  · rw [e2]
    have : 0 ≤ ∑ i : Fin n, (lam i.castSucc - sg i) := Finset.sum_nonneg (fun i _ => by linarith [(h i).1])
    linarith
  · intro hn W h1 h2
    rw [e2]
    have : lam (Fin.castSucc ⟨0,hn⟩) - sg ⟨0,hn⟩ ≤ ∑ i : Fin n, (lam i.castSucc - sg i) :=
      Finset.single_le_sum (f := fun i : Fin n => lam i.castSucc - sg i) (fun i _ => by linarith [(h i).1]) (Finset.mem_univ _)
    have h0 : (Fin.castSucc ⟨0,hn⟩ : Fin (n+1)) = 0 := rfl
    rw [h0] at this
    linarith

theorem fourier_commutes_hecke_scalar : FourierCommutesHeckeScalar := by
  intro R _ M M' _ _ _ _ U D G U' D' G' K c a a' h1 h2 h3 h4
  calc a' • (K ∘ₗ D ∘ₗ G) = (a' • LinearMap.id) ∘ₗ (K ∘ₗ D ∘ₗ G) := by ext; simp
    _ = D' ∘ₗ (U' ∘ₗ K) ∘ₗ D ∘ₗ G := by rw [← h2]; rfl
    _ = c • (D' ∘ₗ K ∘ₗ (U ∘ₗ D) ∘ₗ G) := by rw [h1]; ext; simp
    _ = (c * a) • (D' ∘ₗ (K ∘ₗ G)) := by rw [h3]; ext; simp [mul_smul]
    _ = _ := by rw [h4]

theorem hecke_kernel_scalar_invariance : HeckeKernelScalarInvariance := by
  intro q _ n n' w ph c fW
  simp [kerK, Matrix.smul_vecMul]

theorem quotient_length_embedding_bound : QuotientLengthEmbeddingBound := by
  intro R _ M _ _ A N
  apply Module.length_le_of_injective (Submodule.mapQ (N.comap A.subtype) N A.subtype le_rfl)
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
  simp

theorem slope_kronecker_formula : SlopeTensorProductAdditive := by
  intro a b _ _ _ _ _ _ A B hA hB
  rw [Matrix.det_kronecker, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have ha : (Fintype.card a : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card b : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

theorem primitive_orbit_functional_unique : PrimitiveOrbitFunctionalUnique := by
  intro F _ n f g e he
  constructor
  · rintro ⟨h1, h2⟩
    funext j
    have := h1 (Pi.single j 1 - f j • e) (by simp [dotProduct_sub, he])
    simp [dotProduct_sub, h2] at this
    exact (sub_eq_zero.mp this)
  · rintro rfl
    exact ⟨fun _ h => h, he⟩

theorem length_bound_under_twist : LemmaB'_twist := by
  intro k lam a W b' h0 hW hl
  have hk : (0:ℚ) < (k:ℚ) + 2 := by positivity
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW (Fin.last (k+1)) (by simp [Fin.ext_iff]))
  have hb : b' ≤ W := by
    have := hW (Fin.last (k+1)) (by simp [Fin.ext_iff])
    rw [hl, abs_neg] at this
    exact le_trans (le_abs_self _) this
  rw [div_add' _ _ _ hk.ne', div_le_div_iff_of_pos_right hk, Fin.sum_univ_succ, h0]
  have : ∑ i : Fin (k+1), (lam i.succ + b') ≤ ∑ i : Fin (k+1), (W + W) := by
    apply Finset.sum_le_sum
    intro i _
    have := hW i.succ (Fin.succ_ne_zero i)
    linarith [le_trans (le_abs_self _) this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

theorem joint_coefficient_formula : Joint_coef := by
  intro ι TT a W L k m f q e logP muM0 muRam muN EP E0 Eprice hL hk hm hf hq ha hW h1 h2 h3 h4
  have hk0 : 0 < k := by linarith
  have key : ∑ τ ∈ TT, m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) ≤
      m / k * (∑ τ ∈ TT, a τ) + ∑ τ ∈ TT, (m * (3 * W τ + k) * (1 + 2 * f / q) + m * f / (2 * k)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro τ hτ
    obtain ⟨h0, h4a⟩ := ha τ hτ
    have : a τ / q ≤ 1 / 4 := by rw [div_le_iff₀ hq]; linarith
    have e1 : m * (a τ / k + 3 * W τ + k) * (1 + 2 * f / q) =
      m / k * a τ + m * (3 * W τ + k) * (1 + 2 * f / q) + (2 * m * f / k) * (a τ / q) := by
      field_simp; ring
    have e2 : m * f / (2 * k) = (2 * m * f / k) * (1/4) := by field_simp; ring
    rw [e1, e2]
    have : (2 * m * f / k) * (a τ / q) ≤ (2 * m * f / k) * (1/4) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have key2 := mul_le_mul_of_nonneg_right key hL.le
  have e3 : -(1 - (m + 1) / k) * (∑ τ ∈ TT, a τ) * L = -(∑ τ ∈ TT, a τ) * L + (∑ τ ∈ TT, a τ) / k * L + m / k * (∑ τ ∈ TT, a τ) * L := by
    field_simp; ring
  rw [e3]
  nlinarith

theorem exponent_total_bound : ExponentTotalBound := by
  intro ι Ψ TT VV W bp m t f N C1 C2 e1 hV hm ht htN hf hC1 hC2 hW hb hWb he
  have hN : 1 ≤ N := by linarith
  set A := ∑ τ ∈ Ψ, W τ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg hW
  set Bs := ∑ τ ∈ TT, (bp τ + N) with hB
  have hB0 : 0 ≤ Bs := Finset.sum_nonneg (fun τ h => by linarith [hb τ h])
  have s1 : ∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N) ≤ (C2 + 4) * Bs := by
    calc _ ≤ ∑ τ ∈ VV, (C2 + 4) * (bp τ + N) := by
          apply Finset.sum_le_sum
          intro τ h
          have := hWb τ h
          have := hb τ (hV h)
          nlinarith
      _ ≤ ∑ τ ∈ TT, (C2 + 4) * (bp τ + N) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hV
          intro τ h _
          have := hb τ h
          positivity
      _ = _ := by rw [Finset.mul_sum]
  have s2 : (∑ τ ∈ VV, (t + 1 + 2 * W τ + C2 * N)) * (m * (m + 1) / 2) ≤ (C2 + 4) * Bs * (m * m) := by
    calc _ ≤ (C2 + 4) * Bs * (m * (m + 1) / 2) := mul_le_mul_of_nonneg_right s1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have s3 : m * e1 ≤ m * (4 * A + C1 * f * N) := mul_le_mul_of_nonneg_left he (by linarith)
  have s4 : C1 * f * N * m ≤ C1 * f * N * (m * m) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have p1 : 0 ≤ (C1 + C2 + 5) * m * A := by positivity
  have p2 : 0 ≤ (C2 + 9) * m * (f * m * N) := by positivity
  have p3 : 0 ≤ (C1 + 5) * m * (m * Bs) := by positivity
  nlinarith

theorem kronecker_root_of_unity' : KroneckerRootOfUnity := by
  intro K _ _ α hα h0 hle hμ
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ h0 hα hle
  exact hμ α ⟨n, hn, h⟩

theorem consecutive_ratio_power_bound : ConsecutiveRatioPowerBound := by
  intro q f N hN hf hq
  have h1 : 4 * f + 2 ≤ q := by nlinarith
  have hQ : (4:ℝ) * f + 2 ≤ q := by exact_mod_cast h1
  have hF : (1:ℝ) ≤ f := by exact_mod_cast hf
  generalize (q:ℝ) = Q at *
  have hQ2 : 0 < Q - 2 := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = 1 / (Q - 2) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1/4 := by rw [hx, div_le_div_iff₀ hQ2 (by norm_num)]; linarith
  have e : (Q - 1)/(Q - 2) = 1 + x := by rw [hx]; field_simp; ring
  rw [e]
  have b1 : 1 + (f:ℝ) * (-x) ≤ (1 + (-x))^f := one_add_mul_le_pow (by linarith) f
  have b2 : (1 + x)^f * (1 + (-x))^f ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ <;> nlinarith
  have hfx : (f:ℝ) * x ≤ 1/4 := by rw [hx, mul_one_div, div_le_div_iff₀ hQ2 (by norm_num)]; linarith
  have pos : 0 < 1 + (f:ℝ) * (-x) := by linarith
  have b3 : (1+x)^f * (1 + (f:ℝ) * (-x)) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left b1 (by positivity)) b2
  have b4 : 1 ≤ (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x)) := by
    have : (1 + 2*(f:ℝ)/Q) * (1 + (f:ℝ) * (-x)) - 1 = (f:ℝ)*(Q-4-2*f)/(Q*(Q-2)) := by
      rw [hx]; field_simp; ring
    have h2 : 0 ≤ (f:ℝ)*(Q-4-2*f)/(Q*(Q-2)) := by
      apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith
  exact le_of_mul_le_mul_right (le_trans b3 b4) pos

theorem length_average_bound : LemmaB'_avg := by
  intro k n S mult hS hm hn j
  have key : ∀ i : Fin k, ∑ w ∈ S, mult w * w i = ∑ w ∈ S, mult w * w j := by
    intro i
    apply Finset.sum_nbij' (fun w => w ∘ Equiv.swap i j) (fun w => w ∘ Equiv.swap i j)
    · intro w hw; exact hS _ w hw
    · intro w hw; exact hS _ w hw
    · intro w _; funext a; simp [Function.comp]
    · intro w _; funext a; simp [Function.comp]
    · intro w _; simp [hm]
  have : ∑ i : Fin k, ∑ w ∈ S, mult w * w i = k * ∑ w ∈ S, mult w * w j := by
    rw [Finset.sum_congr rfl (fun i _ => key i)]; simp
  rw [← this, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.mul_sum, hn w hw, mul_comm]

theorem commuting_operators : HeckeProductCommutation := by
  intro R _ M _ _ U K c h
  have A : ∀ j p, (K j).comp ((U j) ^ p) = (((c j)⁻¹ ^ p : Rˣ) : R) • ((U (j+1)) ^ p).comp (K j) := by
    intro j p
    induction p with
    | zero => ext; simp
    | succ p ih =>
      have h' : (K j).comp (U j) = (((c j)⁻¹ : Rˣ) : R) • (U (j+1)).comp (K j) := by
        rw [h j, smul_smul]; simp
      calc (K j).comp ((U j) ^ (p+1)) = ((K j).comp ((U j)^p)).comp (U j) := by rw [pow_succ]; rfl
        _ = (((c j)⁻¹ ^ p : Rˣ) : R) • ((U (j+1)) ^ p).comp ((K j).comp (U j)) := by rw [ih]; rfl
        _ = _ := by
          rw [h', LinearMap.comp_smul, smul_smul, pow_succ, pow_succ]; push_cast; rfl
  have B : ∀ m p, (chainK R M K m).comp ((U 0) ^ (m + p)) =
      ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j + p) : Rˣ) : R) • ((U m) ^ p).comp (chainUK R M U K m) := by
    intro m
    induction m with
    | zero => intro p; ext; simp [chainK, chainUK]
    | succ m ih =>
      intro p
      have e0 : m + 1 + p = m + (p + 1) := by ring
      have e1 : ∏ j ∈ range (m+1), (c j)⁻¹ ^ (m + 1 - j + p) =
          (∏ j ∈ range m, (c j)⁻¹ ^ (m - j + (p+1))) * (c m)⁻¹ ^ (p+1) := by
        rw [Finset.prod_range_succ]
        congr 1
        · apply Finset.prod_congr rfl
          intro j hj
          have := Finset.mem_range.mp hj
          congr 1; omega
        · congr 1; omega
      calc (chainK R M K (m+1)).comp ((U 0) ^ (m + 1 + p))
          = (K m).comp ((chainK R M K m).comp ((U 0) ^ (m + (p+1)))) := by rw [e0]; rfl
        _ = ((∏ j ∈ range m, (c j)⁻¹ ^ (m - j + (p+1)) : Rˣ) : R) •
              ((K m).comp ((U m) ^ (p+1))).comp (chainUK R M U K m) := by
            rw [ih (p+1), LinearMap.comp_smul]; rfl
        _ = _ := by
            rw [A m (p+1), e1, LinearMap.smul_comp, smul_smul, pow_succ ((U (m+1)))]; push_cast; rfl
  intro m
  have := B m 0
  simp only [add_zero, pow_zero] at this
  rw [this]; rfl

theorem coset_decomposition : SupportCosetStructure := by
  intro q _ n n' fW f hfW
  obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push_neg at h; exact hfW (funext h)
  have add : ∀ x y : Matrix (Fin n') (Fin n) ℤ, compF fW (x - y) = compF fW x - compF fW y := by
    intro x y; funext j; simp [compF, mul_sub, Finset.sum_sub_distrib]
  let x0 : Matrix (Fin n') (Fin n) ℤ := fun i j => if i = i0 then ((f j / fW i0 : ZMod q).val : ℤ) else 0
  have hx0 : compF fW x0 = f := by
    funext j
    simp only [compF, x0]
    rw [Finset.sum_eq_single i0]
    · simp; field_simp
    · intro i _ hi; simp [hi]
    · simp
  refine ⟨x0, ?_, ?_, ?_⟩
  · intro x; rw [add, hx0, sub_eq_zero]
  · funext j; simp [compF]
  · intro x hx l hl
    have : ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q) := by
      simp only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hx]; exact hl

theorem sum_zero_lattice_spanning : SumZeroLatticeSpanning := by
  intro n
  constructor
  · intro v hv
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Fin.sum_univ_castSucc] at hv
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne']
      linarith
    · simp [Pi.single_apply, Fin.ext_iff, (Fin.is_lt _).ne]
      simp only [← Fin.ext_iff]; simp
  · have : (Matrix.of fun i j : Fin n =>
        ((Pi.single i.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1 : Fin (n + 1) → ℚ) ⬝ᵥ
          (Pi.single j.castSucc (1 : ℚ) - Pi.single (Fin.last n) 1))) =
        1 + Matrix.replicateCol Unit (fun _ => (1:ℚ)) * Matrix.replicateRow Unit (fun _ => (1:ℚ)) := by
      ext i j
      simp [Matrix.one_apply, Matrix.mul_apply, dotProduct_sub, sub_dotProduct, Pi.single_apply, Fin.ext_iff,
        (Fin.is_lt _).ne, (Fin.is_lt _).ne']
      by_cases h : (j:ℕ) = i
      · simp [h]
      · simp [h, Ne.symm h]
    rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct]; ring

theorem length_quotient_power_injective : LengthQuotientPowerInjective := by
  intro R _ M _ _ U hU m
  induction m with
  | zero =>
    have : LinearMap.range ((U:Module.End R M)^0) = ⊤ := by rw [pow_zero]; exact LinearMap.range_id
    rw [this, zero_smul]
    exact Module.length_eq_zero
  | succ m ih =>
    have h1 : LinearMap.range (U^m) ≤ (LinearMap.range (U^(m+1))).comap U := by
      rintro _ ⟨y, rfl⟩; exact ⟨y, by rw [pow_succ']; rfl⟩
    have h2 : LinearMap.range (U^(m+1)) ≤ (LinearMap.range U).comap LinearMap.id := by
      rintro _ ⟨y, rfl⟩; exact ⟨(U^m) y, by rw [pow_succ']; rfl⟩
    have key := Module.length_eq_add_of_exact (Submodule.mapQ _ _ U h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_
    · rw [key, ih, succ_nsmul]
    · rw [injective_iff_map_eq_zero]
      intro a
      induction a using Submodule.Quotient.induction_on with
      | H x =>
        intro hx
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨y, hy⟩ := hx
        rw [Submodule.Quotient.mk_eq_zero]
        refine ⟨y, hU ?_⟩
        rw [← hy, pow_succ']; rfl
    · intro b
      induction b using Submodule.Quotient.induction_on with
      | H x => exact ⟨Submodule.Quotient.mk x, by simp⟩
    · intro b
      induction b using Submodule.Quotient.induction_on with
      | H x =>
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        constructor
        · rintro ⟨y, hy⟩
          exact ⟨Submodule.Quotient.mk y, by rw [Submodule.mapQ_apply]; simp at hy; rw [hy]⟩
        · rintro ⟨a, ha⟩
          induction a using Submodule.Quotient.induction_on with
          | H y =>
            rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at ha
            obtain ⟨z, hz⟩ := ha
            refine ⟨y - (U^m) z, ?_⟩
            have : (U^(m+1)) z = U ((U^m) z) := by rw [pow_succ']; rfl
            simp only [LinearMap.id_coe, id_eq, map_sub]
            rw [← this, hz]; abel

theorem length_quotient_twist_formula : LengthQuotientTwistFormula := by
  intro R _ M _ _ T hT N c
  obtain ⟨V, hV⟩ : ∃ V : Module.End R N, V = T • LinearMap.id := ⟨_, rfl⟩
  have hVinj : Function.Injective V := by
    rw [injective_iff_map_eq_zero]; intro x hx
    apply Subtype.ext; apply hT; have := congrArg Subtype.val hx; simpa [hV] using this
  have hVc : ∀ x : N, ((V^c) x : M) = T^c • (x:M) := by
    intro x
    induction c with
    | zero => simp
    | succ c ih =>
      have hz : ∀ z : N, ((V z : N) : M) = T • (z:M) := by intro z; rw [hV]; simp
      rw [pow_succ', Module.End.mul_apply, hz, ih, pow_succ', mul_smul]
  have it := length_quotient_power_injective R N V hVinj c
  rw [← hV, ← it]
  have h1 : LinearMap.range (V^c) ≤ (N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M))).comap N.subtype := by
    rintro _ ⟨y, rfl⟩; exact ⟨y, y.2, by simp [hVc]⟩
  have h2 : N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M)) ≤ N.comap LinearMap.id := by
    rintro _ ⟨y, hy, rfl⟩; exact N.smul_mem _ hy
  have key := Module.length_eq_add_of_exact (Submodule.mapQ _ _ N.subtype h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_
  · rw [key, add_comm]
  · rw [injective_iff_map_eq_zero]
    intro a
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      intro hx
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [hVc]; simpa using hyx
  · intro b
    induction b using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, by simp⟩
  · intro b
    induction b using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, by rw [Submodule.mapQ_apply]; rfl⟩
      · rintro ⟨a, ha⟩
        induction a using Submodule.Quotient.induction_on with
        | H y =>
          rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at ha
          have := h2 ha
          simp only [Submodule.mem_comap, LinearMap.id_coe, id_eq, Submodule.subtype_apply] at this ⊢
          have h3 := N.sub_mem y.2 this
          simpa using h3

theorem linear_form_integrality_on_support : LinearFormIntegralityOnSupport := by
  intro q _ n n' fW f
  have swap : ∀ (x : Matrix (Fin n') (Fin n) ℤ) (l : Fin n → ℤ),
      ∑ i, fW i * ((x.mulVec l) i : ZMod q) = ∑ j, compF fW x j * (l j : ZMod q) := by
    intro x l
    simp only [compF, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
  constructor
  · intro x hx l hl η hη
    exact hη (x.mulVec l) (by rw [swap, hx]; exact hl)
  · intro hn hfW hf
    obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push Not at h; exact hfW (funext h)
    obtain ⟨j0, hj0⟩ : ∃ j, f j ≠ 0 := by by_contra h; push Not at h; exact hf (funext h)
    obtain ⟨j1, hj1⟩ : ∃ j : Fin n, j ≠ j0 := by
      by_cases h : (j0 : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩
      · exact ⟨⟨0, by omega⟩, by intro h'; rw [← h'] at h; simp at h⟩
    have hq : (q:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    refine ⟨fun i j => if i = i0 ∧ j = j1 then 1 else 0,
      fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0,
      fun i => ((fW i).val : ℚ) / q, ?_, ?_, ?_⟩
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j1), ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hj1.symm, Finset.mem_univ j0⟩)]
      rw [Finset.sum_eq_zero]
      · simp [hj1.symm]; field_simp; ring
      · intro j hj
        simp only [Finset.mem_erase] at hj
        simp [hj.1, hj.2.1]
    · intro μ hμ
      have : ((∑ i, ((fW i).val : ℤ) * μ i : ℤ) : ZMod q) = 0 := by push_cast; simpa using hμ
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      obtain ⟨z, hz⟩ := this
      refine ⟨z, ?_⟩
      have h2 : (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) = (q:ℚ) * z := by exact_mod_cast hz
      have h3 : ∑ i, ((fW i).val : ℚ) / q * (μ i : ℚ) = (∑ i, ((fW i).val : ℚ) * (μ i : ℚ)) / q := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro i _; ring
      rw [h3, h2]; field_simp
    · rintro ⟨z, hz⟩
      have hv : ∀ i, (Matrix.mulVec (fun i j => if i = i0 ∧ j = j1 then (1:ℤ) else 0 : Matrix (Fin n') (Fin n) ℤ)
          (fun j => if j = j1 then 1 else if j = j0 then -((f j1 / f j0 : ZMod q).val : ℤ) else 0)) i = if i = i0 then 1 else 0 := by
        intro i
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single j1]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      simp only [hv] at hz
      rw [Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)] at hz
      simp only [if_true, Int.cast_one, mul_one] at hz
      have h4 : ((fW i0).val : ℚ) = (q:ℚ) * z := by rw [hz]; field_simp
      have h5 : ((fW i0).val : ℤ) = (q:ℤ) * z := by exact_mod_cast h4
      have h6 : ((((fW i0).val : ℤ)) : ZMod q) = 0 := by rw [h5]; simp
      apply hi0; simpa using h6

theorem supportVolumeIndex_statement : SupportVolumeIndex := by
  intro q _ n n'
  have gen : ∀ (A B : Type) [AddCommGroup A] [Module (ZMod q) A] [AddCommGroup B] [Module (ZMod q) B]
      (φ : A →ₗ[ZMod q] B), Function.Surjective φ →
      Nat.card {x : A // φ x = 0} * Nat.card B = Nat.card A := by
    intro A B _ _ _ _ φ hφ
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
    have h2 : Nat.card (A ⧸ LinearMap.ker φ) = Nat.card B :=
      Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv
    have h3 : Nat.card {x : A // φ x = 0} = Nat.card (LinearMap.ker φ) := rfl
    rw [h1, h2, h3]
  have cM : Nat.card (Matrix (Fin n') (Fin n) (ZMod q)) = q ^ (n' * n) := by
    show Nat.card (Fin n' → Fin n → ZMod q) = _
    simp [Nat.card_eq_fintype_card, ZMod.card, ← pow_mul, mul_comm]
  have cV : ∀ k, Nat.card (Fin k → ZMod q) = q ^ k := by
    intro k; simp [Nat.card_eq_fintype_card, ZMod.card]
  constructor
  · intro x0 hx0
    obtain ⟨j0, hj0⟩ : ∃ j, x0 j ≠ 0 := by by_contra h; push Not at h; exact hx0 (funext h)
    let φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n' → ZMod q) :=
      { toFun := fun x => x.mulVec x0, map_add' := fun x y => Matrix.add_mulVec x y x0,
        map_smul' := fun c x => Matrix.smul_mulVec c x x0 }
    have := gen _ _ φ (by
      intro y
      refine ⟨fun i j => if j = j0 then y i / x0 j0 else 0, ?_⟩
      funext i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j0 (by intro j _ hj; simp [hj]) (by simp)]
      simp; field_simp)
    rw [cM, cV] at this
    exact this
  · intro fW hfW
    obtain ⟨i0, hi0⟩ : ∃ i, fW i ≠ 0 := by by_contra h; push Not at h; exact hfW (funext h)
    let φ : Matrix (Fin n') (Fin n) (ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) :=
      { toFun := fun x => Matrix.vecMul fW x, map_add' := fun x y => Matrix.vecMul_add x y fW,
        map_smul' := fun c x => Matrix.vecMul_smul fW c x }
    have := gen _ _ φ (by
      intro y
      refine ⟨fun i j => if i = i0 then y j / fW i0 else 0, ?_⟩
      funext j
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMul, dotProduct]
      rw [Finset.sum_eq_single i0 (by intro i _ hi; simp [hi]) (by simp)]
      simp; field_simp)
    rw [cM, cV] at this
    exact this

theorem weaker_displayed_bound : NonintegralMatrixPreservesThirdOverlattice := by
  unfold NonintegralMatrixPreservesThirdOverlattice
  refine ⟨?_, ?_, ?_⟩
  · intro l c
    refine ⟨fun _ => l 0, c + l 1, ?_⟩
    intro i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    push_cast
    ring
  · intro i
    refine ⟨0, ?_⟩
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro h
    obtain ⟨z, hz⟩ := h 0 1
    simp at hz
    have h3 : (3 : ℚ) * z = 1 := by rw [hz]; norm_num
    have : (3 : ℤ) * z = 1 := by exact_mod_cast h3
    omega

end Formalism.HermitianLattices.LocalLatticeBases
