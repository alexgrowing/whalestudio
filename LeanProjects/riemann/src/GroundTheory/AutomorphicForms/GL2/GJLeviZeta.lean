import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJLeviZetaConv
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory Polynomial ValuativeRel
open scoped NNReal ENNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (levi F n β)] [BorelSpace (levi F n β)]

def leviIntegrand (σ : Representation ℂ (levi F n β) W) (θ : levi F n β →* ℝ≥0)
    (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (m : levi F n β) : ℂ :=
  Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (θ m : ℂ) * detPow (m : GL (Fin n) F) s *
    ℓ (σ m w)

theorem leviIntegrand_eq (θ : levi F n β →* ℝ≥0) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) :
    leviIntegrand σ θ Ψ w ℓ s m =
      Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * coeffIntegrand σ θ w ℓ s m := by
  simp only [leviIntegrand, coeffIntegrand]
  ring

def BlockSmall (b : Set.range β) (t : ℤ) (X : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, blockOf β i = b → (uniformizer F : F) ^ (-t) * X i j ∈ 𝒪[F]

theorem zeroBlock_blockDiag {b : Set.range β} {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) : ∀ i j, β i ≠ β j → zeroBlock b X i j = 0 := by
  intro i j h
  simp only [zeroBlock]
  split_ifs
  · rfl
  · exact hX i j h

theorem eq_zeroBlock_of_invariant {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) →
      (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) → Ψ (X + Y) = Ψ X)
    {b : Set.range β} {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (hsmall : BlockSmall b r X) : Ψ X = Ψ (zeroBlock b X) := by
  have hsplit : X = zeroBlock b X + (X - zeroBlock b X) := by abel
  conv_lhs => rw [hsplit]
  refine hinv _ _ (zeroBlock_blockDiag hX) (fun i j h => ?_) fun i j => ?_
  · rw [Matrix.sub_apply, hX i j h, zeroBlock_blockDiag hX i j h, sub_zero]
  · refine exists_eq_pow_mul_iff.2 ?_
    rw [Matrix.sub_apply]
    simp only [zeroBlock]
    split_ifs with hi
    · rw [sub_zero]
      exact hsmall i j hi
    · rw [sub_self, mul_zero]
      exact (𝒪[F]).zero_mem

theorem neg_le_blockOrd {b : Set.range β} {m : levi F n β} {A : ℕ}
    (h : ∀ i j, blockOf β i = b →
      (uniformizer F : F) ^ A * ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]) :
    -((blockSize β b : ℤ) * A) ≤ blockOrd F b m := by
  set B := ((leviBlock F m b : GL (Fiber β b) F) : Matrix (Fiber β b) (Fiber β b) F)
  have hB : B.det ≠ 0 := det_ne_zero_of_GL _
  have hmem : ((uniformizer F : F) ^ A • B).det ∈ 𝒪[F] :=
    det_mem_integer_of_fintype fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact h i.1 j.1 i.2
  rw [Matrix.det_smul] at hmem
  have hϖ : ((uniformizer F : F) ^ A) ^ Fintype.card (Fiber β b) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (Cartan.uniformizer_ne_zero F))
  have h0 := ord_nonneg_of_mem (mul_ne_zero hϖ hB) hmem
  rw [LocalField.ord_mul hϖ hB, ← pow_mul, ← zpow_natCast, ord_zpow_uniformizer] at h0
  simp only [blockOrd]
  rw [blockSize]
  push_cast at h0 ⊢
  linarith

theorem IsLeviSchwartz.sub {Ψ₁ Ψ₂ : Matrix (Fin n) (Fin n) F → ℂ} (h₁ : IsLeviSchwartz β Ψ₁)
    (h₂ : IsLeviSchwartz β Ψ₂) : IsLeviSchwartz β (Ψ₁ - Ψ₂) := by
  obtain ⟨r₁, A₁, hi₁, hs₁⟩ := h₁
  obtain ⟨r₂, A₂, hi₂, hs₂⟩ := h₂
  have hweak : ∀ {r r' : ℕ}, r ≤ r' → ∀ y : F, (∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ r' * a) →
      ∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ r * a := by
    rintro r r' hr y ⟨a, ha, rfl⟩
    refine ⟨(uniformizer F : F) ^ (r' - r) * a, Subring.mul_mem _
      (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _) ha, ?_⟩
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hr]
  have hweakA : ∀ {A A' : ℕ}, A ≤ A' → ∀ y : F, (uniformizer F : F) ^ A * y ∈ 𝒪[F] →
      (uniformizer F : F) ^ A' * y ∈ 𝒪[F] := by
    intro A A' hA y hy
    rw [← Nat.add_sub_cancel' hA, pow_add, mul_comm ((uniformizer F : F) ^ A), mul_assoc]
    exact Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _) hy
  refine ⟨max r₁ r₂, max A₁ A₂, fun X Y hX hY hYs => ?_, fun X hX h0 i j => ?_⟩
  · simp only [Pi.sub_apply]
    rw [hi₁ X Y hX hY fun i j => hweak (le_max_left _ _) _ (hYs i j),
      hi₂ X Y hX hY fun i j => hweak (le_max_right _ _) _ (hYs i j)]
  · simp only [Pi.sub_apply] at h0
    by_cases h1 : Ψ₁ X = 0
    · rw [h1, zero_sub, neg_ne_zero] at h0
      exact hweakA (le_max_right _ _) _ (hs₂ X hX h0 i j)
    · exact hweakA (le_max_left _ _) _ (hs₁ X hX h1 i j)

def shiftBlock (b : Set.range β) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) :
    Matrix (Fin n) (Fin n) F → ℂ :=
  fun X => Ψ ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X)

theorem blockUnif_inv_mul_apply (b : Set.range β) (X : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (-blockIndicator b i) * X i j := by
  have : ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (uniformizer F : F) ^ (-blockIndicator b i) := by
    rw [InvMemClass.coe_inv, blockUnif, ← diagPow_neg, Cartan.coe_diagPow]
    rfl
  rw [this, Matrix.diagonal_mul]

theorem blockIndicator_nonneg (b : Set.range β) (i : Fin n) : 0 ≤ blockIndicator b i := by
  simp only [blockIndicator]
  split_ifs <;> norm_num

theorem blockIndicator_le_one (b : Set.range β) (i : Fin n) : blockIndicator b i ≤ 1 := by
  simp only [blockIndicator]
  split_ifs <;> norm_num

theorem IsLeviSchwartz.shiftBlock {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ)
    (b : Set.range β) : IsLeviSchwartz β (shiftBlock b Ψ) := by
  obtain ⟨r, A, hinv, hsupp⟩ := hΨ
  have hϖ := Cartan.uniformizer_ne_zero F
  have hbd : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      ∀ i j, β i ≠ β j → ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X :
        Matrix (Fin n) (Fin n) F) i j = 0 := by
    intro X hX i j h
    rw [blockUnif_inv_mul_apply, hX i j h, mul_zero]
  refine ⟨r + 1, A + 1, fun X Y hX hY hYs => ?_, fun X hX h0 i j => ?_⟩
  · simp only [GodementJacquet.shiftBlock]
    rw [Matrix.mul_add]
    refine hinv _ _ (hbd X hX) (hbd Y hY) fun i j => ?_
    obtain ⟨a, ha, hYa⟩ := hYs i j
    refine ⟨(uniformizer F : F) ^ (1 - blockIndicator b i) * a, Subring.mul_mem _ ?_ ha, ?_⟩
    · have h0 : 0 ≤ 1 - blockIndicator b i := by linarith [blockIndicator_le_one b i]
      rw [← Int.toNat_of_nonneg h0, zpow_natCast]
      exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 _
    · rw [blockUnif_inv_mul_apply, hYa, pow_succ]
      rw [show (uniformizer F : F) ^ (1 - blockIndicator b i) =
        (uniformizer F : F) ^ (1 : ℤ) * (uniformizer F : F) ^ (-blockIndicator b i) by
        rw [← zpow_add₀ hϖ]; ring_nf]
      rw [zpow_one]
      ring
  · have h := hsupp _ (hbd X hX) h0 i j
    rw [blockUnif_inv_mul_apply] at h
    have h1 : 0 ≤ 1 + blockIndicator b i := by linarith [blockIndicator_nonneg b i]
    have : (uniformizer F : F) ^ (1 + blockIndicator b i) *
        ((uniformizer F : F) ^ A * ((uniformizer F : F) ^ (-blockIndicator b i) * X i j)) =
        (uniformizer F : F) ^ (A + 1) * X i j := by
      rw [← mul_assoc, ← mul_assoc, ← zpow_natCast (uniformizer F : F) A, ← zpow_add₀ hϖ,
        ← zpow_add₀ hϖ, ← zpow_natCast]
      congr 2
      push_cast
      ring
    rw [← this]
    refine Subring.mul_mem _ ?_ h
    rw [← Int.toNat_of_nonneg h1, zpow_natCast]
    exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 _

theorem integrable_of_le_indicator {μ : Measure (levi F n β)} {G H : levi F n β → ℂ}
    (hG : Continuous G) {C : ℝ} (hC : 0 ≤ C) {E : Set (levi F n β)}
    (hH : ∫⁻ m, E.indicator (fun m => ‖H m‖ₑ) m ∂μ < ⊤)
    (hle : ∀ m, ‖G m‖ ≤ C * E.indicator (fun m => ‖H m‖) m) : Integrable G μ := by
  refine ⟨hG.aestronglyMeasurable, ?_⟩
  have hpt : ∀ m, ‖G m‖ₑ ≤ ENNReal.ofReal C * E.indicator (fun m => ‖H m‖ₑ) m := by
    intro m
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal (hle m)).trans_eq ?_
    rw [ENNReal.ofReal_mul hC]
    congr 1
    by_cases hm : m ∈ E
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, ofReal_norm]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, ENNReal.ofReal_zero]
  calc ∫⁻ m, ‖G m‖ₑ ∂μ ≤ ∫⁻ m, ENNReal.ofReal C * E.indicator (fun m => ‖H m‖ₑ) m ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal C * ∫⁻ m, E.indicator (fun m => ‖H m‖ₑ) m ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH

theorem continuous_leviIntegrand (hσ : IsSmooth σ) (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ)
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ) (w : W) (ℓ : Module.Dual ℂ W)
    (s : ℂ) : Continuous (leviIntegrand σ θ Ψ w ℓ s) := by
  have : leviIntegrand σ θ Ψ w ℓ s = fun m : levi F n β =>
      Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * coeffIntegrand σ θ w ℓ s m :=
    funext fun m => leviIntegrand_eq θ Ψ w ℓ s m
  rw [this]
  exact hΨ.isLocallyConstant.continuous.mul (continuous_coeffIntegrand hσ θ hθ w ℓ s)

theorem mem_of_isLeviSchwartz {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {A : ℕ}
    (hsupp : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → Ψ X ≠ 0 →
      ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F])
    {m : levi F n β} (hm : Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ 0) :
    m ∈ {m : levi F n β | ∀ b, -((blockSize β b : ℤ) * A) ≤ blockOrd F b m} :=
  fun _ => neg_le_blockOrd fun i j _ => hsupp _ (mem_levi.1 m.2) hm i j

theorem integrable_leviIntegrand (hσ : IsSmooth σ) (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ)
    {μ : Measure (levi F n β)} {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ)
    (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (hconv : ∀ k : Set.range β → ℤ, ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
      (fun m => ‖coeffIntegrand σ θ w ℓ s m‖ₑ) m ∂μ < ⊤) :
    Integrable (leviIntegrand σ θ Ψ w ℓ s) μ := by
  obtain ⟨C, hC⟩ := hΨ.exists_bound
  obtain ⟨r, A, hinv, hsupp⟩ := hΨ
  refine integrable_of_le_indicator (continuous_leviIntegrand hσ θ hθ ⟨r, A, hinv, hsupp⟩ w ℓ s)
    (le_max_right C 0) (hconv fun b => -((blockSize β b : ℤ) * A)) fun m => ?_
  rw [leviIntegrand_eq, norm_mul]
  by_cases h0 : Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 0
  · rw [h0, norm_zero, zero_mul]
    exact mul_nonneg (le_max_right C 0) (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
  · rw [Set.indicator_of_mem (mem_of_isLeviSchwartz hsupp h0)]
    exact mul_le_mul_of_nonneg_right ((hC _ (mem_levi.1 m.2)).trans (le_max_left _ _))
      (norm_nonneg _)

theorem coe_blockUnif_inv_mul (b : Set.range β) (m : levi F n β) :
    (((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) *
      ((((blockUnif F b * m : levi F n β) : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel_left]

theorem integral_shiftBlock (μ : Measure (levi F n β)) [μ.IsMulLeftInvariant]
    {ω : Set.range β → ℂ} (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) (θ : levi F n β →* ℝ≥0)
    (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) (b : Set.range β) :
    ∫ m, leviIntegrand σ θ (shiftBlock b Ψ) w ℓ s m ∂μ =
      ((θ (blockUnif F b) : ℂ) * ω b * qs F s ^ blockSize β b) *
        ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ := by
  rw [← integral_mul_left_eq_self _ (blockUnif F b), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only
  rw [leviIntegrand_eq, leviIntegrand_eq, shiftBlock, coe_blockUnif_inv_mul,
    coeffIntegrand_blockUnif_mul hω]
  ring

theorem eq_shiftBlock_of_small {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) →
      (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) → Ψ (X + Y) = Ψ X)
    {b : Set.range β} {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (hsmall : BlockSmall b ((r : ℤ) + 1) X) : Ψ X = shiftBlock b Ψ X := by
  have hϖ := Cartan.uniformizer_ne_zero F
  have hX' : ∀ i j, β i ≠ β j →
      ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X : Matrix (Fin n) (Fin n) F) i j = 0 :=
    fun i j h => by rw [blockUnif_inv_mul_apply, hX i j h, mul_zero]
  have h1 : BlockSmall b r X := fun i j hi => by
    have := Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 1) (hsmall i j hi)
    rwa [← mul_assoc, pow_one, ← zpow_one_add₀ hϖ, show (1 : ℤ) + -((r : ℤ) + 1) = -(r : ℤ) by ring]
      at this
  have h2 : BlockSmall b r ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X :
      Matrix (Fin n) (Fin n) F) := fun i j hi => by
    rw [blockUnif_inv_mul_apply, ← mul_assoc, ← zpow_add₀ hϖ]
    have hind : blockIndicator b i = 1 := by simp [blockIndicator, hi]
    rw [hind, show -(r : ℤ) + -1 = -((r : ℤ) + 1) by ring]
    exact hsmall i j hi
  have hz : zeroBlock b ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X :
      Matrix (Fin n) (Fin n) F) = zeroBlock b X := by
    ext i j
    simp only [zeroBlock]
    split_ifs with hi
    · rfl
    · rw [blockUnif_inv_mul_apply]
      have hind : blockIndicator b i = 0 := by simp [blockIndicator, hi]
      rw [hind, neg_zero, zpow_zero, one_mul]
  rw [eq_zeroBlock_of_invariant hinv hX h1, shiftBlock, eq_zeroBlock_of_invariant hinv hX' h2, hz]

theorem blockSmall_shift {b b' : Set.range β} (hb : b' ≠ b) {t : ℤ}
    {X : Matrix (Fin n) (Fin n) F} (h : BlockSmall b' t X) :
    BlockSmall b' t ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X :
      Matrix (Fin n) (Fin n) F) := fun i j hi => by
  rw [blockUnif_inv_mul_apply]
  have hind : blockIndicator b i = 0 := by simp [blockIndicator, hi, hb]
  rw [hind, neg_zero, zpow_zero, one_mul]
  exact h i j hi

theorem leviIntegrand_sub (θ : levi F n β →* ℝ≥0) (Ψ₁ Ψ₂ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) :
    leviIntegrand σ θ (Ψ₁ - Ψ₂) w ℓ s =
      leviIntegrand σ θ Ψ₁ w ℓ s - leviIntegrand σ θ Ψ₂ w ℓ s := by
  funext m
  simp only [leviIntegrand, Pi.sub_apply]
  ring

theorem exists_removeBlocks (hσ : IsSmooth σ) (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ)
    (μ : Measure (levi F n β)) [μ.IsHaarMeasure] {ω : Set.range β → ℂ}
    (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) (w : W) (ℓ : Module.Dual ℂ W) {s₀ : ℝ}
    (hconv : ∀ s : ℂ, s₀ < s.re → ∀ k : Set.range β → ℤ,
      ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
        (fun m => ‖coeffIntegrand σ θ w ℓ s m‖ₑ) m ∂μ < ⊤)
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ) (S : Finset (Set.range β)) :
    ∃ Ψ' : Matrix (Fin n) (Fin n) F → ℂ, IsLeviSchwartz β Ψ' ∧
      (∀ b ∈ S, ∃ t : ℤ, ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
        BlockSmall b t X → Ψ' X = 0) ∧
      ∀ s : ℂ, s₀ < s.re → ∫ m, leviIntegrand σ θ Ψ' w ℓ s m ∂μ =
        (∏ b ∈ S, (1 - (θ (blockUnif F b) : ℂ) * ω b * qs F s ^ blockSize β b)) *
          ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨Ψ, hΨ, by simp, fun s _ => by simp⟩
  | insert b S hb ih =>
    obtain ⟨Ψ', hΨ', hvan, hint⟩ := ih
    obtain ⟨r, A, hinv, hsupp⟩ := id hΨ'
    refine ⟨Ψ' - shiftBlock b Ψ', hΨ'.sub (hΨ'.shiftBlock b), fun b' hb' => ?_, fun s hs => ?_⟩
    · rcases Finset.mem_insert.1 hb' with rfl | hb'S
      · exact ⟨(r : ℤ) + 1, fun X hX hsm => by
          rw [Pi.sub_apply, ← eq_shiftBlock_of_small hinv hX hsm, sub_self]⟩
      · obtain ⟨t, ht⟩ := hvan b' hb'S
        have hne : b' ≠ b := fun e => hb (e ▸ hb'S)
        refine ⟨t, fun X hX hsm => ?_⟩
        have hX' : ∀ i j, β i ≠ β j → ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X :
            Matrix (Fin n) (Fin n) F) i j = 0 := fun i j h => by
          rw [blockUnif_inv_mul_apply, hX i j h, mul_zero]
        rw [Pi.sub_apply, ht X hX hsm, shiftBlock, ht _ hX' (blockSmall_shift hne hsm), sub_zero]
    · have hi1 := integrable_leviIntegrand hσ θ hθ hΨ' w ℓ s (hconv s hs)
      have hi2 := integrable_leviIntegrand hσ θ hθ (hΨ'.shiftBlock b) w ℓ s (hconv s hs)
      rw [leviIntegrand_sub]
      simp only [Pi.sub_apply]
      rw [integral_sub hi1 hi2, integral_shiftBlock μ hω, hint s hs, Finset.prod_insert hb]
      ring

theorem isLocallyConstant_comp_of_invariant {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) →
      (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) → Ψ (X + Y) = Ψ X)
    {f : levi F n β → Matrix (Fin n) (Fin n) F} (hbd : ∀ m i j, β i ≠ β j → f m i j = 0)
    (hf : ∀ i j, Continuous fun m => f m i j) : IsLocallyConstant fun m => Ψ (f m) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  refine ⟨⋂ i, ⋂ j, (fun x : levi F n β => f x i j) ⁻¹'
      {x : F | (uniformizer F : F) ^ (-(r : ℤ)) * (x - f m i j) ∈ 𝒪[F]},
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_small r _).preimage (hf i j), ?_, fun x hx => ?_⟩
  · simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq, sub_self, mul_zero]
    exact fun _ _ => (𝒪[F]).zero_mem
  · simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq] at hx
    have hx' : f x = f m + (f x - f m) := by abel
    show Ψ (f x) = Ψ (f m)
    rw [hx']
    refine hinv _ _ (hbd m) (fun i j h => ?_) fun i j => exists_eq_pow_mul_iff.2 (hx i j)
    rw [Matrix.sub_apply, hbd x i j h, hbd m i j h, sub_zero]

theorem continuous_zeroBlock_apply (b : Set.range β) (i j : Fin n) :
    Continuous fun m : levi F n β =>
      zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j := by
  simp only [zeroBlock]
  split_ifs
  · exact continuous_const
  · exact (continuous_entry F n i j).comp continuous_subtype_val

theorem exists_two_of_blockSize {b : Set.range β} (hb : 2 ≤ blockSize β b) :
    ∃ i₀ j₀ : Fin n, blockOf β i₀ = b ∧ β i₀ = β j₀ ∧ i₀ ≠ j₀ := by
  have : 1 < Fintype.card (Fiber β b) := hb
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card this
  refine ⟨x.1, y.1, x.2, ?_, fun e => hxy (Subtype.ext e)⟩
  exact congrArg Subtype.val (x.2.trans y.2.symm)

theorem integral_indicator_eq_zero (hσ : IsSmooth σ) (hc : IsCuspidal σ)
    (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ) (μ : Measure (levi F n β)) [μ.IsHaarMeasure]
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r A : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) →
      (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) → Ψ (X + Y) = Ψ X)
    (hsupp : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → Ψ X ≠ 0 →
      ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F])
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → ‖Ψ X‖ ≤ C)
    (w : W) (ℓ : Module.Dual ℂ W) {N : ℕ}
    (hN : ∀ m : levi F n β, ℓ (σ m w) ≠ 0 → ∀ (b : Set.range β) (t : ℤ),
      (blockSize β b : ℤ) * (t + N) ≤ blockOrd F b m → ∀ i j, blockOf β i = b →
        (uniformizer F : F) ^ (-t) * ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F])
    (s : ℂ) (hconv : ∀ (w' : W) (k : Set.range β → ℤ),
      ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
        (fun m => ‖coeffIntegrand σ θ w' ℓ s m‖ₑ) m ∂μ < ⊤)
    {b : Set.range β} (hb : 2 ≤ blockSize β b) (Pr : (Set.range β → ℤ) → Prop)
    (hPr : ∀ v, Pr v → (blockSize β b : ℤ) * ((r : ℤ) + N) ≤ v b) :
    ∫ m, {m : levi F n β | Pr fun b' => blockOrd F b' m}.indicator
      (leviIntegrand σ θ Ψ w ℓ s) m ∂μ = 0 := by
  classical
  obtain ⟨i₀, j₀, hi₀, hij, hne⟩ := exists_two_of_blockSize hb
  set R : Set (levi F n β) := {m | Pr fun b' => blockOrd F b' m} with hR
  set G : levi F n β → ℂ := fun m => R.indicator (fun m =>
    Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (θ m : ℂ) *
      detPow (m : GL (Fin n) F) s) m with hG
  have hpt : ∀ m, R.indicator (leviIntegrand σ θ Ψ w ℓ s) m = G m * ℓ (σ m w) := by
    intro m
    by_cases hm : m ∈ R
    · rw [Set.indicator_of_mem hm, hG]
      simp only
      rw [Set.indicator_of_mem hm, leviIntegrand]
      by_cases hℓ0 : ℓ (σ m w) = 0
      · rw [hℓ0, mul_zero, mul_zero]
      · rw [eq_zeroBlock_of_invariant hinv (mem_levi.1 m.2)
          (fun i j hi => hN m hℓ0 b r (hPr _ hm) i j hi)]
    · rw [Set.indicator_of_notMem hm, hG]
      simp only
      rw [Set.indicator_of_notMem hm, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]

  have hRu : ∀ m u : levi F n β, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun {i₀}) →
      (m * u ∈ R ↔ m ∈ R) := by
    intro m u hu
    have : (fun b' => blockOrd F b' (m * u)) = fun b' => blockOrd F b' m := by
      funext b'
      rw [blockOrd_mul, blockOrd_of_mem_unipotentRadical b' hu, add_zero]
    simp only [hR, Set.mem_ofPred_eq, this]
  refine integral_eq_zero_of_cuspidal hc μ hij hne ℓ (fun m u hu => ?_) (fun w' => ?_) w
  · simp only [hG]
    by_cases hm : m ∈ R
    · rw [Set.indicator_of_mem ((hRu m u hu).2 hm), Set.indicator_of_mem hm,
        zeroBlock_mul_unipotent hi₀ m hu, map_mul, map_eq_one_of_mem_unipotentRadical θ hθ hu,
        mul_one, Subgroup.coe_mul, detPow_mul, detPow_eq_qs_zpow (u : GL (Fin n) F),
        ordDet_of_mem_unipotentRadical hu, zpow_zero, mul_one]
    · rw [Set.indicator_of_notMem (fun h => hm ((hRu m u hu).1 h)), Set.indicator_of_notMem hm]
  ·
    let k : Set.range β → ℤ := fun b' =>
      if b' = b then (blockSize β b : ℤ) * ((r : ℤ) + N) else -((blockSize β b' : ℤ) * A)
    have hcont : Continuous fun m => G m * ℓ (σ m w') := by
      have hloc : IsLocallyConstant fun m : levi F n β => if m ∈ R then (1 : ℂ) else 0 :=
        (isLocallyConstant_blockOrds (F := F) (β := β)).comp
          (fun v => if Pr v then (1 : ℂ) else 0)
      have heq : (fun m => G m * ℓ (σ m w')) = fun m =>
          (if m ∈ R then (1 : ℂ) else 0) *
            (Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
              coeffIntegrand σ θ w' ℓ s m) := by
        funext m
        simp only [hG, coeffIntegrand, Set.indicator]
        split_ifs <;> ring
      rw [heq]
      exact hloc.continuous.mul ((isLocallyConstant_comp_of_invariant hinv
        (fun m i j h => zeroBlock_blockDiag (mem_levi.1 m.2) i j h)
        (continuous_zeroBlock_apply b)).continuous.mul
          (continuous_coeffIntegrand hσ θ hθ w' ℓ s))
    refine integrable_of_le_indicator hcont hC0 (hconv w' k) fun m => ?_
    simp only [hG]
    by_cases hm : m ∈ R
    · rw [Set.indicator_of_mem hm]
      by_cases h0 : Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = 0
      · rw [h0, zero_mul, zero_mul, zero_mul, norm_zero]
        exact mul_nonneg hC0 (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
      · have hmE : m ∈ {m : levi F n β | ∀ b', k b' ≤ blockOrd F b' m} := by
          intro b'
          by_cases hb' : b' = b
          · subst hb'
            simp only [k, if_pos rfl]
            exact hPr _ hm
          · simp only [k, if_neg hb']
            refine neg_le_blockOrd fun i j hi => ?_
            have := hsupp _ (zeroBlock_blockDiag (mem_levi.1 m.2)) h0 i j
            simpa [zeroBlock, hi, hb'] using this
        rw [Set.indicator_of_mem hmE]
        have : Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (θ m : ℂ) *
            detPow (m : GL (Fin n) F) s * ℓ (σ m w') =
            Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
              coeffIntegrand σ θ w' ℓ s m := by
          simp only [coeffIntegrand]; ring
        rw [this, norm_mul]
        exact mul_le_mul_of_nonneg_right (hC _ (zeroBlock_blockDiag (mem_levi.1 m.2)))
          (norm_nonneg _)
    · rw [Set.indicator_of_notMem hm, zero_mul, norm_zero]
      exact mul_nonneg hC0 (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)

theorem eval_laurent_sum {x : ℂ} (hx : x ≠ 0) {K₀ : ℤ} (hK₀ : K₀ ≤ 0) (S : Finset ℤ)
    (hS : ∀ k ∈ S, K₀ ≤ k) (a : ℤ → ℂ) :
    (∑ k ∈ S, Polynomial.C (a k) * Polynomial.X ^ (k - K₀).toNat).eval x / x ^ (-K₀).toNat =
      ∑ k ∈ S, a k * x ^ k := by
  rw [Polynomial.eval_finsetSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (hS k hk)),
    Int.toNat_of_nonneg (neg_nonneg.2 hK₀), mul_div_assoc, ← zpow_sub₀ hx]
  congr 2
  ring

theorem exists_laurent (hσ : IsSmooth σ) (hc : IsCuspidal σ) (θ : levi F n β →* ℝ≥0)
    (hθ : Continuous θ) (μ : Measure (levi F n β)) [μ.IsHaarMeasure]
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ)
    (hvan : ∀ b, blockSize β b = 1 → ∃ t : ℤ, ∀ X : Matrix (Fin n) (Fin n) F,
      (∀ i j, β i ≠ β j → X i j = 0) → BlockSmall b t X → Ψ X = 0)
    (w : W) {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) {s₀ : ℝ}
    (hconv : ∀ s : ℂ, s₀ < s.re → ∀ (w' : W) (k : Set.range β → ℤ),
      ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
        (fun m => ‖coeffIntegrand σ θ w' ℓ s m‖ₑ) m ∂μ < ⊤) :
    ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
      ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ = P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨Ns, hNs⟩ := exists_block_small hσ hc w hℓ
  obtain ⟨C, hC⟩ := hΨ.exists_bound
  obtain ⟨r, A, hinv, hsupp⟩ := id hΨ
  choose! t ht using hvan
  set T : Set.range β → ℤ := fun b => (blockSize β b : ℤ) * ((r : ℤ) + Ns) with hT
  set nonB1 : Finset (Set.range β) := Finset.univ.filter fun b => blockSize β b ≠ 1 with hnonB1
  let Q : Finset (Set.range β) → Set (levi F n β) := fun S => {m | ∀ b ∈ S, blockOrd F b m < T b}
  have hQm : ∀ S, MeasurableSet (Q S) := fun S =>
    measurableSet_blockOrds (fun v => ∀ b ∈ S, v b < T b)

  have hcut : ∀ s : ℂ, s₀ < s.re → ∀ S : Finset (Set.range β), S ⊆ nonB1 →
      ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ = ∫ m, (Q S).indicator (leviIntegrand σ θ Ψ w ℓ s) m ∂μ := by
    intro s hs S
    have hint := integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w)
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have : Q ∅ = Set.univ := by ext m; simp [Q]
      rw [this, Set.indicator_univ]
    | insert b S hb ih =>
      intro hsub
      rw [ih ((Finset.subset_insert b S).trans hsub)]
      have hb2 : 2 ≤ blockSize β b := by
        have h1 := (Finset.mem_filter.1 (hsub (Finset.mem_insert_self b S))).2
        have h2 := blockSize_pos β b
        omega
      let R : Set (levi F n β) :=
        {m | (fun v : Set.range β → ℤ => (∀ b' ∈ S, v b' < T b') ∧ T b ≤ v b)
          fun b' => blockOrd F b' m}
      have hRm : MeasurableSet R :=
        measurableSet_blockOrds (fun v => (∀ b' ∈ S, v b' < T b') ∧ T b ≤ v b)
      have hpt : (Q S).indicator (leviIntegrand σ θ Ψ w ℓ s) =
          (Q (insert b S)).indicator (leviIntegrand σ θ Ψ w ℓ s) +
            R.indicator (leviIntegrand σ θ Ψ w ℓ s) := by
        funext m
        simp only [Pi.add_apply, Set.indicator, Q, R, Set.mem_ofPred_eq, Finset.mem_insert]
        by_cases h1 : ∀ b' ∈ S, blockOrd F b' m < T b'
        · by_cases h2 : blockOrd F b m < T b
          · have : ∀ b', b' = b ∨ b' ∈ S → blockOrd F b' m < T b' := by
              rintro b' (rfl | h)
              · exact h2
              · exact h1 b' h
            rw [if_pos h1, if_pos this, if_neg (fun h => absurd h.2 (not_le.2 h2)), add_zero]
          · rw [if_pos h1, if_neg (fun h => h2 (h b (Or.inl rfl))), if_pos ⟨h1, not_lt.1 h2⟩,
              zero_add]
        · rw [if_neg h1, if_neg (fun h => h1 fun b' hb' => h b' (Or.inr hb')),
            if_neg (fun h => h1 h.1), add_zero]
      rw [hpt]
      simp only [Pi.add_apply]
      rw [integral_add (hint.indicator (hQm _)) (hint.indicator hRm)]
      have hzero := integral_indicator_eq_zero hσ hc θ hθ μ hinv hsupp (le_max_right C 0)
        (fun X hX => (hC X hX).trans (le_max_left _ _)) w ℓ hNs s (hconv s hs) hb2
        (fun v => (∀ b' ∈ S, v b' < T b') ∧ T b ≤ v b) (fun v hv => hv.2)
      rw [hzero, add_zero]

  set K₀ : ℤ := -∑ b, (blockSize β b : ℤ) * A with hK₀
  set V : Set.range β → ℤ := fun b => max (T b) ((blockSize β b : ℤ) * (t b + Ns)) with hV
  set K₁ : ℤ := ∑ b, (V b - 1) with hK₁
  have hK₀0 : K₀ ≤ 0 := by
    rw [hK₀, neg_nonpos]
    exact Finset.sum_nonneg fun b _ => by positivity
  let e : levi F n β → ℂ := fun m =>
    Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (θ m : ℂ) * ℓ (σ m w)
  let Qk : ℤ → Set (levi F n β) := fun k =>
    {m | (fun v : Set.range β → ℤ => (∀ b ∈ nonB1, v b < T b) ∧ ∑ b, v b = k)
      fun b => blockOrd F b m}
  have hQkm : ∀ k, MeasurableSet (Qk k) := fun k =>
    measurableSet_blockOrds (fun v => (∀ b ∈ nonB1, v b < T b) ∧ ∑ b, v b = k)
  let a : ℤ → ℂ := fun k => ∫ m, (Qk k).indicator e m ∂μ
  refine ⟨(-K₀).toNat, ∑ k ∈ Finset.Icc K₀ K₁, Polynomial.C (a k) *
    Polynomial.X ^ (k - K₀).toNat, fun s hs => ?_⟩
  rw [eval_laurent_sum (qs_ne_zero s) hK₀0 _ (fun k hk => (Finset.mem_Icc.1 hk).1),
    hcut s hs nonB1 le_rfl]
  have hint := integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w)

  have hrange : ∀ m ∈ Q nonB1, leviIntegrand σ θ Ψ w ℓ s m ≠ 0 →
      K₀ ≤ ordDet (m : GL (Fin n) F) ∧ ordDet (m : GL (Fin n) F) ≤ K₁ := by
    intro m hm h0
    have hΨ0 : Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ 0 := fun h => h0 (by
      simp [leviIntegrand, h])
    have hℓ0 : ℓ (σ m w) ≠ 0 := fun h => h0 (by simp [leviIntegrand, h])
    have hlow := mem_of_isLeviSchwartz hsupp hΨ0
    rw [ordDet_eq_sum_blockOrd]
    constructor
    · rw [hK₀, ← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun b _ => hlow b
    · refine Finset.sum_le_sum fun b _ => ?_
      by_cases hb1 : blockSize β b = 1
      · by_contra hcon
        have hge : (blockSize β b : ℤ) * (t b + Ns) ≤ blockOrd F b m := by
          have := le_max_right (T b) ((blockSize β b : ℤ) * (t b + Ns))
          simp only [hV] at hcon
          linarith
        exact hΨ0 (ht b hb1 _ (mem_levi.1 m.2) fun i j hi => hNs m hℓ0 b (t b) hge i j hi)
      · have := hm b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb1⟩)
        have := le_max_left (T b) ((blockSize β b : ℤ) * (t b + Ns))
        simp only [hV]
        linarith

  have hpt : ∀ m, (Q nonB1).indicator (leviIntegrand σ θ Ψ w ℓ s) m =
      ∑ k ∈ Finset.Icc K₀ K₁, qs F s ^ k * (Qk k).indicator e m := by
    intro m
    have hQk : ∀ k, m ∈ Qk k ↔ m ∈ Q nonB1 ∧ ordDet (m : GL (Fin n) F) = k := by
      intro k
      simp only [Qk, Q, Set.mem_ofPred_eq, ordDet_eq_sum_blockOrd]
    have hval : leviIntegrand σ θ Ψ w ℓ s m =
        qs F s ^ ordDet (m : GL (Fin n) F) * e m := by
      simp only [leviIntegrand, e, detPow_eq_qs_zpow]
      ring
    have hterm : ∀ k, qs F s ^ k * (Qk k).indicator e m =
        if k = ordDet (m : GL (Fin n) F) then (Q nonB1).indicator (leviIntegrand σ θ Ψ w ℓ s) m
          else 0 := by
      intro k
      by_cases hk : k = ordDet (m : GL (Fin n) F)
      · rw [if_pos hk]
        by_cases hm : m ∈ Q nonB1
        · rw [Set.indicator_of_mem ((hQk k).2 ⟨hm, hk.symm⟩), Set.indicator_of_mem hm, hval, hk]
        · rw [Set.indicator_of_notMem (fun h => hm ((hQk k).1 h).1), Set.indicator_of_notMem hm,
            mul_zero]
      · rw [if_neg hk, Set.indicator_of_notMem (fun h => hk ((hQk k).1 h).2.symm), mul_zero]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · by_cases hm : m ∈ Q nonB1
      · rw [Set.indicator_of_mem hm]
        by_contra h0
        exact hmem (Finset.mem_Icc.2 (hrange m hm h0))
      · rw [Set.indicator_of_notMem hm]
  have hintk : ∀ k, Integrable ((Qk k).indicator e) μ := by
    intro k
    have heq : (Qk k).indicator e =
        fun m => (qs F s ^ k)⁻¹ * (Qk k).indicator (leviIntegrand σ θ Ψ w ℓ s) m := by
      funext m
      by_cases hm : m ∈ Qk k
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
        have hk : ordDet (m : GL (Fin n) F) = k := by
          have := hm.2
          rw [ordDet_eq_sum_blockOrd]
          exact this
        simp only [leviIntegrand, e, detPow_eq_qs_zpow, hk]
        field_simp [zpow_ne_zero k (qs_ne_zero s)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, mul_zero]
    rw [heq]
    exact (hint.indicator (hQkm k)).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ fun k _ => (hintk k).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, mul_comm]

theorem exists_leviZeta (hσ : IsSmooth σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧
      ∀ Ψ : Matrix (Fin n) (Fin n) F → ℂ, IsLeviSchwartz β Ψ → ∀ w : W,
        ∀ ℓ ∈ smoothVectors (Representation.dual σ),
          (∀ s : ℂ, s₀ < s.re → Integrable (leviIntegrand σ θ Ψ w ℓ s) μM) ∧
          ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
            D.eval (qs F s) * ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μM =
              P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨ω, hω⟩ := exists_blockChar (F := F) hσ
  obtain ⟨s₀, -, hconv⟩ := exists_lintegral_lt_top hσ hc θ hθ μM
  set B1 : Finset (Set.range β) := Finset.univ.filter fun b => blockSize β b = 1 with hB1
  refine ⟨s₀, ∏ b ∈ B1, (1 - Polynomial.C ((θ (blockUnif F b) : ℂ) * ω b) * Polynomial.X),
    ?_, fun Ψ hΨ w ℓ hℓ => ⟨fun s hs =>
      integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w ℓ hℓ), ?_⟩⟩
  · rw [Polynomial.eval_prod]
    exact Finset.prod_eq_one fun b _ => by simp
  · obtain ⟨Ψ', hΨ', hvan, hint⟩ := exists_removeBlocks hσ θ hθ μM hω w ℓ
      (fun s hs k => hconv s hs w ℓ hℓ k) hΨ B1
    obtain ⟨N, P, hNP⟩ := exists_laurent hσ hc θ hθ μM hΨ'
      (fun b hb => hvan b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) w hℓ
      (fun s hs w' k => hconv s hs w' ℓ hℓ k)
    refine ⟨N, P, fun s hs => ?_⟩
    rw [← hNP s hs, hint s hs, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [(Finset.mem_filter.1 hb).2, pow_one]
    simp

end GodementJacquet

end GroundTheory.Automorphic
