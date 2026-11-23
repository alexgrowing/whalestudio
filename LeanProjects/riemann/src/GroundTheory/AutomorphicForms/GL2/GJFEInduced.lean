import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

variable (β) in

def leviMeasure (ψ : AddChar F Circle) : Measure (levi F n β) :=
  haarLevi β (leviCoordMeasure β ψ)

instance (ψ : AddChar F Circle) : (leviMeasure β ψ).IsHaarMeasure := by
  unfold leviMeasure
  infer_instance

omit [MeasurableSpace F] [BorelSpace F] in

theorem continuous_inducedChar : Continuous (inducedChar (F := F) β) := by
  have h3 : Continuous (leviAbsDetShift (F := F) β) := by
    refine continuous_monoidHom_of_eq_one _
      ⟨leviIntegral F n β, isOpen_leviIntegral (F := F)⟩ fun k hk => ?_
    show leviAbsDet β k ^ (((n : ℝ) - 1) / 2) = 1
    rw [leviAbsDet_of_mem_integralGL (Subgroup.mem_subgroupOf.1 hk), NNReal.one_rpow]
  exact (continuous_leviRatio.mul continuous_leviSqrtModular).mul h3

theorem iwasawa_transfer (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure]
    (μP : Measure (blockUpper F n β)) [μP.IsHaarMeasure] (r : ℕ)
    [Fintype (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))] :
    ∃ C : ℂ, ∀ f : GL (Fin n) F → ℂ, Continuous f →
      (∀ g, ∀ k ∈ congruenceSubgroup F n r, f (g * k) = f g) →
      (∀ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n),
        Integrable (fun p : blockUpper F n β =>
          f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F))) μP) →
      Integrable f μG ∧ ∫ g, f g ∂μG = C * ∑ q : integralGL F n ⧸
        (congruenceSubgroup F n r).subgroupOf (integralGL F n),
          ∫ p, f ((p : GL (Fin n) F) * ((q.out : integralGL F n) : GL (Fin n) F)) ∂μP := by
  classical
  have : BorelSpace (integralGL F n) := Subtype.borelSpace _
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  let μK : Measure (integralGL F n) := Measure.haar
  set κ : ℝ := μP.real (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) * μK.real Set.univ
    with hκ
  set κ' : ℝ := μG.real (integralGL F n) * μK.real ((congruenceSubgroup F n r).subgroupOf
      (integralGL F n) : Set (integralGL F n)) with hκ'
  refine ⟨((κ⁻¹ * κ' : ℝ) : ℂ), fun f hf hr hint => ?_⟩
  have hintP : ∀ y ∈ integralGL F n,
      Integrable (fun p : blockUpper F n β => f ((p : GL (Fin n) F) * y)) μP := by
    intro y hy
    obtain ⟨h, hq⟩ := QuotientGroup.mk_out_eq_mul
      ((congruenceSubgroup F n r).subgroupOf (integralGL F n)) (⟨y, hy⟩ : integralGL F n)
    have heq : ∀ p : blockUpper F n β, f ((p : GL (Fin n) F) * y) =
        f ((p : GL (Fin n) F) * (((QuotientGroup.mk ⟨y, hy⟩ : integralGL F n ⧸
          (congruenceSubgroup F n r).subgroupOf (integralGL F n)).out : integralGL F n) :
            GL (Fin n) F)) := by
      intro p
      rw [hq, Subgroup.coe_mul, ← mul_assoc]
      exact (hr _ _ (Subgroup.mem_subgroupOf.1 h.2)).symm
    simp_rw [heq]
    exact hint _
  have hP0 : μP (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F))) ≠ 0 :=
    ((isOpen_integralGL F n).preimage continuous_subtype_val).measure_ne_zero _
      ⟨1, by simp [one_mem]⟩
  have hK0 : μK Set.univ ≠ 0 := isOpen_univ.measure_ne_zero μK Set.univ_nonempty
  have hintG : Integrable f μG := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    have hC := lintegral_eq_sum_parabolic (β := β) (r := r) μG μP μK hf.enorm.measurable
      (h := fun g => ‖f g‖ₑ) (fun g k hk => by simp only [hr g k hk])
    have hlt : μG (integralGL F n) * (μK ((congruenceSubgroup F n r).subgroupOf
        (integralGL F n)) * ∑ q : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf
          (integralGL F n), ∫⁻ p, ‖f ((p : GL (Fin n) F) *
          ((q.out : integralGL F n) : GL (Fin n) F))‖ₑ ∂μP) < ⊤ :=
      ENNReal.mul_lt_top (isCompact_integralGL F n).measure_lt_top
        (ENNReal.mul_lt_top (measure_lt_top _ _)
          (ENNReal.sum_lt_top.2 fun q _ => (hint q).2))
    rw [hC] at hlt
    exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne (mul_ne_zero hP0 hK0)
  refine ⟨hintG, ?_⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    have hPc : IsCompact (Subtype.val ⁻¹' (integralGL F n : Set (GL (Fin n) F)) :
        Set (blockUpper F n β)) :=
      (Measures.isClosed_blockUpper F n β).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_integralGL F n)
    exact mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hP0, hPc.measure_lt_top.ne⟩)
      (ENNReal.toReal_ne_zero.2 ⟨hK0, measure_ne_top _ _⟩)
  have hC := integral_eq_sum_parabolic (β := β) μG μP μK hintG hr hintP
  rw [Complex.real_smul, Complex.real_smul, Complex.real_smul] at hC
  have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ0
  rw [← hκ, ← mul_assoc, ← Complex.ofReal_mul, ← hκ'] at hC
  push_cast
  field_simp
  linear_combination hC.symm

omit [MeasurableSpace F] [BorelSpace F] in
theorem detPow_inv_mul_of_mem {y : GL (Fin n) F} (hy : y ∈ integralGL F n) (g : GL (Fin n) F)
    (s : ℂ) : detPow (y⁻¹ * g) s = detPow g s := by
  rw [detPow_mul, detPow_of_mem_integralGL ((integralGL F n).inv_mem hy), one_mul]

theorem inducedFE_of_leviFE [mG : MeasurableSpace (GL (Fin n) F)] [hGB : BorelSpace (GL (Fin n) F)]
    (μG : Measure (GL (Fin n) F)) [μG.IsHaarMeasure] {ψ : AddChar F Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ} (hL : LeviFE F σ (inducedChar β) (leviMeasure β ψ) ψ γ) :
    InducedFE F σ μG ψ γ := by
  classical
  obtain rfl : mG = Units.instMeasurableSpace :=
    hGB.measurable_eq.trans (borelSpace_GL (F := F) (n := n)).measurable_eq.symm
  intro Φ hΦ φ hφ ℓ hℓ

  obtain ⟨r₁, hr₁⟩ := hΦ.exists_mul_congruenceSubgroup
  obtain ⟨K', hK'o, hK'⟩ := hφ.2
  obtain ⟨r₂, -, hr₂⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hK'o.mem_nhds K'.one_mem)
  set r := max r₁ r₂ with hrdef
  have hΦr : ∀ X : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := fun X k hk =>
    hr₁ X k (congruenceSubgroup_antitone F n (le_max_left _ _) hk)
  have hφr : ∀ g, ∀ k ∈ congruenceSubgroup F n r, φ (g * k) = φ g := fun g k hk =>
    hK' k (hr₂ (congruenceSubgroup_antitone F n (le_max_right _ _) hk)) g
  have hk₀ : ∀ k ∈ congruenceSubgroup F n r, k ∈ integralGL F n := fun k hk =>
    congruenceSubgroup_le F n r hk
  have : CompactSpace (integralGL F n) :=
    isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have : Finite (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n)) :=
    Subgroup.quotient_finite_of_isOpen _
      ((isOpen_congruenceSubgroup F n r).preimage continuous_subtype_val)
  let _ := Fintype.ofFinite
    (integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n))
  obtain ⟨C, hCf⟩ := iwasawa_transfer (β := β) μG (measureP β ψ) r
  set y : integralGL F n ⧸ (congruenceSubgroup F n r).subgroupOf (integralGL F n) →
    GL (Fin n) F := fun q => ((q.out : integralGL F n) : GL (Fin n) F) with hydef
  have hy : ∀ q, y q ∈ integralGL F n := fun q => (q.out).2

  have hD := fun q => levi_decomp hψ hψ1 hL (hΦ.comp_mulRight (y q)) (φ (y q)) hℓ
  choose sA hsA using fun q => (hD q).1
  choose sB hsB using fun q => (hD q).2.1
  have hRq := fun q => (hD q).2.2
  set s₁ : ℝ := ∑ q, (|sA q| + |sB q|) with hs₁
  have hsA' : ∀ q, sA q ≤ s₁ := fun q =>
    (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun q => |sA q| + |sB q|)
        (fun q _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ q)))
  have hsB' : ∀ q, -s₁ ≤ sB q := fun q => by
    have h1 : |sB q| ≤ s₁ := (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun q => |sA q| + |sB q|)
        (fun q _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ q))
    linarith [neg_abs_le (sB q)]

  have hcontA : ∀ s : ℂ, Continuous fun g : GL (Fin n) F =>
      Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) :=
    fun s => continuous_inducedIntegrand hΦ hφ.2 ℓ _
  have hrA : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n r,
      Φ ((g * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          detPow (g * k) (s + ((n : ℂ) - 1) / 2) * ℓ (φ (g * k)) =
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) := by
    intro s g k hk
    rw [Units.val_mul, hΦr _ k hk, detPow_mul_of_mem_integralGL g (hk₀ k hk), hφr g k hk]
  have hPA : ∀ s : ℂ, s₁ < s.re → ∀ q, Integrable (fun p : blockUpper F n β =>
      Φ (((p : GL (Fin n) F) * y q : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        detPow ((p : GL (Fin n) F) * y q) (s + ((n : ℂ) - 1) / 2) *
          ℓ (φ ((p : GL (Fin n) F) * y q))) (measureP β ψ) := by
    intro s hs q
    refine ⟨((hcontA s).comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable,
      ?_⟩
    show ∫⁻ p, ‖inducedIntegrand Φ φ ℓ (s + ((n : ℂ) - 1) / 2) ((p : GL (Fin n) F) * y q)‖ₑ
      ∂measureP β ψ < ⊤
    rw [lintegral_inducedIntegrand_mul (leviCoordMeasure β ψ) (unipMeasure β ψ) hΦ hφ ℓ _ (hy q)]
    simp_rw [leviIntegrand_shift]
    exact hsA q s (lt_of_le_of_lt (hsA' q) hs)
  have hformA : ∀ s : ℂ, s₁ < s.re →
      Integrable (fun g : GL (Fin n) F =>
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g)) μG ∧
      ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g) ∂μG =
        C * ∑ q, ∫ m, leviIntegrand σ (inducedChar β)
          (fun X => ∫ u, Φ ((X + unipMatrix F u) * (y q : Matrix (Fin n) (Fin n) F))
            ∂unipMeasure β ψ) (φ (y q)) ℓ s m ∂measureM β ψ := by
    intro s hs
    obtain ⟨hint, heq⟩ := hCf _ (hcontA s) (hrA s) (hPA s hs)
    refine ⟨hint, heq.trans ?_⟩
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have := integral_inducedIntegrand_mul (leviCoordMeasure β ψ) (unipMeasure β ψ) hφ ℓ
      (s + ((n : ℂ) - 1) / 2) (hy q) (hPA s hs q)
    simp only [inducedIntegrand] at this
    rw [this]
    simp_rw [leviIntegrand_shift]

  set fB : ℂ → GL (Fin n) F → ℂ := fun s g =>
    localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) *
      detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ g⁻¹) with hfB
  have hΦh : IsSchwartzBruhat (localMatrixFourier ψ Φ) := hΦ.localMatrixFourier hψ hψ1
  have hℓφ : Continuous fun g => ℓ (φ g) := by
    refine IsLocallyConstant.continuous fun S => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    refine ⟨g • (K' : Set (GL (Fin n) F)), ?_, hK'o.smul g, ⟨1, one_mem _, mul_one g⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_preimage, smul_eq_mul, hK' k hk]
    exact hg
  have hcontB : ∀ s : ℂ, Continuous fun g : GL (Fin n) F => fB s g⁻¹ := fun s =>
    ((hΦh.1.continuous.comp (Units.continuous_val.comp continuous_inv)).mul
      ((continuous_detPow _).comp continuous_inv)).mul (hℓφ.comp (continuous_inv.comp continuous_inv))
  have hΦhr : ∀ Z : Matrix (Fin n) (Fin n) F, ∀ k ∈ congruenceSubgroup F n r,
      localMatrixFourier ψ Φ (((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Z) =
        localMatrixFourier ψ Φ Z := by
    intro Z k hk
    rw [← localMatrixFourier_mul_right ψ Φ (hk₀ k hk) Z]
    congr 1
    funext X
    exact hΦr X k hk
  have hrB : ∀ s : ℂ, ∀ g, ∀ k ∈ congruenceSubgroup F n r, fB s (g * k)⁻¹ = fB s g⁻¹ := by
    intro s g k hk
    simp only [hfB, _root_.mul_inv_rev, inv_inv, Units.val_mul]
    rw [hΦhr _ k hk, detPow_inv_mul_of_mem (hk₀ k hk), hφr g k hk]
  have hΞ : ∀ q, IsSchwartzBruhat
      (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F))) := fun q =>
    (hΦ.comp_mulRight (y q)).localMatrixFourier hψ hψ1
  have hBeq : ∀ s : ℂ, ∀ q, ∀ p : blockUpper F n β, fB s ((p : GL (Fin n) F) * y q)⁻¹ =
      parabolicB β (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
        φ ℓ s (y q) p⁻¹ := by
    intro s q p
    simp only [hfB, parabolicB, _root_.mul_inv_rev, inv_inv, Subgroup.coe_inv, Units.val_mul]
    rw [localMatrixFourier_mul_right ψ Φ (hy q), detPow_inv_mul_of_mem (hy q)]
  have hPB : ∀ s : ℂ, s.re < -s₁ → ∀ q, Integrable (fun p : blockUpper F n β =>
      fB s ((p : GL (Fin n) F) * y q)⁻¹) (measureP β ψ) := by
    intro s hs q
    simp_rw [hBeq s q]
    refine ⟨((continuous_parabolicB hφ (hΞ q) ℓ s (y q)).comp
      continuous_inv).aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖parabolicB β (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
      φ ℓ s (y q) p⁻¹‖ₑ ∂measureP β ψ < ⊤
    rw [lintegral_parabolicB_inv ψ hφ (hΞ q) ℓ s (y q)]
    exact hsB q s (lt_of_lt_of_le hs (hsB' q))
  have hinvG : μG.IsInvInvariant := ⟨inv_eq_self_GL F n μG⟩
  have hformB : ∀ s : ℂ, s.re < -s₁ → Integrable (fB s) μG ∧
      ∫ g, fB s g ∂μG = C * ∑ q, ∫ m, leviIntegrandB σ (inducedChar β)
        (fun X => ∫ u, localMatrixFourier ψ (fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
          (X + unipMatrix F u) ∂unipMeasure β ψ) (φ (y q)) ℓ s m ∂measureM β ψ := by
    intro s hs
    obtain ⟨hint, heq⟩ := hCf (fun g => fB s g⁻¹) (hcontB s) (hrB s) (hPB s hs)
    refine ⟨?_, ?_⟩
    · simpa using hint.comp_inv
    · rw [← integral_inv_eq_self (fB s) μG, heq]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      have hint2 : Integrable (fun p => parabolicB β
          (localMatrixFourier ψ fun X => Φ (X * (y q : Matrix (Fin n) (Fin n) F)))
            φ ℓ s (y q) p⁻¹) (measureP β ψ) := by
        have := hPB s hs q
        simp_rw [hBeq s q] at this
        exact this
      refine (integral_congr_ae (Filter.Eventually.of_forall fun p => hBeq s q p)).trans ?_
      exact integral_parabolicB_inv ψ hφ (hΞ q) ℓ s (y q) hint2
  refine ⟨⟨s₁, fun s hs => (hformA s hs).1⟩, ⟨-s₁, fun s hs => (hformB s hs).1⟩, ?_⟩
  have hR := (RatFE.sum Finset.univ fun q _ => hRq q).const_mul C
  exact hR.congr ⟨s₁, fun s hs => (hformA s hs).2⟩ ⟨-s₁, fun s hs => (hformB s hs).2⟩

end GodementJacquet

end GroundTheory.Automorphic
