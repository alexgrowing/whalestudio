import CompanionTheory.AutomorphicTheory.ThetaDilations.IsOpenCoset

open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups

noncomputable section

namespace CompanionTheory.PlacePermOperatorBicommutantSpan

open GlobalTheory.CompanionTheory.SW.Core

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]

theorem bsym {B : Matrix ι ι R} (hB : B.IsSymm) (x y : ι → R) : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hB.eq, dotProduct_comm]

variable [TopologicalSpace R] [MeasurableSpace R] {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)}

theorem impl_one : Impl ψ h B μ 1 id :=
  ⟨fun _ hφ => hφ, fun φ hφ => ⟨φ, hφ, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun x y φ _ => by simp⟩

variable (H : NAQuad ψ h B μ)
include H

theorem sb_heis (x y : ι → R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (Heisenberg₂ ψ h B x y φ) := by
  have hD := H.2.2.2.2.2
  have := hD.1
  have e : Heisenberg₂ ψ h B x y φ =
      ψ (h * (x ⬝ᵥ (B *ᵥ y))) • fun u => (φ ∘ Homeomorph.addRight x) u * chiB ψ B u y := by
    funext u
    simp only [Heisenberg₂, chiB, AddChar.map_add_eq_mul, Pi.smul_apply, smul_eq_mul, Function.comp, Homeomorph.coe_addRight]
    ring
  exact e ▸ sb_smul _ (sb_chi hD (sb_homeo hφ _) y)

theorem sb_opU (b : R) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opU ψ h B b φ) := by
  have hD := H.2.2.2.2.2
  have := hD.1
  have := H.1
  refine sb_mul ((IsLocallyConstant.iff_exists_open _).2 fun u => ?_) hφ
  obtain ⟨L₀, hL₀, -⟩ := co_cpt hD isCompact_empty
  obtain ⟨L, hL, hKL⟩ := co_cpt hD ((hL₀.1.image (continuous_const_smul (b * h))).insert (b • u))
  refine ⟨{y | y - u ∈ L₀ ⊓ perpG hD L}, isOpen_coset u (hL₀.inf (co_perp hD hL).2).2, by simp, fun y hy => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, y = u + l := ⟨y - u, by abel⟩
  simp only [mem_setOf_eq, add_sub_cancel_left] at hy
  have h1 : chiB ψ B (b • u) l = 1 := hy.2 _ (hKL (mem_insert _ _))
  have h2 : chiB ψ B ((b * h) • l) l = 1 := hy.2 _ (hKL (mem_insert_of_mem _ ⟨l, hy.1, rfl⟩))
  have e : b * qf h B (u + l) = b * qf h B u + (b • u) ⬝ᵥ (B *ᵥ l) + ((b * h) • l) ⬝ᵥ (B *ᵥ l) := by
    simp only [qf, mulVec_add, add_dotProduct, dotProduct_add, smul_dotProduct, smul_eq_mul, bsym H.2.2.2.2.1 l u]
    linear_combination (b * (u ⬝ᵥ (B *ᵥ l))) * H.2.1
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  exact (congrArg₂ _ (congrArg _ h1) h2).trans (by simp)

theorem sb_opD (m : ℝ) (a : Rˣ) {φ : (ι → R) → ℂ} (hφ : SB φ) : SB (opD m (a : R) φ) := by
  have := H.1
  exact sb_smul (m : ℂ) (sb_homeo hφ (Homeomorph.smul a))

omit H in
theorem impl_mul {g g' : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g' T') : Impl ψ h B μ (g * g') (T ∘ T') := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hT
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hT'
  refine ⟨fun φ hφ => a1 _ (b1 φ hφ), fun φ hφ => ?_, fun φ φ' hφ hφ' => ?_, fun c φ hφ => ?_, fun φ hφ => ?_,
    fun x y φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, rfl⟩ := a2 φ hφ
    obtain ⟨φ₂, h2, rfl⟩ := b2 φ₁ h1
    exact ⟨φ₂, h2, rfl⟩
  · simp only [Function.comp, b3 φ φ' hφ hφ', a3 _ _ (b1 φ hφ) (b1 φ' hφ')]
  · simp only [Function.comp, b4 c φ hφ, a4 c _ (b1 φ hφ)]
  · exact (a5 _ (b1 φ hφ)).trans (b5 φ hφ)
  · simp only [Function.comp, a6 x y _ (b1 φ hφ), b6 _ _ φ hφ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    congr 3 <;> module

theorem impl_U (b : R) : Impl ψ h B μ (nMat b) (opU ψ h B b) := by
  refine ⟨fun φ hφ => sb_opU H b hφ, fun φ hφ => ⟨_, sb_opU H (-b) hφ, ?_⟩, fun φ φ' _ _ => ?_, fun c φ _ => ?_,
    fun φ _ => ?_, fun x y φ _ => ?_⟩
  · funext u; simp only [opU, ← mul_assoc, ← AddChar.map_add_eq_mul]; simp
  · funext u; simp only [opU, Pi.add_apply, mul_add]
  · funext u; simp only [opU, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [opU, norm_mul, H.2.2.2.1, one_mul]
  · funext u
    simp only [Heisenberg₂, opU, ← mul_assoc, ← AddChar.map_add_eq_mul, nMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, zero_smul, add_zero]
    congr 2
    simp only [qf, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul,
      bsym H.2.2.2.2.1 x u]
    linear_combination (b * (u ⬝ᵥ (B *ᵥ x))) * H.2.1

theorem impl_D (a : Rˣ) {m : ℝ} (hm : 0 < m)
    (hμ : ∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    Impl ψ h B μ (mMat a) (opD m (a : R)) := by
  have := H.1
  have := H.2.2.2.2.2.2.2.2.2.1
  refine ⟨fun φ hφ => sb_opD H m a hφ, fun φ hφ => ⟨_, sb_opD H m⁻¹ a⁻¹ hφ, ?_⟩, fun φ φ' _ _ => ?_, fun c φ _ => ?_,
    fun φ _ => ?_, fun x y φ _ => ?_⟩
  · funext u
    have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    simp [opD, smul_smul, this]
  · funext u; simp only [opD, Pi.add_apply, mul_add]
  · funext u; simp only [opD, Pi.smul_apply, smul_eq_mul]; ring
  · let e : (ι → R) ≃ᵐ (ι → R) := (Homeomorph.smul a).toMeasurableEquiv
    have he : μ = ENNReal.ofReal (m ^ 2) • μ.map e := by
      ext s hs
      rw [Measure.smul_apply, e.map_apply, smul_eq_mul, ← hμ _ (e.measurable hs)]
      exact congrArg μ (e.surjective.image_preimage s).symm
    conv_rhs => rw [he]
    rw [integral_smul_measure, integral_map_equiv, ENNReal.toReal_ofReal (sq_nonneg m), smul_eq_mul,
      ← integral_const_mul]
    simp only [opD, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rfl
  · funext u
    simp only [Heisenberg₂, opD, mMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zero_smul, add_zero, zero_add, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_add,
      smul_eq_mul, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left]
    ring

theorem impl_fou_chiB : Impl ψ h B μ wMat (fou (chiB ψ B) μ) := by
  have hD := H.2.2.2.2.2
  have hh := hD
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  refine ⟨fun φ hφ => (fou_sb hD hφ).1, fun φ hφ => ?_, fun φ φ' hφ hφ' => fou_add hD hφ hφ',
    fun c φ _ => fou_smul c φ, fun φ hφ => planch hD hφ, fun x y φ _ => ?_⟩
  · have h1 := sb_homeo hφ (Homeomorph.neg _)
    exact ⟨_, (fou_sb hD h1).1, funext fun u => by rw [(fou_sb hD h1).2]; simp⟩
  · funext u
    simp only [Heisenberg₂, fou, wMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_smul, zero_smul, add_zero, zero_add, neg_smul, ← integral_const_mul]
    conv_rhs => rw [← integral_add_right_eq_self _ y]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [add_neg_cancel_right, chiB]
    rw [mul_left_comm, mul_right_comm, mul_comm _ (φ v), ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [mulVec_add, add_dotProduct, dotProduct_add, neg_dotProduct, bsym H.2.2.2.2.1 y u, bsym H.2.2.2.2.1 y x]
    linear_combination (x ⬝ᵥ (B *ᵥ y)) * H.2.1

theorem sq_pos_of_ne {φ : (ι → R) → ℂ} (hφ : SB φ) (hne : φ ≠ 0) : ∫ u, ‖φ u‖ ^ 2 ∂μ ≠ 0 := by
  have hh := H.2.2.2.2.2
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  intro h0
  have hc : Continuous fun u => ‖φ u‖ ^ 2 := hφ.1.continuous.norm.pow 2
  have h1 := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) (hc.integrable_of_hasCompactSupport
    (hφ.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)))).1 h0
  have h2 := (hc.ae_eq_iff_eq μ continuous_zero).1 h1
  exact hne (funext fun u => by simpa using congrFun h2 u)

theorem impl_uniq {g : SL(2, R)} {T T' : ((ι → R) → ℂ) → ((ι → R) → ℂ)} (hT : Impl ψ h B μ g T)
    (hT' : Impl ψ h B μ g T') : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, SB φ → T' φ = c • T φ := by
  classical
  have hD := H.2.2.2.2.2
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hT
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hT'
  have inj : ∀ φ φ', SB φ → SB φ' → T φ = T φ' → φ = φ' := fun φ φ' h1 h2 e => by
    have h3 := sb_add h1 (sb_smul (-1) h2)
    by_contra hne
    refine sq_pos_of_ne H h3 (fun h0 => hne (by simpa [← sub_eq_add_neg, sub_eq_zero] using h0)) ?_
    rw [← a5 _ h3, a3 _ _ h1 (sb_smul _ h2), a4 _ _ h2, e]
    simp
  choose! I hI1 hI2 using a2
  have hIT : ∀ φ, SB φ → I (T φ) = φ := fun φ hφ => inj _ _ (hI1 _ (a1 φ hφ)) hφ (hI2 _ (a1 φ hφ))
  have hH : ∀ x y φ, SB φ → T' (I (Heisenberg₂ ψ h B x y φ)) = Heisenberg₂ ψ h B x y (T' (I φ)) := fun x y φ hφ => by
    conv_lhs => rw [← hI2 φ hφ, a6 x y _ (hI1 φ hφ), hIT _ (sb_heis H _ _ (hI1 φ hφ)), ← b6 x y _ (hI1 φ hφ)]
  obtain ⟨c, hc⟩ := schur hD (T := fun φ => T' (I φ))
    (fun φ φ' h1 h2 => by
      conv_lhs => rw [← hI2 φ h1, ← hI2 φ' h2, ← a3 _ _ (hI1 φ h1) (hI1 φ' h2), hIT _ (sb_add (hI1 φ h1) (hI1 φ' h2)),
        b3 _ _ (hI1 φ h1) (hI1 φ' h2)])
    (fun c φ h1 => by
      conv_lhs => rw [← hI2 φ h1, ← a4 _ _ (hI1 φ h1), hIT _ (sb_smul c (hI1 φ h1)), b4 _ _ (hI1 φ h1)])
    (fun y φ h1 => by
      have e : ∀ f : (ι → R) → ℂ, Heisenberg₂ ψ h B 0 y f = fun u => chiB ψ B u y * f u := fun f => by
        funext u; simp [Heisenberg₂, chiB]
      simpa only [e] using hH 0 y φ h1)
    (fun x φ h1 => by
      have e : ∀ f : (ι → R) → ℂ, Heisenberg₂ ψ h B x 0 f = fun u => f (u + x) := fun f => by funext u; simp [Heisenberg₂]
      simpa only [e] using hH x 0 φ h1)
  have hc' : ∀ φ, SB φ → T' φ = c • T φ := fun φ hφ => by rw [← hc _ (a1 φ hφ), hIT φ hφ]
  refine ⟨c, ?_, hc'⟩
  obtain ⟨L, hL, -⟩ := co_cpt hD isCompact_empty
  have := hD.1
  have := hD.2.1
  have hs := sb_ind 0 hL
  have hne := sq_pos_of_ne H hs fun h0 => by simpa [ind_of_mem] using congrFun h0 0
  have h1 := b5 _ hs
  rw [hc' _ hs] at h1
  simp only [Pi.smul_apply, norm_smul, mul_pow, integral_const_mul, a5 _ hs] at h1
  have h2 : ‖c‖ ^ 2 = 1 := mul_right_cancel₀ hne (h1.trans (one_mul _).symm)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 h2

theorem weil_id (b : Rˣ) {m : ℝ} (hm : 0 < m) (hμ : ∀ s : Set (ι → R), MeasurableSet s →
      μ ((fun u => ((b⁻¹ : Rˣ) : R) • u) '' s) = ENNReal.ofReal (m ^ 2) * μ s) :
    ∃ γ : ℂ, ‖γ‖ = 1 ∧ ∀ φ, SB φ → opU ψ h B (b : R) (fou (chiB ψ B) μ φ) =
      γ • fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) (opD m ((b⁻¹ : Rˣ) : R)
        (fou (chiB ψ B) μ (opU ψ h B (-((b⁻¹ : Rˣ) : R)) φ)))) := by
  have h1 := impl_mul (impl_U H b) (impl_fou_chiB H)
  have h2 := impl_mul (impl_fou_chiB H) (impl_mul (impl_U H (-((b⁻¹ : Rˣ) : R))) (impl_mul (impl_D H b⁻¹ hm hμ)
    (impl_mul (impl_fou_chiB H) (impl_U H (-((b⁻¹ : Rˣ) : R))))))
  have e : wMat * (nMat (-((b⁻¹ : Rˣ) : R)) * (mMat b⁻¹ * (wMat * nMat (-((b⁻¹ : Rˣ) : R))))) =
      nMat (b : R) * wMat := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [wMat, nMat, mMat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e] at h2
  exact impl_uniq H h2 h1

theorem orbit_bd (O : Set R) {L : AddSubgroup (ι → R)} (hL : CO L) (hst : ∀ a ∈ O, ∀ x ∈ L, a • x ∈ L)
    {φ : (ι → R) → ℂ} (hφ : SB φ) (hfix : ∀ x ∈ L, ∀ y ∈ L, Heisenberg₂ ψ h B x y φ = φ) :
    ∃ (L' : AddSubgroup (ι → R)) (s : Finset (ι → R)) (C : ℝ), CO L' ∧ ∀ k : SL(2, R), (∀ i j, k i j ∈ O) →
      ∀ T, Impl ψ h B μ k T → (∀ u, ‖T φ u‖ ≤ C) ∧ ∃ c : (ι → R) → ℂ, (∀ a, ‖c a‖ ≤ C) ∧ T φ = ∑ a ∈ s, c a • ind a L' := by
  have hD := H.2.2.2.2.2
  have hh := hD
  obtain ⟨_, _, _, _, _, _, -⟩ := hh
  have hP := co_perp hD hL
  have hL' := hL.inf hP.2
  obtain ⟨s, hs⟩ := sb_span (sb_ind 0 hP) hL'.2 fun x l hl => ind_add x hl.2
  have hpos : 0 < μ.real L := ENNReal.toReal_pos (hL.2.measure_ne_zero μ ⟨0, L.zero_mem⟩) hL.1.measure_lt_top.ne
  refine ⟨_, s, Real.sqrt ((∫ u, ‖φ u‖ ^ 2 ∂μ) / μ.real L), hL', fun k hk T hT => ?_⟩
  have hfT : ∀ x ∈ L, ∀ y ∈ L, Heisenberg₂ ψ h B x y (T φ) = T φ := fun x hx y hy => by
    rw [hT.2.2.2.2.2 x y φ hφ, hfix _ (L.add_mem (hst _ (hk _ _) _ hx) (hst _ (hk _ _) _ hy)) _
      (L.add_mem (hst _ (hk _ _) _ hx) (hst _ (hk _ _) _ hy))]
  have hinv : ∀ u, ∀ l ∈ L, T φ (u + l) = T φ u := fun u l hl => by
    simpa [Heisenberg₂] using congrFun (hfT l hl 0 L.zero_mem) u
  have hsupp : ∀ u, u ∉ perpG hD L → T φ u = 0 := fun u hu => by
    by_contra hne
    refine hu fun y hy => ?_
    have := congrFun (hfT 0 L.zero_mem y hy) u
    simp only [Heisenberg₂, zero_dotProduct, mul_zero, add_zero] at this
    rw [chi_sym hD]
    exact mul_right_cancel₀ hne (this.trans (one_mul _).symm)
  have hTs := hT.1 φ hφ
  have hbd : ∀ u, ‖T φ u‖ ≤ Real.sqrt ((∫ u, ‖φ u‖ ^ 2 ∂μ) / μ.real L) := fun u => by
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hpos, ← hT.2.2.2.2.1 φ hφ, ← integral_add_left_eq_self _ u, mul_comm, ← smul_eq_mul,
      ← integral_indicator_const _ hL.2.measurableSet]
    have hc : Continuous fun v => ‖T φ v‖ ^ 2 := hTs.1.continuous.norm.pow 2
    refine integral_mono_of_nonneg (ae_of_all _ fun v => Set.indicator_nonneg (fun _ _ => sq_nonneg _) v)
      ((hc.integrable_of_hasCompactSupport (hTs.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))).comp_add_left u)
      (ae_of_all _ fun v => ?_)
    by_cases hv : v ∈ L
    · simp only [Set.indicator_of_mem (s := (L : Set (ι → R))) hv, hinv u v hv, le_refl]
    · simp only [Set.indicator_of_notMem (s := (L : Set (ι → R))) hv, sq_nonneg]
  refine ⟨hbd, fun a => ind 0 (perpG hD L) a * T φ a, fun a => ?_, funext fun u => ?_⟩
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hbd a)
    by_cases ha : a - 0 ∈ perpG hD L
    · rw [ind_of_mem ha, norm_one]
    · rw [ind_of_not ha, norm_zero]; exact zero_le_one
  · have e : T φ u = ind 0 (perpG hD L) u * T φ u := by
      by_cases hu : u ∈ perpG hD L
      · rw [ind_of_mem (by simpa using hu), one_mul]
      · rw [hsupp u hu, mul_zero]
    rw [e, congrFun hs u]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : u - a ∈ L ⊓ perpG hD L
    · have := hinv a _ ha.1
      rw [add_sub_cancel] at this
      rw [this]; ring
    · rw [ind_of_not ha]; ring

end CompanionTheory.PlacePermOperatorBicommutantSpan
