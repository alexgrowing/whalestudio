import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo.PhkS

theorem exists_nhds_invariant {G : Type*} [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] {Φ : G → ℂ} (hlc : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    ∃ V ∈ nhds (0 : G), ∀ x, ∀ z ∈ V, Φ (x + z) = Φ x := by
  have hloc : ∀ x : G, ∃ W ∈ nhds (0 : G), ∀ h ∈ W, ∀ k ∈ W, Φ (x + (h + k)) = Φ x := by
    intro x
    have ho : IsOpen {h : G | Φ (x + h) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    have hU : {h : G | Φ (x + h) = Φ x} ∈ nhds (0 : G) := ho.mem_nhds (by simp)
    obtain ⟨W, hW, hWW⟩ := exists_nhds_zero_half hU
    exact ⟨W, hW, fun h hh k hk => hWW h hh k hk⟩
  choose W hW hWW using hloc
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover
    (fun x => {y : G | y - x ∈ W x})
    (fun x _ => ((continuous_id.sub continuous_const).continuousAt (x := x)).preimage_mem_nhds
      (by simpa using hW x))
  have hV₀ : (⋂ x ∈ t, W x) ∈ nhds (0 : G) := (Filter.biInter_finset_mem t).2 fun x _ => hW x
  have hval : ∀ y ∈ tsupport Φ, ∀ h ∈ (⋂ x ∈ t, W x), Φ (y + h) = Φ y := by
    intro y hy h hh
    have hc' := ht hy
    simp only [Set.mem_iUnion] at hc'
    obtain ⟨x, hxt, hyx⟩ := hc'
    have hhx : h ∈ W x := Set.mem_iInter₂.1 hh x hxt
    have e1 := hWW x (y - x) hyx 0 (mem_of_mem_nhds (hW x))
    have e2 := hWW x (y - x) hyx h hhx
    rw [add_zero, add_sub_cancel] at e1
    rw [← add_assoc, add_sub_cancel] at e2
    rw [e1, e2]
  have hneg : Neg.neg ⁻¹' (⋂ x ∈ t, W x) ∈ nhds (0 : G) :=
    (continuous_neg.tendsto' (0 : G) 0 neg_zero) hV₀
  refine ⟨(⋂ x ∈ t, W x) ∩ Neg.neg ⁻¹' (⋂ x ∈ t, W x), Filter.inter_mem hV₀ hneg, ?_⟩
  rintro y h ⟨hh, hh'⟩
  by_cases hy : y ∈ tsupport Φ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Φ
  · have := hval (y + h) hyh (-h) hh'
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem rows_add (r z r₂ : Fin 2 → F) : what₂ (r + z) r₂ = what₂ r r₂ + what₂ z 0 := by
  ext i j
  fin_cases i <;> simp [what₂]

theorem continuous_rows_zero : Continuous fun z : Fin 2 → F => what₂ z 0 := by
  refine continuous_matrix fun i j => ?_
  fin_cases i
  · simpa [what₂] using continuous_apply j
  · simpa [what₂] using continuous_const

theorem exists_box_invariant {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} (hΦ : SB2 Φ) :
    ∃ n : ℤ, ∀ z ∈ GodementSectionLocal.box F n, ∀ r r₂ : Fin 2 → F,
      Φ (what₂ (r + z) r₂) = Φ (what₂ r r₂) := by
  obtain ⟨V, hV, hinv⟩ := exists_nhds_invariant hΦ.1 hΦ.2
  have h0 : what₂ (0 : Fin 2 → F) 0 = 0 := by
    ext i j
    fin_cases i <;> simp [what₂]
  have hpre : (fun z : Fin 2 → F => what₂ z 0) ⁻¹' V ∈ nhds (0 : Fin 2 → F) :=
    (continuous_rows_zero.tendsto' (0 : Fin 2 → F) 0 h0) hV
  obtain ⟨n, hn⟩ := GodementSectionLocal.exists_box_subset hpre
  exact ⟨n, fun z hz r r₂ => by rw [rows_add]; exact hinv _ _ (hn hz)⟩

theorem continuous_mx : Continuous (mx : (Fin 2 → F) → ℝ) := by
  unfold mx
  exact ((NNReal.continuous_coe.comp continuous_modulus).comp (continuous_apply 0)).max
    ((NNReal.continuous_coe.comp continuous_modulus).comp (continuous_apply 1))

theorem continuous_row (i : Fin 2) :
    Continuous fun X : Matrix (Fin 2) (Fin 2) F => (fun j => X i j : Fin 2 → F) :=
  continuous_pi fun j => continuous_id.matrix_elem i j

theorem rows_first (r r₂ : Fin 2 → F) : (fun j => what₂ r r₂ 0 j) = r := by
  ext j; simp [what₂]

theorem rows_second (r r₂ : Fin 2 → F) : (fun j => what₂ r r₂ 1 j) = r₂ := by
  ext j; simp [what₂]

theorem div_mem_valBall {c ξ : F} {n : ℤ}
    (h : ((modulus c * (residueCard F : NNReal) ^ n : NNReal) : ℝ) < modulus ξ) :
    ξ ≠ 0 ∧ c / ξ ∈ valBall F n := by
  have h' : modulus c * (residueCard F : NNReal) ^ n < modulus ξ := by exact_mod_cast h
  have hξ : ξ ≠ 0 := by
    rintro rfl
    simp at h'
  refine ⟨hξ, ?_⟩
  by_cases h0 : c = 0
  · simp [h0]
  have hQ : (0 : NNReal) < (residueCard F : NNReal) ^ n :=
    zpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal) _
  have hm := modulus_pos hξ
  have hlt : modulus (c / ξ) < (residueCard F : NNReal) ^ (-n) := by
    rw [div_eq_mul_inv, modulus_mul, modulus_inv, _root_.zpow_neg, ← div_eq_mul_inv,
      div_lt_iff₀ hm, inv_mul_eq_div, lt_div_iff₀ hQ]
    exact h'
  rw [mem_valBall_iff_le_ord (div_ne_zero h0 hξ)]
  rw [modulus_of_ne_zero (div_ne_zero h0 hξ)] at hlt
  have := (zpow_lt_zpow_iff_right₀ one_lt_residueCard_nnreal).1 hlt
  omega

variable [MeasurableSpace F] [BorelSpace F]

instance instLeft (ψ : AddChar F Circle) : (LFS.vol2 ψ).IsAddLeftInvariant := by
  unfold LFS.vol2
  infer_instance

instance instCompacts (ψ : AddChar F Circle) : IsFiniteMeasureOnCompacts (LFS.vol2 ψ) := by
  unfold LFS.vol2
  infer_instance

theorem phk_eq_zero_of_shift {ψ : AddChar F Circle} {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} {t : F}
    {r₂ : Fin 2 → F} (z : Fin 2 → F) (hz : ∀ r, Φ (what₂ (r + z) r₂) = Φ (what₂ r r₂))
    (hne : ψ⁻¹ (z 1 / r₂ 1 - t * (z 0 * r₂ 1 - z 1 * r₂ 0)) ≠ 1) : phk ψ Φ t r₂ = 0 := by
  have ha : ((ψ⁻¹ (z 1 / r₂ 1 - t * (z 0 * r₂ 1 - z 1 * r₂ 0)) : Circle) : ℂ) ≠ 1 :=
    fun h => hne (Circle.coe_eq_one.mp h)
  refine eq_zero_of_eq_mul_of_ne_one ha ?_
  unfold phk
  calc ∫ r₁, Φ (what₂ r₁ r₂) * ((ψ⁻¹ (r₁ 1 / r₂ 1 - t * (r₁ 0 * r₂ 1 - r₁ 1 * r₂ 0)) : Circle) : ℂ)
        ∂LFS.vol2 ψ
      = ∫ r₁, Φ (what₂ (r₁ + z) r₂) *
          ((ψ⁻¹ ((r₁ + z) 1 / r₂ 1 - t * ((r₁ + z) 0 * r₂ 1 - (r₁ + z) 1 * r₂ 0)) : Circle) : ℂ)
          ∂LFS.vol2 ψ :=
        (integral_add_right_eq_self (fun r₁ : Fin 2 → F => Φ (what₂ r₁ r₂) *
          ((ψ⁻¹ (r₁ 1 / r₂ 1 - t * (r₁ 0 * r₂ 1 - r₁ 1 * r₂ 0)) : Circle) : ℂ)) z).symm
    _ = ∫ r₁, ((ψ⁻¹ (z 1 / r₂ 1 - t * (z 0 * r₂ 1 - z 1 * r₂ 0)) : Circle) : ℂ) *
          (Φ (what₂ r₁ r₂) *
            ((ψ⁻¹ (r₁ 1 / r₂ 1 - t * (r₁ 0 * r₂ 1 - r₁ 1 * r₂ 0)) : Circle) : ℂ)) ∂LFS.vol2 ψ := by
        congr 1
        ext r₁
        have e : (r₁ + z) 1 / r₂ 1 - t * ((r₁ + z) 0 * r₂ 1 - (r₁ + z) 1 * r₂ 0) =
            (r₁ 1 / r₂ 1 - t * (r₁ 0 * r₂ 1 - r₁ 1 * r₂ 0)) +
              (z 1 / r₂ 1 - t * (z 0 * r₂ 1 - z 1 * r₂ 0)) := by
          simp only [Pi.add_apply]
          ring
        rw [hz, e, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
    _ = _ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.GJTwo.PhkS

open GlobalTheory.CompanionTheory.GJTwo GlobalTheory.CompanionTheory.GJTwo.PhkS in

theorem GlobalTheory.CompanionTheory.GJTwo.phk_bound_support :
    (ForS fun F _ _ _ _ _ _ ψ => ∀ Φ : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 Φ →
  ∃ A R : ℝ, 0 ≤ A ∧ ∀ r₂ : Fin 2 → F, r₂ 1 ≠ 0 → ∀ t : F, ‖phk ψ Φ t r₂‖ ≤ A ∧
    (phk ψ Φ t r₂ ≠ 0 → (modulus (r₂ 1 * t) : ℝ) ≤ R ∧ (modulus (r₂ 0 * t + (r₂ 1)⁻¹) : ℝ) ≤ R) ∧
    (R < GlobalTheory.CompanionTheory.GJTwo.mx r₂ → phk ψ Φ t r₂ = 0)) := by
  intro F _ _ _ _ _ _ ψ hψ Φ hΦ
  obtain ⟨n, hinv⟩ := exists_box_invariant hΦ
  obtain ⟨C, hC⟩ := hΦ.1.continuous.bounded_above_of_compact_support hΦ.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hK₁ : IsCompact ((fun X : Matrix (Fin 2) (Fin 2) F => (fun j => X 0 j : Fin 2 → F)) '' tsupport Φ) :=
    hΦ.2.isCompact.image (continuous_row 0)
  have hK₂ : IsCompact ((fun X : Matrix (Fin 2) (Fin 2) F => (fun j => X 1 j : Fin 2 → F)) '' tsupport Φ) :=
    hΦ.2.isCompact.image (continuous_row 1)
  obtain ⟨R₀, hR₀⟩ := hK₂.bddAbove_image continuous_mx.continuousOn
  obtain ⟨c, hc⟩ : ∃ c, ψ c ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hψ.2.1 (by ext x; simp [hcon x])
  set K₁ := (fun X : Matrix (Fin 2) (Fin 2) F => (fun j => X 0 j : Fin 2 → F)) '' tsupport Φ with hK₁def
  have hsupp : ∀ r r₂ : Fin 2 → F, Φ (what₂ r r₂) ≠ 0 → r ∈ K₁ ∧ mx r₂ ≤ R₀ := by
    intro r r₂ h
    have hm : what₂ r r₂ ∈ tsupport Φ := subset_tsupport Φ h
    refine ⟨⟨_, hm, rows_first r r₂⟩, hR₀ ⟨r₂, ⟨_, hm, rows_second r r₂⟩, rfl⟩⟩
  set Q : ℝ := ((modulus c * (residueCard F : NNReal) ^ n : NNReal) : ℝ) with hQ
  refine ⟨C * (LFS.vol2 ψ).real K₁, max R₀ Q, mul_nonneg hC0 measureReal_nonneg, ?_⟩
  intro r₂ hv t
  refine ⟨?_, ?_, ?_⟩
  · unfold phk
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K₁)]
    · refine norm_setIntegral_le_of_norm_le_const hK₁.measure_lt_top fun r _ => ?_
      simp only [norm_mul, Circle.norm_coe, mul_one]
      exact hC _
    · intro r hr
      have : Φ (what₂ r r₂) = 0 := by
        by_contra h
        exact hr (hsupp r r₂ h).1
      simp [this]
  · intro hne
    constructor
    · by_contra hlt
      push_neg at hlt
      obtain ⟨hξ, ha⟩ := div_mem_valBall (lt_of_le_of_lt (le_max_right _ _) hlt)
      have hb : (![c / (r₂ 1 * t), 0] : Fin 2 → F) ∈ GodementSectionLocal.box F n := by
        refine GodementSectionLocal.mem_box.2 fun i => ?_
        fin_cases i
        · simpa using ha
        · simp
      refine hne (phk_eq_zero_of_shift _ (fun r => hinv _ hb r r₂) ?_)
      · have e : (![c / (r₂ 1 * t), 0] : Fin 2 → F) 1 / r₂ 1 - t * ((![c / (r₂ 1 * t), 0] : Fin 2 → F) 0 * r₂ 1 -
            (![c / (r₂ 1 * t), 0] : Fin 2 → F) 1 * r₂ 0) = -c := by
          have ht : t ≠ 0 := right_ne_zero_of_mul hξ
          simp
          field_simp
        rw [e, AddChar.inv_apply, neg_neg]
        exact hc
    · by_contra hlt
      push_neg at hlt
      obtain ⟨hξ, ha⟩ := div_mem_valBall (lt_of_le_of_lt (le_max_right _ _) hlt)
      have hb : (![0, -(c / (r₂ 0 * t + (r₂ 1)⁻¹))] : Fin 2 → F) ∈ GodementSectionLocal.box F n := by
        refine GodementSectionLocal.mem_box.2 fun i => ?_
        fin_cases i
        · simp
        · simpa using neg_mem ha
      refine hne (phk_eq_zero_of_shift _ (fun r => hinv _ hb r r₂) ?_)
      · have e : (![0, -(c / (r₂ 0 * t + (r₂ 1)⁻¹))] : Fin 2 → F) 1 / r₂ 1 -
            t * ((![0, -(c / (r₂ 0 * t + (r₂ 1)⁻¹))] : Fin 2 → F) 0 * r₂ 1 -
              (![0, -(c / (r₂ 0 * t + (r₂ 1)⁻¹))] : Fin 2 → F) 1 * r₂ 0) = -c := by
          have e2 : -(c / (r₂ 0 * t + (r₂ 1)⁻¹)) / r₂ 1 -
              t * (0 * r₂ 1 - -(c / (r₂ 0 * t + (r₂ 1)⁻¹)) * r₂ 0) =
              -(c / (r₂ 0 * t + (r₂ 1)⁻¹) * (r₂ 0 * t + (r₂ 1)⁻¹)) := by
            ring
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [e2, div_mul_cancel₀ _ hξ]
        rw [e, AddChar.inv_apply, neg_neg]
        exact hc
  · intro hlt
    unfold phk
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun r => ?_)
    have : Φ (what₂ r r₂) = 0 := by
      by_contra h
      exact absurd (lt_of_le_of_lt (le_max_left _ _) hlt) (not_lt.2 (hsupp r r₂ h).2)
    simp [this]
