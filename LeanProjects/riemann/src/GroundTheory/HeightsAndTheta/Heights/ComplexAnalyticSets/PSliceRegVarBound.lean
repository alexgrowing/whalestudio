import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceRegVarBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetLogNormDens
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

noncomputable section

namespace SliceRegVarBound

variable {n d : ℕ}

theorem abs_chartDens_le_mul {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (f : (Fin n → ℂ) → ℝ) (K : ℝ) (hf : ∀ x, |f x| ≤ K)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    |chartDens J A f φ y| ≤ K * chartAbsDens J A (fun _ => 1) φ y := by
  simp only [chartDens, chartAbsDens, sheetSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs
  · rw [abs_mul, one_mul]
    exact mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)
  · simp

end SliceRegVarBound

open SliceRegVarBound FormIntegralPositivity in

theorem SliceRegVarBound.proof (hM : SliceFormMass.Statement) : SliceRegVarBound.Statement := by
  intro n e h W F u' ℓ ε C b₁ b₂ w hW hF hℓ hε hb₁ hb₂ hw hb₁C hb₂C hwI hbw
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb₁C 0)
  set J := W ⊔ Ideal.span {linForm ℓ - 1}
  unfold varInt
  split_ifs with hA
  swap
  · simp
  have hAfin := hA.choose_spec
  unfold chartInt
  set A := hA.choose
  set φ : Fin (e + 1) → (Fin n → ℂ) → ℝ := vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)
  set ψ : Fin (e + 1) → (Fin n → ℂ) → ℝ := fun _ x => Real.log (h.dualNorm x)
  have hfin : ∀ y, (fibre J A y).Finite := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAfin

  have hMφ : Integrable (chartAbsDens J A (fun _ => 1) φ) := by
    have e1 : (fun (k : Fin (e + 1)) x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k *
        Real.log (h.dualNorm x) + (vecCons (fsLogReg h u' ε) fun _ _ => 0 :
          Fin (e + 1) → (Fin n → ℂ) → ℝ) k x) = φ := by
      funext k x
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;> simp [φ]
    rw [← e1]
    refine hM n e h W F ℓ A _ _ _ hW hF hℓ hAfin (fun _ _ _ => rfl) continuousOn_const
      (fun k t x ht => ?_) fun k => ?_
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.fsLogReg_smul h u' ε ht x
      · rfl
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.contDiffOn_fsLogReg h u' hε
      · exact contDiffOn_const
  have hMψ : Integrable (chartAbsDens J A (fun _ => 1) ψ) := by
    have := hM n e h W F ℓ A (fun _ => 1) (fun _ => 1) (fun _ _ => 0) hW hF hℓ hAfin
      (fun _ _ _ => rfl) continuousOn_const (fun _ _ _ _ => rfl) fun _ => contDiffOn_const
    simpa [ψ] using this

  have hint : ∀ (f : (Fin n → ℂ) → ℝ) (K : ℝ) (Φ : Fin (e + 1) → (Fin n → ℂ) → ℝ), Measurable f →
      (∀ x, |f x| ≤ K) → Integrable (chartAbsDens J A (fun _ => 1) Φ) → Integrable (chartDens J A f Φ) :=
    fun f K Φ hfm hfK hΦ => (hΦ.const_mul K).mono'
      (SheetSumMeasurable.measurable_sheetSum hAfin (fun a b => a * b)
        (continuous_fst.mul continuous_snd).measurable hfm Φ).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_chartDens_le_mul hfin f K hfK Φ y)
  have hw1 : ∀ x, |w x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(hwI x).1], (hwI x).2⟩
  have i₁ := hint b₁ C φ hb₁ hb₁C hMφ
  have i₂ := hint b₂ C φ hb₂ hb₂C hMφ
  have iw := hint w 1 φ hw hw1 hMφ
  have iq := hint w 1 ψ hw hw1 hMψ

  have hpt : ∀ y, ‖chartDens J A b₁ φ y - chartDens J A b₂ φ y‖ ≤
      C * (chartDens J A w φ y + 2 * chartDens J A w ψ y) := by
    intro y
    rw [Real.norm_eq_abs]
    simp only [chartDens, sheetSum, finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨hxZ, rfl⟩ := hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := hxZ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      simp [linForm] at this
    split_ifs with hs
    · have hsx := hs.choose_spec
      have hmq := dens_sum_nonneg SheetLogNormDens.proof h u' hε hsx hx0
      have hq : 0 ≤ maDens (fun k => ψ k ∘ hs.choose) (A *ᵥ x) := by
        have hpot : (fun k => ψ k ∘ hs.choose) = fun (_ : Fin (e + 1)) =>
            (fun z => Real.log √(∑ i, ‖(FubiniStudyLogRegularization.regMat h 0 1 *ᵥ z) i‖ ^ 2)) ∘ hs.choose := by
          funext k z
          exact FubiniStudyLogRegularization.log_dualNorm_eq h _
        rw [hpot]
        exact SheetLogNormDens.proof n (e + 1) (n + 1) J A x hs.choose
          (fun _ => FubiniStudyLogRegularization.regMat h 0 1) hsx fun _ =>
            FubiniStudyLogRegularization.regMat_mulVec_ne_zero h 0 one_pos hx0
      set m := maDens (fun k => φ k ∘ hs.choose) (A *ᵥ x)
      set q := maDens (fun k => ψ k ∘ hs.choose) (A *ᵥ x)
      have habs : |m| ≤ m + 2 * q := abs_le.2 ⟨by linarith, by linarith⟩
      have hw0 : 0 ≤ w x := (hwI x).1
      rw [← sub_mul, abs_mul]
      calc |b₁ x - b₂ x| * |m| ≤ (C * w x) * (m + 2 * q) :=
            mul_le_mul (hbw x) habs (abs_nonneg _) (mul_nonneg hC hw0)
        _ = C * (w x * m + 2 * (w x * q)) := by ring
    · simp
  calc |(∫ y, chartDens J A b₁ φ y) - ∫ y, chartDens J A b₂ φ y|
      = ‖∫ y, (chartDens J A b₁ φ y - chartDens J A b₂ φ y)‖ := by
        rw [integral_sub i₁ i₂, Real.norm_eq_abs]
    _ ≤ ∫ y, C * (chartDens J A w φ y + 2 * chartDens J A w ψ y) :=
        norm_integral_le_of_norm_le ((iw.add (iq.const_mul 2)).const_mul C) (Eventually.of_forall hpt)
    _ = C * ((∫ y, chartDens J A w φ y) + 2 * ∫ y, chartDens J A w ψ y) := by
        rw [integral_const_mul, integral_add iw (iq.const_mul 2), integral_const_mul]

end

end GroundTheory.Heights₂.Heights
