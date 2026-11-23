import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PsWord
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TransferB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMLocal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma tt_adW_neg (ε : Fin n → Bool) (k : KG ε) (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    adW ε k (D.map Neg.neg) = (adW ε k D).map Neg.neg := by
  simp [adW, List.map_map, Function.comp_def, Matrix.mul_neg, Matrix.neg_mul]

lemma tt_rWord_local {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {k₀ : KG ε} (hU : IsOpen U) (hW : IsOpen W)
    (hdiff : ∀ D, DifferentiableOn ℂ (lWord D (psM T μ)) U)
    (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * toMK k₀ ∈ U)
    (hloc : ∀ g ∈ W, inUJ ε g → PsiM T μ g = T.op k₀ * psM T μ (g⁻¹ * toMK k₀))
    (D : List (Matrix (Fin n) (Fin n) ℂ)) :
    ∀ g ∈ W, inUJ ε g →
      rWord ε D (PsiM T μ) g = T.op k₀ * lWord (D.map Neg.neg) (psM T μ) (g⁻¹ * toMK k₀) := by
  induction D with
  | nil => exact hloc
  | cons Z D ih =>
    intro g hg hgu
    have hGd : HasFDerivAt (lWord (D.map Neg.neg) (psM T μ))
        (fderiv ℂ (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀)) (g⁻¹ * toMK k₀) :=
      ((hdiff _).differentiableAt (hU.mem_nhds (hWU g hg).2)).hasFDerivAt
    have hc : HasFDerivAt (fun y => T.op k₀ * lWord (D.map Neg.neg) (psM T μ) y)
        ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).comp
          (fderiv ℂ (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀))) (g⁻¹ * toMK k₀) :=
      (ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).hasFDerivAt.comp _ hGd
    show EcV ε Z (rWord ε D (PsiM T μ)) g =
      T.op k₀ * Lhol (-Z) (lWord (D.map Neg.neg) (psM T μ)) (g⁻¹ * toMK k₀)
    rw [ta_ecV_local ε (F := fun y => T.op k₀ * lWord (D.map Neg.neg) (psM T μ) y) hW hg hgu
      hc.differentiableAt ih Z]
    unfold Lhol
    rw [hc.fderiv]
    rfl

theorem transfer (n : ℕ) : TransferStatement n := by
  intro ε lam T μ _hlam hμ N D v hyp g₀ hg₀
  obtain ⟨U, hU, hpos, hconj, hword⟩ := psM_word n ε (lowK ε lam) T μ
  obtain ⟨W, k₀, hW, hg₀W, hWU, hloc⟩ := psiM_local T μ hμ U hU hpos hg₀
  have hcpt : CompactSpace (KG ε) := compactSpace_KG ε
  set x₀ := g₀⁻¹ * toMK k₀ with hx₀def
  have hx₀ : x₀ ∈ U := (hWU g₀ hg₀W).2
  have hA : ∀ i, rWord ε (D i) (PsiM T μ) g₀ (v i) =
      T.op k₀ (lWord ((D i).map Neg.neg) (psM T μ) x₀ (v i)) := fun i => by
    rw [tt_rWord_local T μ hU hW (fun D => (hword D).1) hWU hloc (D i) g₀ hg₀W hg₀]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hA i, ← map_sum]
  suffices h : ∑ i, lWord ((D i).map Neg.neg) (psM T μ) x₀ (v i) = 0 by rw [h, map_zero]
  have hopc : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hAc : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hopc.mul continuous_const).mul (hopc.comp continuous_inv)
  have hint : ∀ i, Integrable (fun k : KG ε =>
      lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
        (T.op k * projW T * T.op k⁻¹)) (muK ε) := fun i =>
    integrableOn_univ.mp ((((hword _).2.1 x₀ hx₀).smul hAc).continuousOn.integrableOn_compact isCompact_univ)
  have hint' : ∀ i ∈ (univ : Finset (Fin N)), Integrable (fun k : KG ε =>
      lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
        (T.op k * projW T * T.op k⁻¹) (v i)) (muK ε) := fun i _ =>
    integrableOn_univ.mp ((((hword _).2.1 x₀ hx₀).smul (hAc.clm_apply continuous_const)).continuousOn.integrableOn_compact
      isCompact_univ)
  have hterm : ∀ i, lWord ((D i).map Neg.neg) (psM T μ) x₀ (v i) =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
          (T.op k * projW T * T.op k⁻¹) (v i) ∂(muK ε) := by
    intro i
    rw [(hword _).2.2 x₀ hx₀, ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply (hint i)]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.smul_sum, ← integral_finset_sum _ hint']
  have hAv : ∀ (k : KG ε) (u : T.V), (T.op k * projW T * T.op k⁻¹) u = ⟪T.op k T.w, u⟫_ℂ • T.op k T.w := by
    intro k u
    simp only [ContinuousLinearMap.mul_apply, projW, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, map_smul, op_inv_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hzero : ∀ k : KG ε, ∑ i, lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
      (T.op k * projW T * T.op k⁻¹) (v i) = 0 := by
    intro k
    have hy : toMK k⁻¹ * x₀ * toMK k ∈ OmegaSet n := hconj x₀ hx₀ k
    have hyd : IsUnit (toMK k⁻¹ * x₀ * toMK k).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (tb_isUnit_of_omega hy)
    have hinv : (toMK k⁻¹ * x₀ * toMK k)⁻¹⁻¹ = toMK k⁻¹ * x₀ * toMK k :=
      Matrix.nonsing_inv_nonsing_inv _ hyd
    have hz : (toMK k⁻¹ * x₀ * toMK k)⁻¹ ∈ OmegaP n := by
      show (toMK k⁻¹ * x₀ * toMK k)⁻¹⁻¹ ∈ OmegaSet n
      rw [hinv]; exact hy
    have e : ∀ i, hWord (adW ε k (D i)) (PhiP μ) (toMK k⁻¹ * x₀ * toMK k)⁻¹ =
        lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) := fun i => by
      rw [tb_hWord_phiP μ _ _ hz, ← tt_adW_neg, hinv]
    have h := hyp k _ hz
    simp only [e] at h
    calc ∑ i, lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ) (toMK k⁻¹ * x₀ * toMK k) •
          (T.op k * projW T * T.op k⁻¹) (v i)
        = (∑ i, ⟪T.op k T.w, v i⟫_ℂ * lWord (adW ε k ((D i).map Neg.neg)) (PhiM μ)
            (toMK k⁻¹ * x₀ * toMK k)) • T.op k T.w := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hAv, smul_smul, mul_comm]
      _ = 0 := by rw [h, zero_smul]
  simp only [hzero, integral_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
