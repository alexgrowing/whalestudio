import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ThmFD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConsA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ExistsHilbertRepOfPsi
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrS ε + 1 < h) : fdcD ε lam = dimVlam lam := by
  have hgt : ∀ t : ℕ, GapAtLeast ε (lamT lam t) h := fun t a b hab =>
    le_trans (by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]) (gap_lamT hlam.1 hgap t a b hab)
  have hct := isHCParam_lamT hlam
  have hT : ∀ t : ℕ, Nonempty (KType ε (lowK ε (lamT lam t))) := fun t => HW.kType_exists ε _ (hct t)
  let T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)) := fun t => Classical.choice (hT t)
  choose m hm hP using fun t => fdc_model hp hq (hct t) (hgt t) hh (T t)
  have hsg : ∀ t, StdGap ε (lamT lam t) := fun t => fdc_stdGap (hct t) (hgt t) hh
  have hDS : ∀ t, Formalism.MainNotions.S.IsDS ε (lamT lam t) (sigLam ε (PsiM (T t) (m t)) (T t).w) :=
    fun t => isDS_sigLam (hsg t) (hP t) (fdc_w_ne (T t))
  choose j hj1 hj2 hj3 hj4 using fun t => anyF (hDS t) (hsg t) (hP t)
  refine thmFD Lap.Base.b3 hp hq hlam hgap hh (fdcD ε) (fdc_step hp hq hh)
    (fun t => ↥(Hlam ε (PsiM (T t) (m t)) (T t).w)) (fun t => sigLam ε (PsiM (T t) (m t)) (T t).w) T j ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ⟨(hDS t).2.2.1, hj1 t, hj2 t, fun z => ?_⟩
    rw [hj4 t _ (exp_pmat_inUJ z), psiM_exp_pmat, psM_exp_pmat (hm t)]
  · refine Filter.Eventually.of_forall fun t => ?_
    obtain ⟨H', i1, i2, σ', w', hsm, heq⟩ := exists_hilbert_rep_of_psi n ε (lamT lam t) (T t) _ (hsg t) (hP t)
    refine ⟨H', i1, i2, σ', w', hsm, fun z => ?_⟩
    rw [heq _ (exp_pmat_inUJ z), psiM_exp_pmat, psM_exp_pmat (hm t)]
  · refine Filter.Eventually.of_forall fun t => ?_
    obtain ⟨d, hd⟩ := fdcGood_of_isDS (hDS t)
    rw [fdcD_eq (hct t) (hgt t) hh ⟨_, inferInstance, inferInstance, _, hDS t, hd⟩]
    exact hd

theorem fdCons_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrS ε + 1 < h)
    (hΨ : ∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
      ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε lam σ) {v : H} (hv : v ≠ 0) :
    Formalism.MainNotions.S.fdegOf (muCD ε) σ v = dimVlam lam := by
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hσ
  rw [fdegOf_of_isFdeg' hd hv, ← fdcD_eq hlam hgap hh ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩]
  exact fdc_cd hp hq hlam hgap hh

theorem fdCons_muG (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      thrS ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
        ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ) →
      v ≠ 0 → Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  have := muCD_isHaar ε
  have hs := Measure.haarScalarFactor_pos_of_isHaarMeasure (Formalism.REAL.muG ε) (muCD ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (muCD ε)
  have hc : (0 : ℝ) < (Measure.haarScalarFactor (Formalism.REAL.muG ε) (muCD ε) : ℝ) := by exact_mod_cast hs
  obtain ⟨s, hs0, hEq⟩ : ∃ s : ℝ, 0 < s ∧ Formalism.REAL.muG ε = ENNReal.ofReal s • muCD ε :=
    ⟨_, hc, by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩
  refine ⟨1 / s, by positivity, fun lam H _ _ _ σ v hlam hσ h hgap hh hp hq hΨ hv => ?_⟩
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hσ
  have h1 := fdCons_cd hp hq hlam hgap hh hΨ hσ hv
  rw [fdegOf_of_isFdeg' hd hv] at h1
  rw [hEq, fdegOf_of_isFdeg' (isFdeg_smul hs0 hd) hv, h1]
  show dimVlam lam / s = 1 / s * dimVlam lam
  ring

end ReciprocityTheory.ChartRestriction.DS.G2
