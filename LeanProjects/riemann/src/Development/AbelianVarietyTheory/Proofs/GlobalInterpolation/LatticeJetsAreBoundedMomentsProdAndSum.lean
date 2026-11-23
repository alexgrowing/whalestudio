import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureMStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulStatement

noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne

variable {q : ℕ} [Fact q.Prime]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem momInt_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z * G z) := by
  classical
  have cF := (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v F hF).1 mF
  have cG := (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v G hG).1 mG
  refine (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v _ (hF.mul hG)).2 fun n => ?_
  rw [GlobalTheory.T.mahlerJetCoefficient_mul V κ v F G hF hG n, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_one₀ (cF k) (norm_nonneg _) (cG _)

theorem momInt_add (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z + G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mF
  obtain ⟨ν, hν, eν⟩ := mG
  refine ⟨μ + ν, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.add_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using μ.le_of_opNorm_le hμ f
    · simpa using ν.le_of_opNorm_le hν f
  · have h : iteratedFDeriv ℂ k (fun z => F z + G z) 0 =
        iteratedFDeriv ℂ k F 0 + iteratedFDeriv ℂ k G 0 :=
      iteratedFDeriv_add_apply (hF.contDiffAt.of_le (by exact_mod_cast le_top))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h, ContinuousMultilinearMap.add_apply, map_add, eμ k j f hf, eν k j f hf,
      ContinuousLinearMap.add_apply]

theorem momInt_const_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : MomInt ι v G) :
    MomInt ι v (fun z => c * G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mG
  refine ⟨ι c • μ, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.smul_apply, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (μ.le_of_opNorm_le hμ f |>.trans (by simp))
  · have h : iteratedFDeriv ℂ k (fun z => c * G z) 0 = c • iteratedFDeriv ℂ k G 0 := by
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (a := c) (f := G) (i := k) (x := (0 : V))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
      simpa [Pi.smul_def, smul_eq_mul] using this
    rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul, map_mul, eμ k j f hf,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem latInt_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z * G z) :=
  fun κ _ v hv => momInt_mul ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_add (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z + G z) :=
  fun κ _ v hv => momInt_add ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_const_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => c * G z) :=
  fun κ _ v hv => momInt_const_mul ι _ hG hc (mG κ v hv)

theorem latInt_prod_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ω : ℂ_[q]) (Λ : AddSubgroup V),
    (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∏ j, G j z) ∧
    ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) →
      (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  intro q _ ι V _ _ ω Λ
  classical
  refine ⟨fun m _ G hd hl => ?_, fun m s c G hd hc hl => ?_⟩
  · have key : ∀ s : Finset m, ContDiff ℂ ⊤ (fun z => ∏ j ∈ s, G j z) ∧
        LatInt ι ω Λ (fun z => ∏ j ∈ s, G j z) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using ⟨contDiff_const, latInt_one ι ω Λ⟩
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ⟨(hd a).mul ih.1, latInt_mul ι ω Λ (hd a) ih.1 (hl a) ih.2⟩
    exact (key Finset.univ).2
  · have key : ∀ t : Finset m, t ⊆ s → ContDiff ℂ ⊤ (fun z => ∑ j ∈ t, c j * G j z) ∧
        LatInt ι ω Λ (fun z => ∑ j ∈ t, c j * G j z) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        simpa using ⟨contDiff_const, latInt_zero ι ω Λ⟩
      | insert a t ha ih =>
        intro hts
        have hat : a ∈ s := hts (by simp)
        obtain ⟨h1, h2⟩ := ih fun x hx => hts (by simp [hx])
        simp only [Finset.sum_insert ha]
        have h3 : ContDiff ℂ ⊤ (fun z => c a * G a z) := contDiff_const.mul (hd a hat)
        exact ⟨h3.add h1, latInt_add ι ω Λ h3 h1
          (latInt_const_mul ι ω Λ (hd a hat) (hc a hat) (hl a hat)) h2⟩
    exact (key s subset_rfl).2

end GlobalTheory.MomN
