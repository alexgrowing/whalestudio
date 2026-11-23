import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.PairAdj

section General

variable {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (μ : Measure Γ) [μ.IsMulRightInvariant] [μ.IsInvInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [IsTopologicalGroup Γ] [T2Space Γ] [SecondCountableTopology Γ] [BorelSpace Γ] [Group Γ] [TopologicalSpace Γ] in

theorem inner_integral_left {μ : Measure Γ} {A : Γ → V} (hA : Integrable A μ) (c : V) :
    ⟪∫ y, A y ∂μ, c⟫_ℂ = ∫ y, ⟪A y, c⟫_ℂ ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hA c, ← integral_conj]
  simp only [inner_conj_symm]

theorem pair_general (K : Γ → V →L[ℂ] V) (F H : Γ → V) (hK : Continuous K) (hF : Continuous F)
    (hH : Continuous H) (cK : HasCompactSupport K) (cF : HasCompactSupport F) (cH : HasCompactSupport H) :
    ∫ x, ⟪∫ y, ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y)) ∂μ, H x⟫_ℂ ∂μ
      = ∫ x, ⟪F x, ∫ y, K y (H (x * y)) ∂μ⟫_ℂ ∂μ := by
  have hadj : Continuous fun y : Γ => ContinuousLinearMap.adjoint (K y⁻¹) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := V)).continuous.comp (hK.comp continuous_inv)

  have i1 : ∀ x, Integrable (fun y => ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y))) μ := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport
      (hadj.clm_apply (hF.comp (continuous_const.mul continuous_id))) ?_
    have c1 : HasCompactSupport fun y => F (x * y) := cF.comp_homeomorph (Homeomorph.mulLeft x)
    refine c1.mono (fun y hy => ?_)
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    exact hy (by rw [h0, map_zero])
  have i2 : ∀ x, Integrable (fun y => K y (H (x * y))) μ := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport
      (hK.clm_apply (hH.comp (continuous_const.mul continuous_id))) ?_
    refine cK.mono (fun y hy => ?_)
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    exact hy (by rw [h0]; simp)

  have jA : Integrable (Function.uncurry fun x y : Γ => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have c1 : Continuous fun p : Γ × Γ => F (p.1 * p.2⁻¹) :=
        hF.comp (continuous_fst.mul continuous_snd.inv)
      have c2 : Continuous fun p : Γ × Γ => K p.2 (H p.1) :=
        (hK.comp continuous_snd).clm_apply (hH.comp continuous_fst)
      exact c1.inner c2
    · refine HasCompactSupport.intro (cH.isCompact.prod cK.isCompact) (fun p hp => ?_)
      have : H p.1 = 0 ∨ K p.2 = 0 := by
        by_contra hc
        push_neg at hc
        exact hp ⟨subset_tsupport _ hc.1, subset_tsupport _ hc.2⟩
      rcases this with h0 | h0 <;> simp [Function.uncurry, h0]
  have jB : Integrable (Function.uncurry fun x y : Γ => ⟪F x, K y (H (x * y))⟫_ℂ) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have c2 : Continuous fun p : Γ × Γ => K p.2 (H (p.1 * p.2)) :=
        (hK.comp continuous_snd).clm_apply (hH.comp (continuous_fst.mul continuous_snd))
      exact (hF.comp continuous_fst).inner c2
    · refine HasCompactSupport.intro (cF.isCompact.prod cK.isCompact) (fun p hp => ?_)
      have : F p.1 = 0 ∨ K p.2 = 0 := by
        by_contra hc
        push_neg at hc
        exact hp ⟨subset_tsupport _ hc.1, subset_tsupport _ hc.2⟩
      rcases this with h0 | h0 <;> simp [Function.uncurry, h0]
  calc ∫ x, ⟪∫ y, ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y)) ∂μ, H x⟫_ℂ ∂μ
      = ∫ x, ∫ y, ⟪F (x * y⁻¹), K y (H x)⟫_ℂ ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [inner_integral_left (i1 x) (H x),
          ← integral_inv_eq_self (fun y => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) μ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [inv_inv]
        exact ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ∫ y, ∫ x, ⟪F (x * y⁻¹), K y (H x)⟫_ℂ ∂μ ∂μ := integral_integral_swap jA
    _ = ∫ y, ∫ x, ⟪F x, K y (H (x * y))⟫_ℂ ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [← integral_mul_right_eq_self (fun x => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) y]
        simp only [mul_inv_cancel_right]
    _ = ∫ x, ∫ y, ⟪F x, K y (H (x * y))⟫_ℂ ∂μ ∂μ := (integral_integral_swap jB).symm
    _ = ∫ x, ⟪F x, ∫ y, K y (H (x * y)) ∂μ⟫_ℂ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact integral_inner (i2 x) (F x)

end General

variable {n : ℕ}

instance instSC : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Mat n)).symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Mat n)).secondCountableTopology

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  change y.val.det ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem pairAdj : LgFacts → Unimod → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f h : Mat n → E.V), KReg k → ContinuousOn f (GLs n) → ContinuousOn h (GLs n) → Cpt f → Cpt h → (haveI := FiniteDimensional.complete ℂ E.V; ∫ x : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f x.val, h x.val⟫_ℂ ∂μ = ∫ x : G n, ⟪f x.val, act μ E k h x.val⟫_ℂ ∂μ) := by
  intro hL hU n _ _ μ _ E k f h hk hf hh cf ch
  haveI := FiniteDimensional.complete ℂ E.V
  haveI : μ.IsMulRightInvariant := (hU n μ).1
  haveI : μ.IsInvInvariant := (hU n μ).2
  have hc : ∀ R, IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1
  haveI : SigmaFinite μ := ⟨⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun _ => trivial,
    fun m => (hc m).measure_lt_top,
    Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (exists_nat_ge (lg y.val))⟩⟩⟩
  have cont : ∀ {W : Type} [TopologicalSpace W] {φ : Mat n → W}, ContinuousOn φ (GLs n) →
      Continuous fun y : G n => φ y.val := fun hφ =>
    hφ.comp_continuous Units.continuous_val val_mem_GLs
  have supp : ∀ {W : Type} [TopologicalSpace W] [Zero W] {φ : Mat n → W},
      (∃ R, ∀ y ∈ GLs n, R < lg y → φ y = 0) → HasCompactSupport fun y : G n => φ y.val := by
    rintro W _ _ φ ⟨R, hR⟩
    exact HasCompactSupport.intro (hc R) fun y hy => hR _ (val_mem_GLs y) (not_le.1 hy)
  have key := pair_general μ (fun y : G n => k y.val) (fun x => f x.val) (fun x => h x.val)
    (cont hk.1) (cont hf) (cont hh) (supp hk.2) (supp cf) (supp ch)
  simp only [Matrix.coe_units_inv, Units.val_mul] at key
  exact key

end GlobalTheory.CompanionTheory.WaveMult.PairAdj
