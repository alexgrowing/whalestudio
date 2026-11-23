import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ContOnPIterAvgTerm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

namespace Avg

variable {X F : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup F]

theorem integrable_of_continuousOn {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμK : μ Kᶜ = 0) {f : X → F} (hf : ContinuousOn f K) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  exact (integrable_const C).mono' (aesm_of_continuousOn hKm hμK hf) ((ae_mem_of_compl hμK).mono fun k hk => hC k hk)

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smoothVec_rep {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {w : H} (hw : SmoothVec (lieG G) π w) {k : Fin n → Fin n → ℂ}
    (hk : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G) : SmoothVec (lieG G) π (π (Matrix.of k) w) := by
  intro d Xs hXs
  have h := contDiff_avgTerm (p := fun _ => (1 : ℂ)) hG hπ hw hXs hk
  show ContDiff ℝ ∞ fun t => π (oneProd Xs t) (π (Matrix.of k) w)
  have e : (fun t => π (oneProd Xs t) (π (Matrix.of k) w)) = fun t => avgTerm π (fun _ => (1 : ℂ)) w Xs t k := by
    funext t
    show π (oneProd Xs t) (π (Matrix.of k) w) = (1 : ℂ) • π (oneProd Xs t * Matrix.of k) w
    rw [one_smul, hπ.2.1 _ (smooth_oneProd hπ hw Xs hXs t).2 _ hk]
    rfl
  rw [e]
  exact h

end Avg

open Avg in
set_option maxHeartbeats 2000000 in

theorem avgSmooth_of (h4 : SobChart) : AvgSmooth := by
  intro n H _ _ _ G s π hs hπ μ hμ p hp w hw
  have hG := isUnit_det_of_cartan hs
  obtain ⟨hprob, hae, -, -⟩ := hμ
  have hKc := isCompact_Kset hs
  have hKm : MeasurableSet (Kset G s) := (isClosed_Kset G s).measurableSet
  have hμK : μ (Kset G s)ᶜ = 0 := ae_iff.1 hae
  have hKae : ∀ᵐ k ∂μ, k ∈ Kset G s := hae

  have hc0 : ContinuousOn (fun k : Fin n → Fin n → ℂ => p k • π (Matrix.of k) w) (Kset G s) :=
    hp.continuousOn.smul ((hπ.2.2.2 w).comp continuous_id.continuousOn fun k hk => hk.1)
  have hint := integrable_of_continuousOn hKc hKm hμK hc0

  have hmove : ∀ {d : ℕ} (Xs : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ lieG G) → ∀ t : Fin d → ℝ,
      π (oneProd Xs t) (∫ k, p k • π (Matrix.of k) w ∂μ) = ∫ k, avgTerm π p w Xs t k ∂μ := by
    intro d Xs hXs t
    have hO : oneProd Xs t ∈ Formalism.QuantumDeterminants.UH G := (smooth_oneProd hπ hw Xs hXs t).2
    have hc := ((π (oneProd Xs t)).restrictScalars ℝ).integral_comp_comm hint
    calc π (oneProd Xs t) (∫ k, p k • π (Matrix.of k) w ∂μ)
        = ((π (oneProd Xs t)).restrictScalars ℝ) (∫ k, p k • π (Matrix.of k) w ∂μ) := rfl
      _ = ∫ k, ((π (oneProd Xs t)).restrictScalars ℝ) (p k • π (Matrix.of k) w) ∂μ := hc.symm
      _ = ∫ k, avgTerm π p w Xs t k ∂μ := by
        refine integral_congr_ae (hKae.mono fun k hk => ?_)
        show π (oneProd Xs t) (p k • π (Matrix.of k) w) = p k • π (oneProd Xs t * Matrix.of k) w
        rw [map_smul, hπ.2.1 _ hO _ hk.1]
        rfl
  have hparam : ∀ {d : ℕ} (Xs : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Xs i ∈ lieG G) →
      (∀ j : ℕ, iteratedFDeriv ℝ j (fun t => ∫ k, avgTerm π p w Xs t k ∂μ) =
        fun t => ∫ k, pIter (avgTerm π p w Xs) j t k ∂μ) ∧
      ContDiff ℝ ∞ (fun t => ∫ k, avgTerm π p w Xs t k ∂μ) := fun Xs hXs =>
    contDiff_integral_param hKc hKm hμK (fun k hk => contDiff_avgTerm hG hπ hw hXs hk.1)
      (fun j => contOn_pIter_avgTerm h4 hs hπ hw hp hXs j)

  have hv : SmoothVec (lieG G) π (∫ k, p k • π (Matrix.of k) w ∂μ) := by
    intro d Xs hXs
    show ContDiff ℝ ∞ fun t => π (oneProd Xs t) (∫ k, p k • π (Matrix.of k) w ∂μ)
    rw [funext fun t => hmove Xs hXs t]
    exact (hparam Xs hXs).2
  refine ⟨hv, fun l hl => ?_⟩

  obtain ⟨Z, L, hZ, -, hval⟩ := OrbStPf.word_eval (one_mem_UH G) (mul_mem_UH₂ G) hπ.2.1
    (fun Y hY t => expS_mem_UH hY t) l hl (zero_mem_lieG G)
  have hd0 : ∀ v' : H, SmoothVec (lieG G) π v' →
      dL π l v' = OrbStPf.pds L (fun r => π (oneProd Z r) v') 0 := by
    intro v' hv'
    have h := hval v' hv' 0
    simp only [zero_smul, NormedSpace.exp_zero, hπ.1, ContinuousLinearMap.one_apply] at h
    unfold dL
    rw [h]
    rfl
  obtain ⟨hPI, hCD⟩ := hparam Z hZ
  have hsl : ContinuousOn (fun k => pIter (avgTerm π p w Z) L.length 0 k) (Kset G s) :=
    pIter_contOn_slice (contOn_pIter_avgTerm h4 hs hπ hw hp hZ L.length) 0
  have hintP := integrable_of_continuousOn hKc hKm hμK hsl
  have e3 : ∀ k ∈ Kset G s, pIter (avgTerm π p w Z) L.length 0 k (fun i => Pi.single (L.get i) 1) =
      p k • dL π l (π (Matrix.of k) w) := by
    intro k hk
    have hk' : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := hk.1
    have hsm := smoothVec_rep hG hπ hw hk'
    unfold pIter
    rw [← pds_eq_iteratedFDeriv L (contDiff_avgTerm hG hπ hw hZ hk') 0]
    have hfun : (fun t => avgTerm π p w Z t k) =
        fun t => (p k • ContinuousLinearMap.id ℝ H) (π (oneProd Z t) (π (Matrix.of k) w)) := by
      funext t
      show p k • π (oneProd Z t * Matrix.of k) w = p k • π (oneProd Z t) (π (Matrix.of k) w)
      rw [hπ.2.1 _ (smooth_oneProd hπ hw Z hZ t).2 _ hk']
      rfl
    rw [hfun, OrbStPf.pds_clm L (p k • ContinuousLinearMap.id ℝ H)
      (f := fun t => π (oneProd Z t) (π (Matrix.of k) w)) (hsm _ Z hZ), hd0 _ hsm]
    rfl
  have hmain : dL π l (∫ k, p k • π (Matrix.of k) w ∂μ) =
      ∫ k, pIter (avgTerm π p w Z) L.length 0 k (fun i => Pi.single (L.get i) 1) ∂μ := by
    rw [hd0 _ hv]
    have e1 : (fun r => π (oneProd Z r) (∫ k, p k • π (Matrix.of k) w ∂μ)) =
        fun r => ∫ k, avgTerm π p w Z r k ∂μ := funext fun r => hmove Z hZ r
    rw [e1, pds_eq_iteratedFDeriv L hCD 0, hPI L.length]
    exact ContinuousMultilinearMap.integral_apply hintP _
  have hae3 : (fun k => pIter (avgTerm π p w Z) L.length 0 k (fun i => Pi.single (L.get i) 1)) =ᵐ[μ]
      fun k => p k • dL π l (π (Matrix.of k) w) := hKae.mono fun k hk => e3 k hk
  refine ⟨?_, ?_⟩
  · exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin L.length => Fin (l.length + 1) → ℝ) H
      (fun i => Pi.single (L.get i) 1)).integrable_comp hintP).congr hae3
  · rw [hmain]
    exact integral_congr_ae hae3

end Formalism.IndefR.Tow.SobPf

end
