import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem measurePreserving_rearrange (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V')
    (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type)
    [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w))
    [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ) (hb : ∀ i, 0 ≤ b i) (hc : ∀ w, 0 ≤ c w) :
    MeasurePreserving
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v)))
      (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) •
        (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν))
      (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  have hm : Measurable
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) := by
    fun_prop
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq_generateFrom
    (C := fun v => Set.image2 (· ×ˢ ·)
      (Set.pi Set.univ '' Set.pi Set.univ fun i => {s : Set (X i) | MeasurableSet s})
      {s : Set (Y (σ v)) | MeasurableSet s})
    (fun v => (generateFrom_eq_prod generateFrom_pi MeasurableSpace.generateFrom_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)
      isCountablySpanning_measurableSet))
    (fun _ => isPiSystem_pi.prod MeasurableSpace.isPiSystem_measurableSet)
    (fun v => (Measure.FiniteSpanningSetsIn.pi fun i =>
      (ENNReal.ofReal (b i) • m i).toFiniteSpanningSetsIn).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v)).toFiniteSpanningSetsIn) ?_).symm
  intro s hs
  choose t' ht' u hu hst using hs
  choose t ht htt using ht'
  have htm : ∀ v i, MeasurableSet (t v i) := fun v i => ht v i (Set.mem_univ _)
  have hs' : ∀ v, s v = (Set.pi Set.univ (t v)) ×ˢ u v := fun v => by rw [← hst v, htt v]
  have hsm : MeasurableSet (Set.pi Set.univ s) := by
    refine MeasurableSet.univ_pi fun v => ?_
    rw [hs' v]
    exact (MeasurableSet.univ_pi fun i => htm v i).prod (hu v)
  obtain ⟨u', hu'⟩ : ∃ u' : ∀ w, Set (Y w), ∀ v, u' (σ v) = u v :=
    ⟨Equiv.piCongrLeft (fun w => Set (Y w)) σ u, fun v => Equiv.piCongrLeft_apply_apply _ _ _ _⟩
  rw [Measure.map_apply hm hsm]
  have hpre : (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) ⁻¹'
      Set.pi Set.univ s =
      (Set.pi Set.univ fun i => Set.pi Set.univ fun v' => t (β.symm v') i) ×ˢ Set.pi Set.univ u' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hs', Set.mem_prod, forall_and]
    refine and_congr ?_ ?_
    · rw [forall_comm]
      refine forall_congr' fun i => ?_
      rw [← β.forall_congr_right]
      simp only [Equiv.symm_apply_apply]
    · rw [← σ.forall_congr_right]
      simp only [hu']
  rw [hpre, Measure.smul_apply, Measure.prod_prod]
  simp only [hs', Measure.prod_prod, Measure.pi_pi, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h1 : ∏ i, ∏ v', m i (t (β.symm v') i) = ∏ v, ∏ i, m i (t v i) := by
    rw [Finset.prod_comm]
    exact β.symm.prod_comp fun v => ∏ i, m i (t v i)
  have h2 : ∏ w, ν w (u' w) = ∏ v, ν (σ v) (u v) := by
    rw [← σ.prod_comp]
    simp only [hu']
  have h3 : ENNReal.ofReal (∏ w, c w) = ∏ v, ENNReal.ofReal (c (σ v)) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun w _ => hc w, ← σ.prod_comp]
  have h4 : ∏ i, ENNReal.ofReal (b i ^ Fintype.card V) = (∏ i, ENNReal.ofReal (b i)) ^ Fintype.card V := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_pow (hb i) _
  rw [h1, h2, h3, h4]
  ring

end GlobalTheory.LeviIso
