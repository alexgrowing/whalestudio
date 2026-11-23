import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCoverCycles
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreSectionsCovering
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteCoverPuncturedPolydisc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

noncomputable section

private theorem differentiable_update_pow (e k : ℕ) :
    Differentiable ℂ (fun s : Fin (e + 1) → ℂ => Function.update s 0 (s 0 ^ k)) := by
  rw [differentiable_pi]
  intro i
  by_cases hi : i = 0
  · subst hi
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne hi]
    fun_prop

theorem PuncturedCoverCycles.proof (hCov : FibreSectionsCovering.Statement)
    (hCyc : FiniteCoverPuncturedPolydisc.Statement) : PuncturedCoverCycles.Statement := by
  intro n e N A c r X hr hc0 hXP hfib hsec
  have hX : Set.MapsTo (fun x => A *ᵥ x) X (Metric.ball c r ∩ {t | t 0 ≠ 0}) :=
    fun x hx => hXP x hx
  have hcov := hCov n e N A _ X hX (fun y hy => hfib y hy.1 hy.2) hsec
  have hfib' : ∀ z, (hX.restrict ⁻¹' {z}).encard = N := by
    intro z
    have himg : Subtype.val '' (hX.restrict ⁻¹' {z}) = {x | x ∈ X ∧ A *ᵥ x = z} := by
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact ⟨x'.2, congrArg Subtype.val hx'⟩
      · rintro ⟨hx, hxz⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxz, rfl⟩
    rw [← Subtype.val_injective.encard_image, himg]
    exact hfib z z.2.1 z.2.2
  obtain ⟨m, ord, δ, ψ, hδ0, hδ1, hsum, hord, hcont, hA, hinj, hdisj, hcover⟩ :=
    hCyc e N c r X hX.restrict hr hc0 hcov hfib'
  classical
  let Ψ : Fin m → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun b t =>
    if h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0} then (ψ b ⟨t, h⟩ : Fin n → ℂ) else 0
  have hΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}), Ψ b t = ψ b ⟨t, h⟩ :=
    fun b t h => dif_pos h
  have hAΨ : ∀ b t (h : t ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0}),
      A *ᵥ Ψ b t = Function.update t 0 (t 0 ^ ord b) := by
    intro b t h
    rw [hΨ b t h]
    exact hA b ⟨t, h⟩
  have hopen : IsOpen (Metric.ball c δ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) :=
    Metric.isOpen_ball.inter (isOpen_ne_fun (continuous_apply 0) continuous_const)
  refine ⟨m, ord, Ψ, δ, hδ0, hδ1, hsum, hord, ?_, ?_, ?_, ?_, ?_⟩
  · intro b t ht
    have hcontΨ : ContinuousOn (Ψ b) (Metric.ball c δ ∩ {t | t 0 ≠ 0}) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Metric.ball c δ ∩ {t | t 0 ≠ 0}).domRestrict (Ψ b) = fun s => (ψ b s : Fin n → ℂ) :=
        funext fun s => hΨ b s.1 s.2
      rw [this]
      exact continuous_subtype_val.comp (hcont b)
    obtain ⟨O, V', g, hO, hAO, hV', hxV', hg, -, hAg, hXV'⟩ := hsec _ (ψ b ⟨t, ht⟩).2
    have hqt : Function.update t 0 (t 0 ^ ord b) ∈ O := by
      rw [← hAΨ b t ht, hΨ b t ht]
      exact hAO
    have h1 : ∀ᶠ s in 𝓝 t, s ∈ Metric.ball c δ ∩ {t | t 0 ≠ 0} := hopen.mem_nhds ht
    have h2 : ∀ᶠ s in 𝓝 t, Ψ b s ∈ V' :=
      (hcontΨ.continuousAt (hopen.mem_nhds ht)).preimage_mem_nhds
        (hV'.mem_nhds (by rw [hΨ b t ht]; exact hxV'))
    have heq : Ψ b =ᶠ[𝓝 t] fun s => g (Function.update s 0 (s 0 ^ ord b)) := by
      filter_upwards [h1, h2] with s hs hsV
      have hmem : Ψ b s ∈ X ∩ V' := ⟨by rw [hΨ b s hs]; exact (ψ b ⟨s, hs⟩).2, hsV⟩
      rw [hXV'] at hmem
      obtain ⟨o, ho, hgo⟩ := hmem
      have hAo : A *ᵥ Ψ b s = o := by rw [← hgo, hAg o ho]
      rw [← hgo, ← hAo, hAΨ b s hs]
    have hdiff : DifferentiableAt ℂ (fun s => g (Function.update s 0 (s 0 ^ ord b))) t :=
      (hg.differentiableAt (hO.mem_nhds hqt)).comp t (differentiable_update_pow e (ord b) t)
    exact (heq.differentiableAt_iff.mpr hdiff).differentiableWithinAt
  · intro b t ht
    rw [hΨ b t ht]
    exact ⟨(ψ b ⟨t, ht⟩).2, hA b ⟨t, ht⟩⟩
  · intro b t ht t' ht' h
    rw [hΨ b t ht, hΨ b t' ht'] at h
    exact congrArg Subtype.val (hinj b (Subtype.ext h))
  · intro b b' hbb t ht t' ht' h
    rw [hΨ b t ht, hΨ b' t' ht'] at h
    exact hdisj b b' hbb _ _ (Subtype.ext h)
  · intro x hx hdist
    obtain ⟨b, t, hbt⟩ := hcover ⟨x, hx⟩ hdist
    refine ⟨b, t.1, t.2, ?_⟩
    rw [hΨ b t.1 t.2]
    exact congrArg Subtype.val hbt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
