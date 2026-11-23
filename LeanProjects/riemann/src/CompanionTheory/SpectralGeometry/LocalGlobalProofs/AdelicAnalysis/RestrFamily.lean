import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExistsStatement
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreGlue

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Local

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y}

lemma ae_g_eq (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) {U : Set V} {m : Measure V}
    {b : X} (h : m (f ⁻¹' {ι b} ∩ U)ᶜ = 0) : ∀ᵐ v ∂m, g v = b := by
  have h' : ∀ᵐ v ∂m, v ∈ f ⁻¹' {ι b} ∩ U := by
    rw [ae_iff]; exact h
  refine h'.mono fun v hv => ?_
  apply hι
  rw [← hf v]
  exact hv.1

lemma piece (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {s D : Set X} (hD : MeasurableSet D) (hDs : D ⊆ s) {F : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' s) ν s F) {φ : V → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ b in D, ∫⁻ v, φ v ∂(F b) ∂ν := by
  have hm : MeasurableSet (g ⁻¹' D) := hg.measurable hD
  have e1 : ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ v in g ⁻¹' s, (g ⁻¹' D).indicator φ v ∂μ := by
    rw [setLIntegral_indicator hm, Set.inter_eq_left.2 (Set.preimage_mono hDs)]
  rw [e1, h.2.1 _ (hφ.indicator hm), ← lintegral_indicator hD]
  refine lintegral_congr fun b => ?_
  have hae := ae_g_eq hι hf (h.1 b)
  by_cases hb : b ∈ D
  · rw [Set.indicator_of_mem hb]
    refine lintegral_congr_ae (hae.mono fun v hv => ?_)
    have : v ∈ g ⁻¹' D := by
      show g v ∈ D
      rw [hv]; exact hb
    simp only [Set.indicator_of_mem this]
  · rw [Set.indicator_of_notMem hb]
    have e : ∫⁻ v, (g ⁻¹' D).indicator φ v ∂(F b) = ∫⁻ _, 0 ∂(F b) := by
      refine lintegral_congr_ae (hae.mono fun v hv => ?_)
      have : v ∉ g ⁻¹' D := by
        show g v ∉ D
        rw [hv]; exact hb
      simp only [Set.indicator_of_notMem this]
    simpa using e

open Classical in

noncomputable def restr (B : Set X) (fam : X → Measure V) : X → Measure V :=
  fun b => if b ∈ B then fam b else 0

lemma restr_family (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {B B₂ : Set X} (hB₂ : IsOpen B₂) (hsub : B₂ ⊆ B) {fam : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' B) ν B fam) :
    IsFibreFamily μ f ι (g ⁻¹' B₂) ν B₂ (restr B₂ fam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ B₂
    · simp only [restr, if_pos hb]
      refine measure_mono_null ?_ (h.1 b)
      intro v hv hv2
      apply hv
      refine ⟨hv2.1, ?_⟩
      show g v ∈ B₂
      have : g v = b := by
        apply hι
        rw [← hf v]
        exact hv2.1
      rw [this]; exact hb
    · simp [restr, hb]
  · intro φ hφ
    rw [piece hι hg hf hB₂.measurableSet hsub h hφ, ← lintegral_indicator hB₂.measurableSet]
    refine lintegral_congr fun b => ?_
    by_cases hb : b ∈ B₂
    · simp [restr, hb]
    · simp [restr, hb]
  · intro φ hφ hφc hφs
    have H := h.2.2 φ hφ hφc (hφs.trans (Set.preimage_mono hsub))
    refine ⟨fun b hb => ?_, ?_⟩
    · simp only [restr, if_pos hb]
      exact H.1 b (hsub hb)
    · refine (H.2.mono hsub).congr fun b hb => ?_
      simp only [restr, if_pos hb]

end Local

theorem glue : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → (∀ b ∈ B, ∃ B' : Set X, IsOpen B' ∧ b ∈ B' ∧ B' ⊆ B ∧ ∃ fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib') → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf B hB hloc
  classical
  choose! C hCo hbC hCB F hF using hloc
  let fib : X → Measure V := fun b => if b ∈ B then F b b else 0
  have hfibB : ∀ c ∈ B, fib c = F c c := fun c hc => by simp only [fib, if_pos hc]
  have hagree : ∀ a ∈ B, ∀ c ∈ C a, fib c = F a c := by
    intro a ha c hc
    have hcB : c ∈ B := hCB a ha hc
    have hI : IsOpen (C c ∩ C a) := (hCo c hcB).inter (hCo a ha)
    have r1 := restr_family hι hg hf hI Set.inter_subset_right (hF a ha)
    have u := GlobalTheory.T.fibre_family_eq_on_open_subset V X Y μ ν f g ι hι hg hf (C c) (C c ∩ C a) (hCo c hcB) hI
      Set.inter_subset_left (F c) (restr (C c ∩ C a) (F a)) (hF c hcB) r1 c ⟨hbC c hcB, hc⟩
    have hm : c ∈ C c ∩ C a := ⟨hbC c hcB, hc⟩
    simp only [restr, if_pos hm] at u
    rw [hfibB c hcB, u]
  refine ⟨fib, ?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ B
    · rw [hfibB b hb]
      refine measure_mono_null (Set.compl_subset_compl.2 ?_) ((hF b hb).1 b)
      intro v hv
      exact ⟨hv.1, hCB b hb hv.2⟩
    · simp [fib, hb]
  · intro φ hφ
    rcases B.eq_empty_or_nonempty with rfl | hne
    · simp [fib]
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun b : B => C b)
      (fun b => hCo b b.2)
    have hall : ⋃ b : B, C b = B := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun b => hCB b b.2
      · intro b hb
        exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hbC b hb⟩
    have hTne : T.Nonempty := by
      by_contra hT
      rw [Set.not_nonempty_iff_eq_empty] at hT
      subst hT
      rw [hall] at hTU
      simp only [Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty] at hTU
      exact hne.ne_empty hTU.symm
    obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
    let s : ℕ → Set X := fun n => C (e n)
    have hsU : ⋃ n, s n = B := by
      rw [← hall, ← hTU, he]
      simp [s]
    have hDm : ∀ n, MeasurableSet (disjointed s n) :=
      MeasurableSet.disjointed fun n => (hCo (e n) (e n).2).measurableSet
    have hDd : Pairwise (Function.onFun Disjoint (disjointed s)) := disjoint_disjointed s
    have hDU : ⋃ n, disjointed s n = B := by rw [iUnion_disjointed, hsU]
    calc ∫⁻ v in g ⁻¹' B, φ v ∂μ
        = ∫⁻ v in ⋃ n, g ⁻¹' (disjointed s n), φ v ∂μ := by
          rw [← Set.preimage_iUnion, hDU]
      _ = ∑' n, ∫⁻ v in g ⁻¹' (disjointed s n), φ v ∂μ :=
          lintegral_iUnion (fun n => hg.measurable (hDm n))
            (fun i j hij => (hDd hij).preimage g) _
      _ = ∑' n, ∫⁻ b in disjointed s n, ∫⁻ v, φ v ∂(fib b) ∂ν := by
          refine tsum_congr fun n => ?_
          rw [piece hι hg hf (hDm n) (disjointed_subset s n) (hF (e n) (e n).2) hφ]
          refine setLIntegral_congr_fun (hDm n) fun b hb => ?_
          rw [hagree (e n) (e n).2 b (disjointed_subset s n hb)]
      _ = ∫⁻ b in ⋃ n, disjointed s n, ∫⁻ v, φ v ∂(fib b) ∂ν :=
          (lintegral_iUnion hDm hDd _).symm
      _ = ∫⁻ b in B, ∫⁻ v, φ v ∂(fib b) ∂ν := by rw [hDU]
      _ = ∫⁻ b, ∫⁻ v, φ v ∂(fib b) ∂ν := by
          rw [← lintegral_indicator hB.measurableSet]
          refine lintegral_congr fun b => ?_
          by_cases hb : b ∈ B
          · simp [hb]
          · simp [hb, fib]
  · intro φ hφ hφc hφs
    have key : ∀ b ∈ B, Integrable φ (fib b) ∧
        ContinuousAt (fun c => ∫ v, φ v ∂(fib c)) b := by
      intro b hb
      obtain ⟨L₁, hL₁c, hbL₁, hL₁C⟩ := exists_compact_between (isCompact_singleton (x := b))
        (hCo b hb) (Set.singleton_subset_iff.2 (hbC b hb))
      obtain ⟨L₂, hL₂c, hbL₂, hL₂C⟩ := exists_compact_between (isCompact_singleton (x := b))
        isOpen_interior hbL₁
      have hclos : IsCompact (closure (interior L₁)) :=
        hL₁c.closure_of_subset interior_subset
      obtain ⟨χ, hχs, hχ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_interior hclos
        hL₂c.isClosed hL₂C
      have hK : L₂ ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 (hbL₂ rfl)
      let ψ : V → ℝ := φ * (χ ∘ g)
      have hψ : Continuous ψ := hφ.mul (χ.continuous.comp hg)
      have hψc : HasCompactSupport ψ := hφc.mul_right
      have hψs : tsupport ψ ⊆ g ⁻¹' (C b) := by
        refine (tsupport_mul_subset_right).trans ?_
        refine (tsupport_comp_subset_preimage _ hg).trans ?_
        exact Set.preimage_mono (hχs.trans (interior_subset.trans hL₁C))
      have H := (hF b hb).2.2 ψ hψ hψc hψs
      have hCsub : L₂ ⊆ C b := hL₂C.trans (interior_subset.trans hL₁C)
      have hae : ∀ c ∈ L₂, ∀ᵐ v ∂(F b c), ψ v = φ v := by
        intro c hc
        refine (ae_g_eq hι hf ((hF b hb).1 c)).mono fun v hv => ?_
        simp [ψ, hv, hχ1 hc]
      have hbK : b ∈ L₂ := mem_of_mem_nhds hK
      refine ⟨?_, ?_⟩
      · rw [hagree b hb b (hbC b hb)]
        exact (H.1 b (hbC b hb)).congr (hae b hbK)
      · refine (H.2.continuousAt ((hCo b hb).mem_nhds (hbC b hb))).congr ?_
        filter_upwards [hK] with c hc
        rw [hagree b hb c (hCsub hc)]
        exact integral_congr_ae (hae c hc)
    exact ⟨fun b hb => (key b hb).1, fun b hb => (key b hb).2.continuousWithinAt⟩

end GlobalTheory.CompanionTheory.SW.FibreGlue
