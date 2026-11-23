import Mathlib

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.FiberInt

variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']

noncomputable def periodized (π : A →+ A') (Γ' : AddSubgroup A') (lam : Measure A) (𝓖 : Set A) :
    Measure A' :=
  Measure.sum fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)

theorem lintegral_periodized {π : A →+ A'} (hπ : Measurable π) {Γ' : AddSubgroup A'} [Countable Γ']
    (lam : Measure A) (𝓖 : Set A) {f : A' → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(periodized π Γ' lam 𝓖) = ∫⁻ x in 𝓖, ∑' γ : Γ', f ((γ : A') + π x) ∂lam := by
  rw [show periodized π Γ' lam 𝓖 = Measure.sum (fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)) from rfl, lintegral_sum_measure,
    lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    rw [lintegral_map hf (measurable_const_add _), lintegral_map _ hπ]
    exact hf.comp (measurable_const_add _)
  · intro γ
    exact (hf.comp ((measurable_const_add _).comp hπ)).aemeasurable

theorem periodized_invariant {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} [lam.IsAddHaarMeasure] {𝓖 : Set A}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) :
    (periodized π Γ' lam 𝓖).IsAddLeftInvariant := by
  constructor
  intro c
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_const_add c),
    lintegral_periodized hπ lam 𝓖 (f := fun y => f (c + y)) (hf.comp (measurable_const_add c)),
    lintegral_periodized hπ lam 𝓖 hf]
  have key : ∀ x : A, ∑' γ : Γ', f (c + ((γ : A') + π x)) = ∑' γ : Γ', f ((γ : A') + π (s c + x)) := by
    intro x
    refine tsum_congr fun γ => ?_
    rw [map_add, hs]
    congr 1
    abel
  simp_rw [key]
  have hemb : MeasurableEmbedding (fun x : A => s c + x) :=
    (MeasurableEquiv.addLeft (s c)).measurableEmbedding
  rw [(measurePreserving_add_left lam (s c)).setLIntegral_comp_emb hemb
    (fun x => ∑' γ : Γ', f ((γ : A') + π x)) 𝓖]
  have hG' : IsAddFundamentalDomain Γ ((fun x : A => s c + x) '' 𝓖) lam := hG.vadd_of_comm (s c)
  refine hG'.setLIntegral_eq hG _ ?_
  intro g x
  show ∑' γ : Γ', f ((γ : A') + π ((g : A) + x)) = ∑' γ : Γ', f ((γ : A') + π x)
  rw [← (Equiv.addRight (⟨π g, hΓ g g.2⟩ : Γ')).tsum_eq (fun γ : Γ' => f ((γ : A') + π x))]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_addRight, AddSubgroup.coe_add, map_add, add_assoc]

instance {π : A →+ A'} {Γ' : AddSubgroup A'} [Countable Γ'] {lam : Measure A} [SFinite lam]
    {𝓖 : Set A} : SFinite (periodized π Γ' lam 𝓖) := by
  unfold periodized; infer_instance

theorem measure_preimage_inter_eq {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} {lam' : Measure A'} [lam.IsAddHaarMeasure]
    [lam'.IsAddHaarMeasure] {𝓖 : Set A} {𝓖' : Set A'}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (hG' : IsAddFundamentalDomain Γ' 𝓖' lam') (h1' : lam' 𝓖' = 1)
    {S : Set A'} (hS : MeasurableSet S) (hinv : ∀ γ ∈ Γ', ∀ x, γ + x ∈ S ↔ x ∈ S) :
    lam (π ⁻¹' S ∩ 𝓖) = lam' (S ∩ 𝓖') := by
  obtain ⟨P, hPdef⟩ : ∃ P, P = periodized π Γ' lam 𝓖 := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = Measure.map π (lam.restrict 𝓖) := ⟨_, rfl⟩
  have hPsum : P = Measure.sum fun γ : Γ' => ν.map ((γ : A') + ·) := by rw [hPdef, hνdef]; rfl
  have : P.IsAddLeftInvariant := by rw [hPdef]; exact periodized_invariant hπ hs hΓ hG
  have : SFinite P := by rw [hPdef]; infer_instance
  have : lam'.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam'
  have : lam'.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular lam'
  obtain ⟨M, hMdef⟩ : ∃ M, M = toMeasurable lam' 𝓖' := ⟨_, rfl⟩
  have hMm : MeasurableSet M := by rw [hMdef]; exact measurableSet_toMeasurable lam' 𝓖'
  have hMae : M =ᵐ[lam'] 𝓖' := by rw [hMdef]; exact hG'.nullMeasurableSet.toMeasurable_ae_eq
  have hM1 : lam' M = 1 := by rw [hMdef, measure_toMeasurable, h1']
  have hne : lam' ≠ 0 := fun h => by simp [h] at h1'
  have hPac : P ≪ lam' := absolutelyContinuous_of_isAddLeftInvariant P lam' hne
  have hνP : ν ≤ P := by
    have h0 := Measure.le_sum (fun γ : Γ' => Measure.map (fun y : A' => (γ : A') + y) ν) 0
    simp only [AddSubgroup.coe_zero, zero_add, Measure.map_id'] at h0
    rw [hPsum]
    exact h0
  have hνac : ν ≪ lam' := by
    intro t ht
    exact le_antisymm ((Measure.le_iff'.1 hνP t).trans (hPac ht).le) zero_le
  have claim : ∀ T : Set A', MeasurableSet T → (∀ γ ∈ Γ', ∀ x, γ + x ∈ T ↔ x ∈ T) →
      lam (π ⁻¹' T ∩ 𝓖) = P (T ∩ M) := by
    intro T hT hTinv
    have e1 : lam (π ⁻¹' T ∩ 𝓖) = ν T := by
      rw [hνdef, Measure.map_apply hπ hT, Measure.restrict_apply (hπ hT)]
    rw [e1, hG'.measure_eq_tsum_of_ac hνac T, hPsum, Measure.sum_apply _ (hT.inter hMm)]
    conv_lhs => rw [← (Equiv.neg Γ').tsum_eq]
    refine tsum_congr fun γ => ?_
    rw [Measure.map_apply (measurable_const_add _) (hT.inter hMm)]
    have hpre : (fun x => (γ : A') + x) ⁻¹' (T ∩ M) = T ∩ (fun x => (γ : A') + x) ⁻¹' M := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, hTinv γ γ.2 x]
    have hset : (fun x => (γ : A') + x) ⁻¹' 𝓖' = (Equiv.neg Γ') γ +ᵥ 𝓖' := by
      ext x
      rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
      simp [AddSubgroup.vadd_def]
    have hae : (fun x => (γ : A') + x) ⁻¹' M =ᵐ[lam'] (fun x => (γ : A') + x) ⁻¹' 𝓖' :=
      (measurePreserving_add_left lam' (γ : A')).quasiMeasurePreserving.preimage_ae_eq hMae
    rw [hpre, ← hset]
    exact measure_congr ((ae_eq_refl T).inter (hνac.ae_eq hae).symm)
  have hPt : ∀ t, MeasurableSet t → P t = P M * lam' t := by
    intro t ht
    have h := measure_add_lintegral_eq lam' P hMm (t.indicator 1) (measurable_one.indicator ht)
    rw [hM1, one_mul, lintegral_indicator_one ht] at h
    rw [h]
    have hc : ∀ x : A', P ((fun z => z + x) ⁻¹' M) = P M := fun x => by
      simp_rw [add_comm _ x]
      exact measure_preimage_add P x M
    simp_rw [hc]
    rw [lintegral_const_mul (P M) (f := fun x => t.indicator 1 (-x))
      ((measurable_one.indicator ht).comp measurable_neg),
      lintegral_neg_eq_self (t.indicator 1), lintegral_indicator_one ht]
  have hU := claim Set.univ MeasurableSet.univ (fun _ _ _ => by simp)
  rw [Set.preimage_univ, Set.univ_inter, h1, Set.univ_inter] at hU
  rw [claim S hS hinv, hPt _ (hS.inter hMm), ← hU, one_mul]
  exact measure_congr ((ae_eq_refl S).inter hMae)

theorem integral_comp_eq : ∀ {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A'] [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A'] (π : A →+ A') (s : A' →+ A), Continuous π → Continuous s → (∀ x, π (s x) = x) → ∀ (Γ : AddSubgroup A) (Γ' : AddSubgroup A'), Countable Γ → Countable Γ' → (∀ γ ∈ Γ, π γ ∈ Γ') → (∀ γ ∈ Γ', s γ ∈ Γ) → ∀ (lam : Measure A) (lam' : Measure A'), lam.IsAddHaarMeasure → lam'.IsAddHaarMeasure → ∀ (𝓖 : Set A) (𝓖' : Set A'), IsAddFundamentalDomain Γ 𝓖 lam → lam 𝓖 = 1 → IsAddFundamentalDomain Γ' 𝓖' lam' → lam' 𝓖' = 1 → ∀ G : A' → ℂ, Continuous G → (∀ γ ∈ Γ', ∀ x, G (γ + x) = G x) → ∫ x in 𝓖, G (π x) ∂lam = ∫ x in 𝓖', G x ∂lam' := by
  intro A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π s hπc _ hs Γ Γ' hΓc hΓ'c hΓ _ lam lam' hlam hlam' 𝓖 𝓖' hG h1 hG' h1' G hGc hGinv
  have := hΓc
  have := hΓ'c
  have := hlam
  have := hlam'
  have hπ : Measurable π := hπc.measurable
  have hGm : Measurable G := hGc.measurable
  have key : Measure.map G (Measure.map π (lam.restrict 𝓖)) = Measure.map G (lam'.restrict 𝓖') := by
    ext B hB
    have hinvB : ∀ γ ∈ Γ', ∀ x, γ + x ∈ G ⁻¹' B ↔ x ∈ G ⁻¹' B := fun γ hγ x => by
      simp only [Set.mem_preimage, hGinv γ hγ x]
    rw [Measure.map_apply hGm hB, Measure.map_apply hGm hB, Measure.map_apply hπ (hGm hB),
      Measure.restrict_apply (hπ (hGm hB)), Measure.restrict_apply (hGm hB)]
    exact measure_preimage_inter_eq hπ hs hΓ hG h1 hG' h1' (hGm hB) hinvB
  calc ∫ x in 𝓖, G (π x) ∂lam = ∫ y, G y ∂(Measure.map π (lam.restrict 𝓖)) :=
        (integral_map hπ.aemeasurable hGc.aestronglyMeasurable).symm
    _ = ∫ z, z ∂(Measure.map G (Measure.map π (lam.restrict 𝓖))) :=
        (integral_map hGm.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ z, z ∂(Measure.map G (lam'.restrict 𝓖')) := by rw [key]
    _ = ∫ x in 𝓖', G x ∂lam' := integral_map hGm.aemeasurable aestronglyMeasurable_id

end GlobalTheory.CompanionTheory.FiberInt
