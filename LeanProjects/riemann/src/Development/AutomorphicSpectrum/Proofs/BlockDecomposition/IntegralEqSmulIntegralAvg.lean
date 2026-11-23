import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarQK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapWithDensityEqOfScale
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotVan

def AbsVanish : Prop := ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (Q K : Subgroup G) (_ : IsClosed (Q : Set G)) (_ : IsCompact (K : Set G))
  (_ : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k)
  (N M : Subgroup Q) [N.Normal] (_ : IsClosed (N : Set Q)) (_ : IsClosed (M : Set Q))
  (_ : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m) (_ : N ⊓ M = ⊥)
  (νN : Measure N) [νN.IsHaarMeasure]
  (T : Subgroup G) (_ : ∀ t ∈ T, ∃ h : t ∈ Q, (⟨t, h⟩ : Q) ∈ M)
  (μT : Measure T) [SFinite μT] [μT.IsInvInvariant]
  (F : G → ℂ), Measurable F → (∀ t ∈ T, ∀ x, F (t * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) →
    (∀ x, ∫ u : N, F (((u : Q) : G) * x) ∂νN = 0) → quotIntegral μ T μT F = 0

theorem integral_mul_weight_eq_zero {Q : Type} [Group Q] [MeasurableSpace Q]
    (N M : Subgroup Q) (νN : Measure N) [SFinite νN] (νM : Measure M) [SFinite νM]
    (δ : M → ℝ≥0∞) (hδ : Measurable δ) (hδt : ∀ m, δ m ≠ ∞)
    (hφ : MeasurableEmbedding (fun p : N × M => (p.1 : Q) * (p.2 : Q)))
    (f w : Q → ℂ) (w' : M → ℂ) (hw : ∀ (u : N) (m : M), w ((u : Q) * (m : Q)) = w' m)
    (hf0 : ∀ m : M, ∫ u : N, f ((u : Q) * (m : Q)) ∂νN = 0) :
    ∫ q, f q * w q ∂(((νN.prod νM).withDensity fun p => δ p.2).map
      (fun p : N × M => (p.1 : Q) * (p.2 : Q))) = 0 := by
  rw [hφ.integral_map,
    integral_withDensity_eq_integral_toReal_smul (f := fun p : N × M => δ p.2) (hδ.comp measurable_snd)
      (Filter.Eventually.of_forall fun p => lt_top_iff_ne_top.2 (hδt p.2))]
  by_cases hI : Integrable (fun p : N × M => (δ p.2).toReal • (f ((p.1 : Q) * (p.2 : Q)) *
      w ((p.1 : Q) * (p.2 : Q)))) (νN.prod νM)
  · rw [integral_prod_symm _ hI]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun m => ?_)
    simp only [hw, Pi.zero_apply]
    rw [integral_smul, integral_mul_const, hf0 m]
    simp
  · exact integral_undef hI

theorem integral_eq_smul_integral_avg {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) (Q K : Subgroup G) (νQ : Measure Q) [SFinite νQ] (κ : Measure K) [SFinite κ]
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hμ : μ = c • (νQ.prod κ).map (fun p : Q × K => (p.1 : G) * (p.2 : G)))
    (F : G → ℂ) (hF : Measurable F) (hFK : ∀ k ∈ K, ∀ x, F (x * k) = F x)
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hfin : ∀ᵐ g ∂μ, ρ g < ∞)
    (hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ =
      c.toReal • ∫ q : Q, F q * (((∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ).toReal : ℝ) : ℂ) ∂νQ := by
  have hm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hg : Measurable (fun g => F g * ((ρ g).toReal : ℂ)) :=
    hF.mul (Complex.measurable_ofReal.comp hρ.ennreal_toReal)
  subst hμ
  have hint' := (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).1
    ((integrable_smul_measure hc0 hct).1 hint)
  have hfin' : ∀ᵐ p ∂(νQ.prod κ), ρ ((p.1 : G) * (p.2 : G)) < ∞ :=
    ae_of_ae_map hm.aemeasurable ((Measure.absolutelyContinuous_smul hc0).ae_le hfin)
  have hint'' : Integrable (fun p : Q × K => F ((p.1 : G) * (p.2 : G)) *
      ((ρ ((p.1 : G) * (p.2 : G))).toReal : ℂ)) (νQ.prod κ) := hint'
  rw [integral_smul_measure, integral_map hm.aemeasurable hg.aestronglyMeasurable,
    integral_prod _ hint'']
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hfin'] with q hq
  have hmk : Measurable fun k : K => ρ ((q : G) * (k : G)) :=
    hρ.comp (measurable_subtype_coe.const_mul _)
  have e1 : ∀ k : K, F ((q : G) * (k : G)) = F q := fun k => hFK k k.2 _
  simp only [e1]
  rw [integral_const_mul, integral_complex_ofReal, integral_toReal hmk.aemeasurable hq]

section Normalisers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def onQ (Q T : Subgroup G) (h : T ≤ Q) (t : T) : T.subgroupOf Q :=
  ⟨⟨t, h t.2⟩, Subgroup.mem_subgroupOf.2 t.2⟩

theorem measurable_onQ (Q T : Subgroup G) (h : T ≤ Q) : Measurable (onQ Q T h) :=
  (measurable_subtype_coe.subtype_mk).subtype_mk

theorem isInvInvariant_map_onQ (Q T : Subgroup G) (h : T ≤ Q) (μT : Measure T) [μT.IsInvInvariant] :
    (μT.map (onQ Q T h)).IsInvInvariant := by
  have hi : MeasurableInv T := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hi' : MeasurableInv (T.subgroupOf Q) := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  show Measure.map Inv.inv (μT.map (onQ Q T h)) = μT.map (onQ Q T h)
  rw [Measure.map_map measurable_inv (measurable_onQ Q T h)]
  have e : (Inv.inv ∘ onQ Q T h) = onQ Q T h ∘ Inv.inv := rfl
  rw [e, ← Measure.map_map (measurable_onQ Q T h) measurable_inv]
  exact congrArg (Measure.map (onQ Q T h)) (Measure.inv_eq_self μT)

theorem normaliser_onQ {Q T : Subgroup G} (hTQ : T ≤ Q) {μT : Measure T} {σ : Q → ℝ≥0∞}
    (hσ : Measurable σ) (h : ∀ q : Q, ∫⁻ t : T, σ (⟨t, hTQ t.2⟩ * q) ∂μT = 1) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) σ := by
  refine ⟨hσ, fun q => ?_⟩
  have hm : Measurable fun x : T.subgroupOf Q => σ ((x : Q) * q) :=
    hσ.comp (measurable_subtype_coe.mul_const q)
  rw [lintegral_map hm (measurable_onQ Q T hTQ)]
  exact h q

theorem normaliser_avg {Q K T : Subgroup G} (hTQ : T ≤ Q) (κ : Measure K) [SFinite κ]
    (hκ : κ Set.univ = 1) {μT : Measure T} [SFinite μT] {ρ : G → ℝ≥0∞}
    (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ))
      (fun q => ∫⁻ k : K, ρ ((q : G) * (k : G)) ∂κ) := by
  have hm : Measurable fun p : Q × K => ρ ((p.1 : G) * (p.2 : G)) :=
    hρ.1.comp ((measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd))
  refine normaliser_onQ hTQ hm.lintegral_prod_right' fun q => ?_
  rw [lintegral_lintegral_swap]
  · have key : ∀ k : K, ∫⁻ t : T, ρ (((⟨t, hTQ t.2⟩ * q : Q) : G) * (k : G)) ∂μT = 1 := fun k => by
      have := hρ.2 ((q : G) * (k : G))
      simpa [mul_assoc] using this
    simp only [key, lintegral_one, hκ]
  · have : Measurable fun p : T × K => ρ (((p.1 : G) * (q : G)) * (p.2 : G)) :=
      hρ.1.comp (((measurable_subtype_coe.comp measurable_fst).mul_const _).mul
        (measurable_subtype_coe.comp measurable_snd))
    exact this.aemeasurable

theorem normaliser_proj {Q T : Subgroup G} (hTQ : T ≤ Q) (N M : Subgroup Q) [hN : N.Normal]
    (hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M) (hdec : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m)
    (pr : Q → M) (hprm : Measurable pr) (hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m)
    {μT : Measure T} {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser T μT ρ) :
    IsQuotNormaliser (T.subgroupOf Q) (μT.map (onQ Q T hTQ)) (fun q => ρ ((pr q : Q) : G)) := by
  refine normaliser_onQ hTQ
    (hρ.1.comp (measurable_subtype_coe.comp (measurable_subtype_coe.comp hprm))) fun q => ?_
  obtain ⟨u, hu, m, hm, rfl⟩ := hdec q
  have key : ∀ t : T, ((pr ((⟨t, hTQ t.2⟩ : Q) * (u * m)) : Q) : G) = (t : G) * ((m : Q) : G) := by
    intro t
    have e : (⟨t, hTQ t.2⟩ : Q) * (u * m) =
        ((⟨(⟨t, hTQ t.2⟩ : Q) * u * (⟨t, hTQ t.2⟩ : Q)⁻¹, hN.conj_mem u hu _⟩ : N) : Q) *
          ((⟨(⟨t, hTQ t.2⟩ : Q) * m, M.mul_mem (hTM t) hm⟩ : M) : Q) := by
      simp only
      group
    rw [e, hpr]
    rfl
  simp only [key]
  exact hρ.2 _

end Normalisers

theorem absVanish_of (hQK : HaarQK) (hNM : HaarNM) : AbsVanish := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K hQ hK hdec N M _ hN hM hnm hinf νN _ T hT μT _ _ F hF hFT hFK hF0
  classical
  by_cases hex : ∃ ρ, IsQuotNormaliser T μT ρ
  swap
  · simp [quotIntegral, hex]
  rw [quotIntegral, dif_pos hex]
  have hρ := hex.choose_spec
  generalize hex.choose = ρ at hρ
  have hTQ : T ≤ Q := fun t ht => by
    obtain ⟨h, _⟩ := hT t ht
    exact h
  have hTM : ∀ t : T, (⟨t, hTQ t.2⟩ : Q) ∈ M := fun t => by
    obtain ⟨h, h'⟩ := hT t t.2
    exact h'
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Q := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology M := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : PolishSpace N := PI.VolStabS.TopoPolish.polish_of_lcsc N
  haveI : PolishSpace M := PI.VolStabS.TopoPolish.polish_of_lcsc M
  obtain ⟨νQ, _⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨νM, _⟩ : ∃ ν : Measure M, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨κ, _, hκ⟩ : ∃ κ : Measure K, κ.IsHaarMeasure ∧ κ Set.univ = 1 :=
    ⟨Measure.haarMeasure ⊤, inferInstance, Measure.haarMeasure_self⟩
  obtain ⟨c, hc0, hct, hμ⟩ := hQK μ Q K hQ hK hdec νQ κ
  obtain ⟨δ, hδ, hδt, hνQ⟩ := hNM νQ N M hN hM hnm hinf νN νM
  have φc : Continuous fun p : N × M => (p.1 : Q) * (p.2 : Q) := by fun_prop
  have φemb : MeasurableEmbedding fun p : N × M => (p.1 : Q) * (p.2 : Q) :=
    φc.measurableEmbedding (mulMap_injective N M hinf)
  let pr : Q → M := Function.extend (fun p : N × M => (p.1 : Q) * (p.2 : Q)) Prod.snd (fun _ => 1)
  have hprm : Measurable pr := φemb.measurable_extend measurable_snd measurable_const
  have hpr : ∀ (u : N) (m : M), pr ((u : Q) * (m : Q)) = m := fun u m =>
    (mulMap_injective N M hinf).extend_apply Prod.snd _ (u, m)
  have hfin := GlobalTheory.CompanionTheory.QuotNorm.ae_lt_top_of_normaliser (μG := μ) hρ
  by_cases hint : Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μ
  swap
  · exact integral_undef hint
  rw [integral_eq_smul_integral_avg μ Q K νQ κ c hc0 hct hμ F hF hFK ρ hρ.1 hfin hint]
  haveI := isInvInvariant_map_onQ Q T hTQ μT
  have hρ₁ := normaliser_avg (Q := Q) hTQ κ hκ hρ
  have hρ₂ := normaliser_proj hTQ N M hTM hnm pr hprm hpr hρ
  have e := GlobalTheory.CompanionTheory.QuotNorm.integral_normaliser_eq_of (μG := νQ) (F := fun q : Q => F q)
    (hF.comp measurable_subtype_coe)
    (fun h hh g => hFT h (Subgroup.mem_subgroupOf.1 hh) g) hρ₁ hρ₂
  have z : ∫ q : Q, F q * ((ρ ((pr q : Q) : G)).toReal : ℂ) ∂νQ = 0 := by
    rw [hνQ]
    exact integral_mul_weight_eq_zero N M νN νM δ hδ hδt φemb _ _
      (fun m => ((ρ ((m : Q) : G)).toReal : ℂ)) (fun u m => by simp only [hpr])
      (fun m => hF0 _)
  rw [e, z, smul_zero]

theorem absVanish : AbsVanish := absVanish_of haarQK haarNM

end GlobalTheory.CompanionTheory.QuotVan

end
