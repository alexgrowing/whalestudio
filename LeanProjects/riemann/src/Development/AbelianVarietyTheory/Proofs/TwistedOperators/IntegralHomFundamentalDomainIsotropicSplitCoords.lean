import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecompositionStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistHaar

open scoped Pointwise

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  aedisjoint := by
    intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

end GlobalTheory.TwistHaar

namespace GlobalTheory.TwistHaar

open scoped Pointwise

set_option maxHeartbeats 1000000 in

theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ κ : ℝ, 0 < κ ∧ (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) := by
  intro D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨e, he, hrat⟩ := GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition D V V' W r C B hs C' h1 h2 h3
  obtain ⟨a1, a2, a3, a4, a5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨b1, b2, b3, b4, b5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have : BorelSpace (WO V' W) := ⟨rfl⟩
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : DiscreteTopology (ratMx D W.rank r) := a5
  have : DiscreteTopology (ratL W V') := b5
  have : DiscreteTopology (ratL W V) := c5
  have cA : Countable (ratMx D W.rank r) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have cB : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : μ.IsAddHaarMeasure := hY.1

  set Γ' : AddSubgroup (Mx D W.rank r × Mx D W.rank r × WO V' W) :=
    (ratMx D W.rank r).prod ((ratMx D W.rank r).prod (ratL W V')) with hΓ'
  have hmem : ∀ p, e p ∈ ratL W V ↔ p ∈ Γ' := by
    rintro ⟨t, y, x⟩
    rw [hrat]
    simp [Γ', AddSubgroup.mem_prod]
  have : Countable Γ' := Function.Injective.countable
    (f := fun g : Γ' => ((⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).1, (AddSubgroup.mem_prod.1 g.2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.1, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).1⟩ :
        ratMx D W.rank r),
      (⟨(g : Mx D W.rank r × Mx D W.rank r × WO V' W).2.2, (AddSubgroup.mem_prod.1 (AddSubgroup.mem_prod.1 g.2).2).2⟩ :
        ratL W V')))
    fun g h hgh => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hgh
      exact Subtype.ext (Prod.ext hgh.1 (Prod.ext hgh.2.1 hgh.2.2))
  set P : Measure (Mx D W.rank r × Mx D W.rank r × WO V' W) := μ.prod (μ.prod μ') with hP
  have hT : IsAddFundamentalDomain Γ' (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) P :=
    isAddFundamentalDomain_prod hY.2.1 (isAddFundamentalDomain_prod hY.2.1 hF')
  set m : Measure (WO V W) := P.map e with hm
  have : (μ.prod μ').IsAddHaarMeasure := inferInstance
  have : P.IsAddHaarMeasure := inferInstance
  have : m.IsAddHaarMeasure := e.isAddHaarMeasure_map P
  have : VAddInvariantMeasure Γ' (Mx D W.rank r × Mx D W.rank r × WO V' W) P :=
    ⟨fun g s _ => measure_preimage_add P (g : Mx D W.rank r × Mx D W.rank r × WO V' W) s⟩
  set c : NNReal := μV.addHaarScalarFactor m with hcdef
  have hc : μV = c • m := Measure.isAddLeftInvariant_eq_smul μV m
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact (NeZero.ne μV) hc
  have hac : m ≪ μV := fun s hs0 => by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hs0
    exact (mul_eq_zero.1 hs0).resolve_left (by simpa using hc0)
  have hFm : IsAddFundamentalDomain (ratL W V) 𝓕V m := hFV.mono hac
  have hemeas : Measurable e := e.continuous.measurable
  have hpre : IsAddFundamentalDomain Γ' (e ⁻¹' 𝓕V) P := by
    refine hFm.preimage_of_equiv (f := e) (MeasurePreserving.quasiMeasurePreserving ⟨hemeas, rfl⟩)
      (e := fun g => ⟨e.symm g, (hmem _).1 (by simpa using g.2)⟩) ⟨fun g h hgh => ?_, fun g => ?_⟩ fun g x => ?_
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val hgh))
    · exact ⟨⟨e g, (hmem g).2 g.2⟩, Subtype.ext (by simp)⟩
    · change e (e.symm g + x) = (g : WO V W) + e x
      rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have hfin : μ' 𝓕' ≠ ⊤ := (GlobalTheory.Size.measure_dom hμ' hF').2
  have : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc0), fun H hH hb hper => ?_⟩
  obtain ⟨b, hb⟩ := hb
  have hmeasH : Measurable (fun p => H (e p)) := (hH.comp e.continuous).measurable
  have step1 : ∫ w in 𝓕V, H w ∂μV = (c : ℝ) • ∫ w in 𝓕V, H w ∂m := by
    have : μV = (c : ENNReal) • m := by rw [hc]; rfl
    rw [this, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  have step2 : ∫ w in 𝓕V, H w ∂m = ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P :=
    (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding).setIntegral_map H 𝓕V
  have step3 : ∫ p in e ⁻¹' 𝓕V, H (e p) ∂P = ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P :=
    hpre.setIntegral_eq hT (f := fun p => H (e p)) fun g p => by
      change H (e ((g : Mx D W.rank r × Mx D W.rank r × WO V' W) + p)) = H (e p)
      rw [map_add]
      exact hper _ ((hmem g).2 g.2) _
  have r1 : (μ.prod (μ.prod μ')).restrict (𝓨 ×ˢ (𝓨 ×ˢ 𝓕')) =
      (μ.restrict 𝓨).prod ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    ((congrArg (Measure.prod (μ.restrict 𝓨)) (Measure.prod_restrict 𝓨 𝓕')).trans
      (Measure.prod_restrict 𝓨 (𝓨 ×ˢ 𝓕'))).symm
  have step4 : ∫ p in 𝓨 ×ˢ (𝓨 ×ˢ 𝓕'), H (e p) ∂P = ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕',
      H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ := by
    refine (congrArg (fun ν => ∫ p, H (e p) ∂ν) r1).trans ?_
    refine (integral_prod _ (Integrable.of_bound hmeasH.aestronglyMeasurable b
      (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    refine (integral_prod (fun q => H (e (t, q))) (Integrable.of_bound
      (hmeasH.comp measurable_prodMk_left).aestronglyMeasurable b (Filter.Eventually.of_forall fun p => hb _))).trans ?_
    simp only [he]
  exact step1.trans (congrArg (fun z : ℂ => (c : ℝ) • z) ((step2.trans step3).trans step4))

end GlobalTheory.TwistHaar
