import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

open scoped Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordUnfold

theorem isAddFundamentalDomain_prod {A B : Type} [AddGroup A] [AddGroup B] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SigmaFinite ν]
    {Γ : AddSubgroup A} {Δ : AddSubgroup B} {s : Set A} {t : Set B}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 : ∀ᵐ p ∂(μ.prod ν), ∃ g : Γ, g +ᵥ p.1 ∈ s :=
      Measure.quasiMeasurePreserving_fst.ae hs.ae_covers
    have h2 : ∀ᵐ p ∂(μ.prod ν), ∃ d : Δ, d +ᵥ p.2 ∈ t :=
      Measure.quasiMeasurePreserving_snd.ae ht.ae_covers
    filter_upwards [h1, h2] with p hg hd
    obtain ⟨g, hg⟩ := hg
    obtain ⟨d, hd⟩ := hd
    exact ⟨⟨((g : A), (d : B)), g.2, d.2⟩, hg, hd⟩
  aedisjoint := by
    rintro ⟨⟨g, d⟩, hg, hd⟩ ⟨⟨g', d'⟩, hg', hd'⟩ hne
    have key : ((⟨(g, d), hg, hd⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) ∩ ((⟨(g', d'), hg', hd'⟩ : Γ.prod Δ) +ᵥ s ×ˢ t) =
        (((⟨g, hg⟩ : Γ) +ᵥ s) ∩ ((⟨g', hg'⟩ : Γ) +ᵥ s)) ×ˢ (((⟨d, hd⟩ : Δ) +ᵥ t) ∩ ((⟨d', hd'⟩ : Δ) +ᵥ t)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_vadd_set_iff_neg_vadd_mem]
      exact ⟨fun ⟨⟨a1, a2⟩, a3, a4⟩ => ⟨⟨a1, a3⟩, a2, a4⟩, fun ⟨⟨a1, a3⟩, a2, a4⟩ => ⟨⟨a1, a2⟩, a3, a4⟩⟩
    show (μ.prod ν) (_ ∩ _) = 0
    rw [key, Measure.prod_prod]
    by_cases h : g = g'
    · subst h
      have hdd : (⟨d, hd⟩ : Δ) ≠ ⟨d', hd'⟩ := fun e => hne (by
        have := congrArg Subtype.val e
        simp only at this
        subst this; rfl)
      have := ht.aedisjoint hdd
      rw [show ν _ = 0 from this, mul_zero]
    · have hgg : (⟨g, hg⟩ : Γ) ≠ ⟨g', hg'⟩ := fun e => h (congrArg Subtype.val e)
      have := hs.aedisjoint hgg
      rw [show μ _ = 0 from this, zero_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem integral_fundamentalDomain_eq_iterated : ∀ (D : D7) (V W : HSp D) (a b k : ℕ) (f₁ f₃ : Mx D a b → WO V W) (f₂ : Mx D 1 k → WO V W), Continuous f₁ → Continuous f₂ → Continuous f₃ → (∀ s s', f₁ (s + s') = f₁ s + f₁ s') → (∀ z z', f₂ (z + z') = f₂ z + f₂ z') → (∀ y y', f₃ (y + y') = f₃ y + f₃ y') → (∀ x : WO V W, ∃ s z y, x = f₁ s + f₂ z + f₃ y) → (∀ s z y, f₁ s + f₂ z + f₃ y = 0 → s = 0 ∧ z = 0 ∧ y = 0) → (∀ s z y, f₁ s + f₂ z + f₃ y ∈ ratL W V ↔ s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∃ κ : ℝ, 0 < κ ∧ ∀ T : WO V W → ℂ, Continuous T → (∀ γ ∈ ratL W V, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂ν = κ * ∫ s in 𝓨, (∫ z in 𝓩, (∫ y in 𝓨, T (f₁ s + f₂ z + f₃ y) ∂μ) ∂η) ∂μ := by
  intro D V W a b k f₁ f₃ f₂ hc₁ hc₂ hc₃ ha₁ ha₂ ha₃ hsurj hinj hrat μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨j1, j2, j3, j4, j5, KZ, hKZ, hKZc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  obtain ⟨l1, l2, l3, l4, l5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V.rank
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D a b) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D 1 k) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsTopologicalAddGroup (WO V W) := l1
  haveI : LocallyCompactSpace (WO V W) := l2
  haveI : SecondCountableTopology (WO V W) := l3
  haveI : T2Space (WO V W) := l4
  haveI : BaireSpace (WO V W) := BaireSpace.of_t2Space_locallyCompactSpace
  haveI : Countable (ratL W V) := by
    have : Countable (GlobalTheory.MixModel.ratMx D W.rank V.rank) :=
      TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact this
  haveI := hμ.1

  have hZfin : η 𝓩 < ⊤ := by
    have hcov : 𝓩 ⊆ ⋃ γ : GlobalTheory.MixModel.ratMx D 1 k, ((γ +ᵥ KZ) ∩ 𝓩) := by
      intro x hx
      obtain ⟨γ, hγ, hγx⟩ := hKZc x
      refine Set.mem_iUnion.2 ⟨⟨-γ, neg_mem hγ⟩, Set.mem_vadd_set.2 ⟨γ + x, hγx, ?_⟩, hx⟩
      show -γ + (γ + x) = x
      abel
    calc η 𝓩 ≤ ∑' γ : GlobalTheory.MixModel.ratMx D 1 k, η ((γ +ᵥ KZ) ∩ 𝓩) :=
          (measure_mono hcov).trans (measure_iUnion_le _)
      _ = η KZ := (h𝓩.measure_eq_tsum KZ).symm
      _ < ⊤ := hKZ.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓩) := ⟨by rw [Measure.restrict_apply_univ]; exact hZfin⟩

  let Ehom : (Mx D a b × (Mx D 1 k × Mx D a b)) →+ WO V W :=
    AddMonoidHom.mk' (fun p => f₁ p.1 + f₂ p.2.1 + f₃ p.2.2) (fun p q => by
      simp only [Prod.fst_add, Prod.snd_add, ha₁, ha₂, ha₃]; abel)
  have hEc : Continuous Ehom :=
    ((hc₁.comp continuous_fst).add (hc₂.comp (continuous_fst.comp continuous_snd))).add
      (hc₃.comp (continuous_snd.comp continuous_snd))
  have hEi : Function.Injective Ehom := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨s, z, y⟩ h
    obtain ⟨h1, h2, h3⟩ := hinj s z y h
    simp [h1, h2, h3]
  have hEs : Function.Surjective Ehom := fun x => by
    obtain ⟨s, z, y, rfl⟩ := hsurj x
    exact ⟨(s, z, y), rfl⟩
  have hEo : IsOpenMap Ehom := AddMonoidHom.isOpenMap_of_sigmaCompact Ehom hEs hEc
  let Eq : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃+ WO V W := AddEquiv.ofBijective Ehom ⟨hEi, hEs⟩
  let H : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ WO V W := Eq.toEquiv.toHomeomorphOfContinuousOpen hEc hEo
  let Ec : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ₜ+ WO V W :=
    { Eq with continuous_toFun := hEc, continuous_invFun := H.symm.continuous }
  have hEapp : ∀ s z y, Ec (s, z, y) = f₁ s + f₂ z + f₃ y := fun _ _ _ => rfl
  let Me : (Mx D a b × (Mx D 1 k × Mx D a b)) ≃ᵐ WO V W := H.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl

  set lam : Measure (Mx D a b × (Mx D 1 k × Mx D a b)) := μ.prod (η.prod μ) with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set m : Measure (WO V W) := lam.map Me with hm
  haveI : m.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hνm := Measure.isAddLeftInvariant_eq_smul ν m
  set c := Measure.addHaarScalarFactor ν m with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν m
  have hcne : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'

  set Γ : AddSubgroup (Mx D a b × (Mx D 1 k × Mx D a b)) :=
    (GlobalTheory.MixModel.ratMx D a b).prod ((GlobalTheory.MixModel.ratMx D 1 k).prod (GlobalTheory.MixModel.ratMx D a b)) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ ratL W V := by
    rintro ⟨s, z, y⟩
    rw [hEapp, hrat]
    simp [Γ, AddSubgroup.mem_prod]
  have hFDP : IsAddFundamentalDomain Γ (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) lam :=
    isAddFundamentalDomain_prod hμ.2.1 (isAddFundamentalDomain_prod h𝓩 hμ.2.1)
  have hac : lam.map Me ≪ ν := by
    intro s hs
    rw [hνm, Measure.smul_apply] at hs
    exact (smul_eq_zero.1 hs).resolve_left hc.ne'
  have hqmp : Measure.QuasiMeasurePreserving Me lam ν := ⟨Me.measurable, hac⟩
  let eΓ : ratL W V → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    h𝓕.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : WO V W) + Me p
      rw [hMe, hMe, map_add, Ec.apply_symm_apply])
  refine ⟨(c : ℝ), by exact_mod_cast hc, fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂ν = (c : ℝ) • ∫ u in 𝓕, T u ∂m := by
    rw [hνm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂m = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓨 ×ˢ (𝓩 ×ˢ 𝓨), T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓨 ×ˢ (𝓩 ×ˢ 𝓨)) = (μ.restrict 𝓨).prod ((η.restrict 𝓩).prod (μ.restrict 𝓨)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  have hs : Continuous fun q : Mx D 1 k × Mx D a b => T (Me (s, q)) := hTE.comp (Continuous.prodMk_right s)
  dsimp only
  rw [integral_prod _ (Integrable.of_bound hs.aestronglyMeasurable C (ae_of_all _ fun p => hbd _))]
  rfl

end GlobalTheory.CoordUnfold

end
