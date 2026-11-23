import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotientIntegralVanishOfIteratedFiniteIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepIteratedQuotientIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.VanMany

theorem quot_lin {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G} {I : Type}
    [Fintype I] (α : I → ℂ) (f : I → G → ℂ) (z : I → ℂ) (h : ∀ i, IsQuotIntL1 μR μG (f i) (z i)) :
    IsQuotIntL1 μR μG (fun x => ∑ i, α i * f i x) (∑ i, α i * z i) := by
  classical
  have key : ∀ S : Finset I, IsQuotIntL1 μR μG (fun x => ∑ i ∈ S, α i * f i x) (∑ i ∈ S, α i * z i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact IsQuotIntL1.zero
    | insert i S hi ih =>
      have := ((h i).smul (α i)).add ih
      have e : (fun x => ∑ j ∈ insert i S, α j * f j x) = α i • f i + (fun x => ∑ j ∈ S, α j * f j x) := by
        funext x
        simp [Finset.sum_insert hi]
      rw [e, Finset.sum_insert hi]
      exact this
  exact key Finset.univ

theorem iteratedQuotientIntegral_finite_linearCombination {G₁ G₂ : Type} [Group G₁] [MeasurableSpace G₁] [TopologicalSpace G₁] [Group G₂] [MeasurableSpace G₂]
    [TopologicalSpace G₂] {R₁ : Subgroup G₁} {R₂ : Subgroup G₂} (ρ₁ : Measure R₁) (μ₁ : Measure G₁) (ρ₂ : Measure R₂)
    (μ₂ : Measure G₂) {I : Type} [Fintype I] (α : I → ℂ) (f : I → G₁ → G₂ → ℂ) (v : I → ℂ)
    (h : ∀ i, Iter2 ρ₁ μ₁ ρ₂ μ₂ (f i) (v i)) :
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ => ∑ i, α i * f i q₁ q₂) (∑ i, α i * v i) := by
  choose g hg1 hg2 using h
  exact ⟨fun q => ∑ i, α i * g i q, quot_lin α g v hg1, fun q => quot_lin α (fun i => f i q) (fun i => g i q) fun i => hg2 i q⟩

theorem invsupp : ∀ (D : D7) (c : Comm D) (t : Tup c), t.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (φ : t.Ch j → GA D (c.X j) → ℂ) (f : GA D (c.V (j + 1 + 1)) → ℂ) (K₁ : Subgroup (GA D (c.V (j + 1)))) (T₁ : Finset (GA D (c.V (j + 1)))), (∀ k ∈ K₁, ∃ a : ℂ, a ≠ 0 ∧ t.om j (1, k) (t.pt j P₁) = a⁻¹ • t.pt j P₁ ∧ t.om (j + 1) (k, 1) (t.pt (j + 1) P₂) = a • t.pt (j + 1) P₂) → (∀ α, ∀ g ∈ (t.e j α).support, ∀ h₁, flatBF (t.sBF j (σ + 1) h) (t.om j (g, h₁) (t.pt j P₁)) ≠ 0 → ∃ q ∈ T₁, InCell (jacGrp (c.jac j (σ + 1) h).d) q K₁ h₁) → (∀ h₁, ∀ k ∈ K₁, t.integrand j σ h P₁ P₂ φ f (h₁ * k) = t.integrand j σ h P₁ P₂ φ f h₁) ∧ (∀ h₁, t.integrand j σ h P₁ P₂ φ f h₁ ≠ 0 → ∃ q ∈ T₁, InCell (jacGrp (c.jac j (σ + 1) h).d) q K₁ h₁) := by
  intro D c t ht j σ h P₁ P₂ φ f K₁ T₁ hlaw hsupp
  obtain ⟨hs1om, -⟩ := ht.sBF j (σ + 1) h
  obtain ⟨hs2om, -⟩ := ht.sFB j σ h
  have HH := fun φ' => GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) φ'
  have per0 : ∀ f', (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ 0 f' = 0 := by
    intro f'
    have := (HH (fun _ => 0)).2.2 0 1 0 f'
    simpa using this
  refine ⟨fun h₁ k hk => ?_, fun h₁ hne => ?_⟩
  · obtain ⟨a, ha, h1, h2⟩ := hlaw k hk
    have key : ∀ α g h₂, Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (t.pt j P₁)
        (t.pt (j + 1) P₂) (φ α) g (h₁ * k) h₂ = Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h)
        (t.pt j P₁) (t.pt (j + 1) P₂) (φ α) g h₁ h₂ := by
      intro α g h₂
      simp only [Chain.hand]
      have m1 : (t.sBF j (σ + 1) h).om (g, h₁ * k) (t.pt j P₁) = a⁻¹ • (t.sBF j (σ + 1) h).om (g, h₁) (t.pt j P₁) := by
        have hm : ((g, h₁ * k) : GA D (c.V j) × GA D (c.V (j + 1))) = (g, h₁) * (1, k) := by simp
        rw [hm, map_mul, Module.End.mul_apply, hs1om, h1, map_smul]
      have m2 : (t.sFB j σ h).om (h₁ * k, h₂) (t.pt (j + 1) P₂) = a • (t.sFB j σ h).om (h₁, h₂) (t.pt (j + 1) P₂) := by
        have hm : ((h₁ * k, h₂) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (h₁, h₂) * (k, 1) := by simp
        rw [hm, map_mul, Module.End.mul_apply, hs2om, h2, map_smul]
      rw [m1, m2, (HH (φ α)).1, inv_mul_cancel₀ ha, one_smul]
    funext h₂
    simp only [Tup.integrand, key]
  · by_contra hno
    push_neg at hno
    apply hne
    funext h₂
    simp only [Tup.integrand, Pi.zero_apply]
    refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun g hg => ?_
    have hflat : flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (g, h₁) (t.pt j P₁)) = 0 := by
      by_contra hf
      rw [hs1om] at hf
      obtain ⟨q, hq, hc⟩ := hsupp α g hg h₁ hf
      exact hno q hq hc
    simp only [Chain.hand, hflat, (HH (φ α)).2.1, per0, mul_zero]

theorem vanMany : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) P₁ P₂ (I : Type) [Fintype I] (s : I → 𝒯) (α : I → ℂ) (φ : ∀ i, (t (s i)).Ch j → GA D (c.X j) → ℂ) (f : I → GA D (c.V (j + 1 + 1)) → ℂ), (∀ i a, IsContAut (c.X j) (φ i a)) → (∀ i, RapidDec _ (f i)) → (∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂))) → (∀ a ∈ GinfC (c.V (j + 1)), ∀ a' ∈ GinfC (c.V (j + 1 + 1)), ∃ v : I → ℂ, (∀ i, Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ => (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) (a * q₁.1) (a' * q₂.1)) (v i)) ∧ ∑ i, α i * v i = 0) → ∑ i, α i * (t (s i)).perF j (σ + 1) h (φ i) (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕 (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 (f i) ((t (s i)).pt (j + 1) P₂)) ((t (s i)).pt j P₁)) = 0 := by
  classical
  intro D c 𝒯 t hDS hc ht hloc j σ h P₁ P₂ I _ s α φ f hφ hf hlift hV
  rcases isEmpty_or_nonempty I with hI | hI
  · simp
  obtain ⟨i₀⟩ := hI
  have hA := fun i => GlobalTheory.T.besselPeriod_double_step_iterated_quotient_integral D c (t (s i)) hDS hc (ht (s i)) j σ h P₁ P₂ (φ i) (f i) (hφ i) (hf i) (hlift i)
  choose F₁ hF₁ hF₂ using hA
  have hL := fun i => hloc (s i) j σ h P₁ P₂
  choose K₁ T₁ hK₁f hK₁c hK₁o hT₁ hlaw hsupp using hL
  have hIS := fun i => invsupp D c (t (s i)) (ht (s i)) j σ h P₁ P₂ (φ i) (f i) (K₁ i) (T₁ i) (hlaw i) (hsupp i)
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.V (j + 1))
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (c.V (j + 1 + 1))
  obtain ⟨gA₁, gB₁, gc₁, ge₁, gμ₁, gR₁⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))
  obtain ⟨gA₂, gB₂, gc₂, ge₂, gμ₂, gR₂⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))
  obtain ⟨⟨jsplit, -, jinvf⟩, -⟩ := gR₁ _ _ (c.jac j (σ + 1) h).d
  obtain ⟨-, bes⟩ := gR₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d
  obtain ⟨bsplit, -, binvf⟩ := bes _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o
  obtain ⟨jcl, jH, jI⟩ := GlobalTheory.QuotZero.jac_haar_inv (c.J j (σ + 1) h)
  obtain ⟨bcl, bH, bI⟩ := GlobalTheory.QuotZero.bes_haar_inv (c.B (j + 1 + 1) σ (idx_step h))
  have hQ1 := quot_lin α F₁ _ hF₁
  have hQ2 := fun h₁ => quot_lin α (fun i => (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) h₁) (fun i => F₁ i h₁)
    (fun i => hF₂ i h₁)
  refine GlobalTheory.T.quotient_integral_vanish_of_iterated_finite_integrals (GA D (c.V (j + 1))) (GA D (c.V (j + 1 + 1))) (GinfC _) (GfC _) (jacGrp (c.jac j (σ + 1) h).d)
    (GinfC _) (GfC _) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
    gA₁ gB₁ jcl gc₁ ge₁ jsplit gA₂ gB₂ bcl gc₂ ge₂ bsplit
    (c.J j (σ + 1) h).μR (c.vol (j + 1)).μ (c.ρJ j (σ + 1) h) (c.μf (j + 1))
    (c.B (j + 1 + 1) σ (idx_step h)).μR (c.vol (j + 1 + 1)).μ (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
    jH jI (c.vol (j + 1)).haar (hc.ρJ _ _ _) (jinvf _ (hc.ρJ _ _ _)) (hc.μf _) (gμ₁ _ (hc.μf _))
    bH bI (c.vol (j + 1 + 1)).haar (hc.ρB _ _ _) (binvf _ (hc.ρB _ _ _)) (hc.μf _)
    (⨅ i, K₁ i) (⋃ i, (K₁ i : Set (GA D (c.V (j + 1))))) (Finset.univ.biUnion T₁) ?_ ?_ ?_ ?_ ?_ ?_
    _ (fun h₁ h₂ => ∑ i, α i * (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) h₁ h₂) _ hQ1 hQ2 ?_ ?_ ?_
  · exact iInf_le_of_le i₀ (hK₁f i₀)
  · rw [Subgroup.coe_iInf]
    exact IsCompact.of_isClosed_subset (hK₁c i₀) (isClosed_iInter fun i => (hK₁c i).isClosed) (Set.iInter_subset _ i₀)
  · have e : (((⨅ i, K₁ i).subgroupOf (GfC (c.V (j + 1))) : Subgroup (GfC (c.V (j + 1)))) : Set (GfC (c.V (j + 1)))) =
        ⋂ i, (((K₁ i).subgroupOf (GfC (c.V (j + 1))) : Subgroup (GfC (c.V (j + 1)))) : Set (GfC (c.V (j + 1)))) := by
      ext x
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun i => hK₁o i
  · exact isCompact_iUnion fun i => hK₁c i
  · exact Set.iUnion_subset fun i => hK₁f i
  · intro q hq
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hq
    exact hT₁ i q hi
  · intro h₁ k hk
    funext h₂
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hIS i).1 h₁ k (Subgroup.mem_iInf.1 hk i)]
  · intro h₁ hne
    have : ∃ i, (t (s i)).integrand j σ h P₁ P₂ (φ i) (f i) h₁ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      funext h₂
      simp [hcon]
    obtain ⟨i, hi⟩ := this
    obtain ⟨q, hq, r, hr, a, ha, k, hk, e⟩ := (hIS i).2 h₁ hi
    exact ⟨q, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hq⟩, r, hr, a, ha, k, Set.mem_iUnion.2 ⟨i, hk⟩, e⟩
  · intro a ha a' ha'
    obtain ⟨v, hv, hsum⟩ := hV a ha a' ha'
    have := iteratedQuotientIntegral_finite_linearCombination (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) α _ v hv
    rw [hsum] at this
    exact this

end GlobalTheory.SeeSaw.VanMany
