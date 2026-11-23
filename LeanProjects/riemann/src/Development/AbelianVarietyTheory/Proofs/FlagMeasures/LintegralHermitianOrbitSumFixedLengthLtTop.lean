import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelicUnitaryComplementRangeStabiliser
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReflection
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal Pointwise

noncomputable section

namespace GlobalTheory.OrbitSumInt

theorem exists_compact_reach {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousSMul G X] (x0 : X) (hcl : IsClosed (MulAction.orbit G x0))
    (K : Set X) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0 := by
  let O := MulAction.orbit G x0
  have : LocallyCompactSpace O := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul G O := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  let o0 : O := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hopen : IsOpenMap (fun g : G => g • o0) := isOpenMap_smul_of_sigmaCompact o0
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set O) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have key : ∃ C : Set G, IsCompact C ∧ (Subtype.val ⁻¹' K : Set O) ⊆ (fun g : G => g • o0) '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set G, IsCompact C ∧ s ⊆ (fun g : G => g • o0) '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · rintro ⟨_, g, rfl⟩ -
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, h⟩ := key
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨c, hc, e⟩ := h (a := g • o0) hg
  exact ⟨c, hc, congrArg Subtype.val e⟩

theorem lintegral_count_lt_top {G H X S : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [MulAction G X]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (Δ : Subgroup H) [Countable Δ] (𝓕 : Set G) (𝓖 : Set H)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hG : IsFundamentalDomain Δ 𝓖 ν) (hfin : ν 𝓖 < ⊤)
    (φ : H →* G) (hφ : Continuous φ) (hinj : Function.Injective φ) (x0 : X)
    (hr : φ.range = MulAction.stabilizer G x0) (hΔ : ∀ δ ∈ Δ, φ δ ∈ Γ)
    (ι : S → X) (hι : Function.Injective ι) (γ : S → Γ) (hγ : ∀ s, (γ s : G) • x0 = ι s)
    (K : Set X) (C : Set G) (hC : IsCompact C) (hKC : ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0) :
    ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Δ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Δ ν
  obtain ⟨U, hU, hU1⟩ := exists_compact_mem_nhds (1 : H)
  have hU0 : ν U ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hU1).ne'
  set D : Set G := (φ '' U)⁻¹ * C⁻¹ with hD
  have hDc : IsCompact D := (hU.image hφ).inv.mul hC.inv
  let f : G → ℝ≥0∞ := D.indicator 1
  have hf : Measurable f := measurable_one.indicator hDc.measurableSet
  let T : G → ℝ≥0∞ := fun g => ∫⁻ k in 𝓖, f ((φ k)⁻¹ * g) ∂ν
  have hm : Measurable fun p : G × H => f ((φ p.2)⁻¹ * p.1) :=
    hf.comp ((hφ.comp continuous_snd).inv.mul continuous_fst).measurable
  have hT : Measurable T := hm.lintegral_prod_right'
  have hfix : ∀ k, φ k • x0 = x0 := fun k => by
    have : φ k ∈ MulAction.stabilizer G x0 := hr ▸ ⟨k, rfl⟩
    exact this
  let j : S × Δ → Γ := fun p => γ p.1 * ⟨φ p.2, hΔ _ p.2.2⟩
  have hj : Function.Injective j := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    have h1 : (γ s : G) * φ a = γ t * φ b := congrArg Subtype.val h
    have h2 : s = t := hι (by rw [← hγ, ← hγ, ← hfix a, ← mul_smul, h1, mul_smul, hfix, hfix])
    subst h2
    rw [Subtype.ext (hinj (mul_left_cancel h1))]
  have step : ∀ (h : G) (s : S), ν U * K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ≤
      ∑' δ : Δ, T ((j (s, δ))⁻¹ • h) := by
    intro h s
    by_cases hK : h⁻¹ • ι s ∈ K
    swap
    · simp [Set.indicator_of_notMem hK]
    rw [Set.indicator_of_mem hK, Pi.one_apply, mul_one]
    rw [← hγ, ← mul_smul] at hK
    obtain ⟨c, hc, e⟩ := hKC _ hK
    obtain ⟨k, hk⟩ : c⁻¹ * (h⁻¹ * γ s) ∈ φ.range := by
      rw [hr, MulAction.mem_stabilizer_iff, mul_smul, ← e, inv_smul_smul]
    have e1 := hG.lintegral_eq_tsum'' fun k' => f ((φ k')⁻¹ * ((γ s : G)⁻¹ * h))
    have e2 : ∀ δ : Δ, T ((j (s, δ))⁻¹ • h) =
        ∫⁻ k' in 𝓖, f ((φ (δ • k'))⁻¹ * ((γ s : G)⁻¹ * h)) ∂ν := fun δ => by
      refine lintegral_congr fun k' => ?_
      congr 1
      simp [j, Subgroup.smul_def, mul_assoc]
    simp only [e2]
    rw [← e1, ← measure_preimage_mul ν k U, ← lintegral_indicator_one
      ((measurable_const_mul k) hU.measurableSet)]
    refine lintegral_mono fun k' => ?_
    by_cases hk' : k' ∈ (fun x => k * x) ⁻¹' U
    swap
    · simp [Set.indicator_of_notMem hk']
    have : (φ k')⁻¹ * ((γ s : G)⁻¹ * h) ∈ D := by
      refine ⟨(φ (k * k'))⁻¹, Set.inv_mem_inv.2 ⟨_, hk', rfl⟩, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
      simp [hk, mul_assoc]
    simp [f, Set.indicator_of_mem hk', Set.indicator_of_mem this]
  have main : ν U * ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ ≤ μ D * ν 𝓖 := by
    rw [← lintegral_const_mul' _ _ hU.measure_lt_top.ne]
    calc _ ≤ ∫⁻ h in 𝓕, ∑' g : Γ, T (g⁻¹ • h) ∂μ := by
          refine lintegral_mono fun h => ?_
          rw [← ENNReal.tsum_mul_left]
          refine (ENNReal.tsum_le_tsum (step h)).trans ?_
          rw [← ENNReal.tsum_prod (f := fun s δ => T ((j (s, δ))⁻¹ • h))]
          exact ENNReal.tsum_comp_le_tsum_of_injective hj fun g => T (g⁻¹ • h)
      _ = ∫⁻ g, T g ∂μ := by
          rw [hF.lintegral_eq_tsum']
          exact lintegral_tsum fun g => (hT.comp (measurable_const_smul g⁻¹)).aemeasurable
      _ = ∫⁻ k in 𝓖, μ D ∂ν := by
          rw [lintegral_lintegral_swap hm.aemeasurable]
          refine lintegral_congr fun k => ?_
          rw [lintegral_mul_left_eq_self f, lintegral_indicator_one hDc.measurableSet]
      _ = μ D * ν 𝓖 := by simp
  by_contra htop
  rw [not_lt_top_iff.1 htop, ENNReal.mul_top hU0] at main
  exact (ENNReal.mul_lt_top hDc.measure_lt_top hfin).not_ge main

open GlobalTheory.GaugeEx in

theorem lintegral_orbitSum_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : F), β ≠ 0 → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∫⁻ h in 𝓕, ∑' x : {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β}, ‖Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))‖ₑ ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ β hβ Φ hΦ hK μ 𝓕 hμ h𝓕
  rcases isEmpty_or_nonempty {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β} with he | ⟨⟨x0, hx0⟩⟩
  · simp
  have hx0 : hE σ J (x0 0) (x0 0) = algebraMap F E β := hx0
  have hβ' : algebraMap F E β ≠ 0 := by simpa using hβ
  have hxx : hE σ J (x0 0) (x0 0) ≠ 0 := hx0 ▸ hβ'
  obtain _ | M := M
  · exact (hxx (by simp [hE, Formalism.UG.hform])).elim
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hθ : ∃ θ : E, IsUnit (θ - (σ : E →+* E) θ) := by
    by_contra hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hCM.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := by
      by_contra hz
      exact hc ⟨z, (sub_ne_zero.2 (Ne.symm hz)).isUnit⟩
    have := hCM.2.2.2 τ z
    rw [hz] at this
    exact this.symm
  obtain ⟨a, B, J', -, -, -, hxB, hBB, hJ'⟩ := GlobalTheory.AdelicStabUnimod.exists_stepData hCM hJ x0 hxx
  obtain ⟨φ, hφ, hinj, hr, -, hrat⟩ := GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser F E σ hCM (M + 1) M
    J J' B x0 rfl hJ hJ' hBB.symm hxB hxx
  let ν : Measure (HA (AF F) σ J') := Measure.haar
  have hν : ν.IsHaarMeasure := inferInstance
  obtain ⟨𝓖, h𝓖⟩ := (GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J' ν hν).1
  have hfin : ν 𝓖 < ⊤ := GlobalTheory.Mem.VolFin.finVol F E σ hCM M J' hJ' ν hν 𝓖 h𝓖
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  have horb : MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0) =
      {y | qR (AF F) σ J (y 0) = algebraMap F (AF F) β} := by
    ext y
    refine ⟨?_, fun hy => GlobalTheory.AdelicWitt.witt_adelic F E σ hCM _ J x0 β hJ hβ hx0 y hy⟩
    rintro ⟨g, rfl⟩
    rw [Set.mem_setOf_eq, ← GlobalTheory.AdelicWitt.qR_ratTup b (AF F) σ J x0 β hx0]
    exact congrArg (fun z => algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z)
      (GlobalTheory.StabOrbit.hR_act (AF F) σ J g _ _)
  have hcl : IsClosed (MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0)) := by
    rw [horb]
    refine isClosed_eq ?_ continuous_const
    have h1 : Continuous (Algebra.trace (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap _
    have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
    unfold qR hR Formalism.UG.hform
    refine continuous_const.mul (h1.comp ?_)
    fun_prop
  obtain ⟨C, hC, hKC⟩ := exists_compact_reach _ hcl _ hK
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  let Δ : Subgroup (HA (AF F) σ J') := HFinIn (AF F) σ J'
  have : Countable Γ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : Countable Δ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J'
  have hγ : ∀ s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β},
      ∃ γ : Γ, (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) x0 = ratTup (F := F) (AF F) s.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, e⟩ := GlobalTheory.WittTransitivity.witt_transitive E (σ : E →+* E) hσ
      (fun a _ ha => ha.isUnit) two_ne_zero.isUnit three_ne_zero hθ _ J hJ.1 hJ.2.isUnit (x0 0) (x 0)
      (hx0.trans (Eq.symm hx)) hxx.isUnit
    have hm : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J := by
      have hg' : Formalism.UG.cT (σ : E →+* E) g.1 * J * g.1 = J := hg
      have h1 := congrArg (·.map (inclR (F := F) (AF F))) hg'
      simp only [Matrix.map_mul] at h1
      exact h1
    refine ⟨⟨(⟨_, hm⟩ : HR (AF F) σ J), ⟨g, hg, rfl⟩⟩, ?_⟩
    funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    change _ = inclR (F := F) (AF F) (x 0 i)
    rw [← e, RingHom.map_mulVec]
    rfl
  choose γ hγ using hγ
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have hι : Function.Injective fun s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β} =>
      ratTup (F := F) (AF F) s.1 := fun s t h => Subtype.ext (funext fun k => funext fun i =>
    (inclR (F := F) (E := E) (AF F)).injective (congrFun (congrFun h k) i))
  have key := lintegral_count_lt_top μ ν Γ Δ 𝓕 𝓖 h𝓕 h𝓖 hfin φ hφ hinj (ratTup (F := F) (AF F) x0) hr
    (fun δ hδ => (hrat δ).2 hδ) _ hι γ hγ (tsupport Φ) C hC hKC
  obtain ⟨A, hA⟩ := hΦ.bounded_above_of_compact_support hK
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := A)) key)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun h => ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : h⁻¹ • ratTup (F := F) (AF F) s.1 ∈ tsupport Φ
  · rw [Set.indicator_of_mem hs, Pi.one_apply, mul_one, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hA _)
  · simp [image_eq_zero_of_notMem_tsupport hs]

end GlobalTheory.OrbitSumInt
