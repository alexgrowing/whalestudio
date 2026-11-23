import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FdomExistsAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariant

open MeasureTheory in
theorem UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ] (C : Set G), IsCompact C → (∀ g, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c) → ∃ B : (G → ℂ) →ₗ⋆[ℂ] (G → ℂ) →ₗ[ℂ] ℂ, (∀ φ : G → ℂ, Continuous φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → B φ φ = 0 → φ = 0) ∧ ∀ (x : G) (φ ψ : G → ℂ), Continuous φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) → B (fun g => φ (g * x)) (fun g => ψ (g * x)) = B φ ψ := by
  intro G _ _ _ _ _ _ Γ _ C hC hcov
  classical
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure G, μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨𝓕, -, h𝓕'⟩ := Formalism.IndefR.Eqv.G5.fdom_exists_all Γ
  have h𝓕 := h𝓕' μ
  have hfin : μ 𝓕 < ⊤ := by
    refine lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := μ))
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro g hg
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hg⟩
  obtain ⟨-, hR, -⟩ := GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G Γ μ 𝓕 h𝓕 hfin
  have hright : ∀ (y : G) (u : G → ℂ), (∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) →
      ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
    intro y u hu
    have h' : IsFundamentalDomain Γ ((fun h => h * y) '' 𝓕) μ := by
      refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
      · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
      · intro γ h
        simp [Subgroup.smul_def, mul_assoc]
    rw [h𝓕.setIntegral_eq h' (f := u) (fun γ h => hu γ γ.2 h)]
    exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
      (measurableEmbedding_mulRight y) u 𝓕).symm
  let N : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp [ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp [ha.2 γ hγ g]⟩ }
  have hRN : ∀ k : G, ∀ φ ∈ N, (fun g => φ (g * k)) ∈ N := by
    intro k φ h
    refine ⟨h.1.comp (continuous_mul_const k), fun γ hγ g => ?_⟩
    show φ (γ * g * k) = φ (g * k)
    rw [mul_assoc, h.2 γ hγ]
  have hI : ∀ x ∈ N, ∀ y ∈ N, IntegrableOn (fun g => star (x g) * y g) 𝓕 μ := by
    intro x hx y hy
    have hc : Continuous (fun g => star (x g) * y g) := hx.1.star.mul hy.1
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne hc.aestronglyMeasurable (ae_of_all _ fun g => ?_)
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    rw [hx.2 γ hγ, hy.2 γ hγ]
    exact hM c hc
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl N
  let P : (G → ℂ) →ₗ[ℂ] N := Submodule.projectionOnto N q hq
  have hPN : ∀ T, ((P T : N) : G → ℂ) ∈ N := fun T => (P T).2
  have hPid : ∀ T ∈ N, ((P T : N) : G → ℂ) = T := fun T hT =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨T, hT⟩)
  let F : (G → ℂ) → (G → ℂ) → ℂ := fun x y => ∫ g in 𝓕, star ((P x).1 g) * (P y).1 g ∂μ
  let B : (G → ℂ) →ₗ⋆[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F, map_add, Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x') _ (hPN y))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F, map_add, Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x) _ (hPN y'))]
      congr 1
      funext g
      simp only [Pi.add_apply, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring)
  have hB : ∀ x ∈ N, ∀ y ∈ N, B x y = ∫ g in 𝓕, star (x g) * y g ∂μ := by
    intro x hx y hy
    show F x y = _
    simp only [F, hPid x hx, hPid y hy]
  refine ⟨B, ?_, ?_⟩
  · intro T hT1 hT2 h0
    have hT : T ∈ N := ⟨hT1, hT2⟩
    rw [hB _ hT _ hT] at h0
    have hre : ∫ g in 𝓕, star (T g) * T g ∂μ = ((∫ g in 𝓕, ‖T g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    rw [hre, Complex.ofReal_eq_zero] at h0
    have hi : IntegrableOn (fun g => ‖T g‖ ^ 2) 𝓕 μ := by
      have := (hI T hT T hT).norm
      have e2 : (fun g => ‖star (T g) * T g‖) = fun g => ‖T g‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 h0
    have := GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant Γ μ 𝓕 h𝓕 T hT1 hT2 (by
      filter_upwards [hae] with g hg
      simpa using hg)
    first | exact this | exact funext this
  · intro k T T' h1 h2 h3 h4
    have hT : T ∈ N := ⟨h1, h2⟩
    have hT' : T' ∈ N := ⟨h3, h4⟩
    rw [hB _ (hRN k T hT) _ (hRN k T' hT'), hB _ hT _ hT']
    exact hright k (fun g => star (T g) * T' g) (fun γ hγ g => by simp only [h2 γ hγ, h4 γ hγ])
