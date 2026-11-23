import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.ZeroLine

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

theorem transl {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {D : Set G}
    (hF : IsFundamentalDomain Γ D μ) (h : G → ℂ) (hh : ∀ γ ∈ Γ, ∀ m, h (γ * m) = h m) (x : G) :
    ∫ m in D, h (m * x) ∂μ = ∫ m in D, h m ∂μ := by
  have hF' : IsFundamentalDomain Γ ((· * x) ⁻¹' D) μ :=
    hF.preimage_of_equiv (measurePreserving_mul_right μ x).quasiMeasurePreserving (e := id) Function.bijective_id
      fun γ y => mul_assoc (γ : G) y x
  rw [hF.setIntegral_eq hF' (f := fun m => h (m * x)) fun γ y => by
    show h (γ * y * x) = _
    rw [mul_assoc, hh _ γ.2]]
  exact (measurePreserving_mul_right μ x).setIntegral_preimage_emb (MeasurableEquiv.mulRight x).measurableEmbedding h _

theorem transl2 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {D : Set G}
    (hF : IsFundamentalDomain Γ D μ) [IsFiniteMeasure (μ.restrict D)] (h : G × G → ℂ) (hc : Continuous h) (B : ℝ)
    (hB : ∀ m, ‖h m‖ ≤ B) (hh : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, ∀ a b, h (γ₁ * a, γ₂ * b) = h (a, b)) (x : G × G) :
    ∫ m, h (m * x) ∂(μ.restrict D).prod (μ.restrict D) = ∫ m, h m ∂(μ.restrict D).prod (μ.restrict D) := by
  rw [integral_prod (fun m => h (m * x))
      (Integrable.of_bound (hc.comp (continuous_mul_const x)).aestronglyMeasurable B (ae_of_all _ fun _ => hB _)),
    integral_prod _ (Integrable.of_bound hc.aestronglyMeasurable B (ae_of_all _ fun _ => hB _)),
    ← transl Γ μ hF (fun a => ∫ b in D, h (a, b) ∂μ) (fun γ hγ a => by
      simpa only [one_mul] using congrArg (fun f => ∫ b in D, f b ∂μ) (funext fun b => hh γ hγ 1 (one_mem _) a b)) x.1]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  exact transl Γ μ hF (fun b => h (a * x.1, b)) (fun γ hγ b => by simpa only [one_mul] using hh 1 (one_mem _) γ hγ (a * x.1) b) x.2

theorem absI {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) [IsFiniteMeasure ν]
    (l : M → G) (hl : Continuous l) (F : M → ℂ) (hF : Continuous F) (W : G → ℂ) (hW : Continuous W)
    (hb : ∀ C : Set G, IsCompact C → ∃ B : ℝ, ∀ m, ∀ g ∈ C, ‖F m‖ * ‖W (l m * g)‖ ≤ B)
    (ρ : Measure G) [IsFiniteMeasure ρ] (U : Set G) (hU : IsCompact U) (hρ : ∀ᵐ k ∂ρ, k ∈ U) (e : G → ℂ) (he : Continuous e)
    (hf : ∀ g, ∫ k, e k * W (g * k) ∂ρ = W g) :
    (∀ g, Integrable (fun m => conj (F m) * W (l m * g)) ν) ∧ Continuous (fun g => ∫ m, conj (F m) * W (l m * g) ∂ν) ∧
      ∀ g, ∫ k, e k * ∫ m, conj (F m) * W (l m * (g * k)) ∂ν ∂ρ = ∫ m, conj (F m) * W (l m * g) ∂ν := by
  have hH : Continuous fun z : G × M => conj (F z.2) * W (l z.2 * z.1) := by fun_prop
  have hHb : ∀ C : Set G, IsCompact C → ∃ B : ℝ, ∀ m, ∀ g ∈ C, ‖conj (F m) * W (l m * g)‖ ≤ B := fun C hC => by
    simpa only [norm_mul, RCLike.norm_conj] using hb C hC
  refine ⟨fun g => ?_, cont_loc ν hH hHb, fun g => fix_swap ρ U hU hρ e he ν _ hH (fun C hC => ?_) g fun m => ?_⟩
  · obtain ⟨B, hB⟩ := hHb _ (isCompact_singleton (x := g))
    exact Integrable.of_bound (hH.comp (Continuous.prodMk_right _)).aestronglyMeasurable B (ae_of_all _ fun m => hB m _ rfl)
  · obtain ⟨B, hB⟩ := hHb C hC
    exact ⟨B, ae_of_all _ hB⟩
  · simp only
    rw [← hf (l m * g), ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun h => by simp only [mul_assoc]; ring)

theorem absMain {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (ν : Measure M) [IsFiniteMeasure ν] (Kc U : Subgroup G) [CompactSpace Kc] [CompactSpace U]
    (hUK : U ≤ Kc) (κ : Measure Kc) [κ.IsHaarMeasure] (lam : Measure U) [IsProbabilityMeasure lam]
    (l : M → G) (hl : Continuous l) (a : ℝ → G) (ha : Continuous a) (F : M → ℂ) (hF : Continuous F) (W : G → ℂ) (hW : Continuous W)
    (hb : ∀ C : Set G, IsCompact C → ∃ B : ℝ, ∀ m, ∀ g ∈ C, ‖F m‖ * ‖W (l m * g)‖ ≤ B) (x : U → M) (hx : Continuous x)
    (key : ∀ (u : U) m t k, W (l m * (a t * k)) = W (l (m * x u) * (a t * ((u : G)⁻¹ * k))))
    (I : G → ℂ) (hI : ∀ g, I g = ∫ m, conj (F m) * W (l m * g) ∂ν) (hIc : Continuous I)
    (htr : ∀ g y, ∫ m, conj (F (m * y)) * W (l (m * y) * g) ∂ν = I g) (t₀ : ℝ) (f : G → ℂ)
    (hv : ∀ m (k : Kc), f (l m * k) = ∫ u : U, F (m * x u) * I (a t₀ * ((u : G)⁻¹ * k)) ∂lam)
    (h0 : ∀ β : ℝ → ℂ, Continuous β → HasCompactSupport β →
      ∫ t, ∫ k : Kc, ∫ m, conj (β t * Complex.exp ((2 * t : ℝ) : ℂ) * f (l m * k)) * W (l m * (a t * k)) ∂ν ∂κ
        ∂(volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal (Real.exp (-4 * t))) = 0) (k₀ : Kc) : I (a t₀ * k₀) = 0 := by
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology Kc := TopologicalSpace.Subtype.secondCountableTopology _
  have hK : IsCompact (Kc : Set G) := isCompact_iff_compactSpace.2 ‹_›
  have inner : ∀ (t : ℝ) (k : Kc), ∫ m, conj (f (l m * k)) * W (l m * (a t * k)) ∂ν =
      ∫ u : U, conj (I (a t₀ * ((u : G)⁻¹ * k))) * I (a t * ((u : G)⁻¹ * k)) ∂lam := by
    intro t k
    obtain ⟨B, hB⟩ := hb _ (hK.image (continuous_const_mul (a t)))
    simp only [hv]
    rw [swap_sec ν lam (fun z : M × U => F (z.1 * x z.2)) (fun u => I (a t₀ * ((u : G)⁻¹ * k))) (fun m => W (l m * (a t * k)))
      (by fun_prop) (by fun_prop) (by fun_prop) B fun m u => by
        rw [key u]
        exact hB _ _ ⟨_, mul_mem (inv_mem (hUK u.2)) k.2, rfl⟩]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    rw [← htr (a t * ((u : G)⁻¹ * k)) (x u)]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun m => by simp only [← key u])
  refine zero_cpt κ (h := fun k : Kc => I (a t₀ * k)) (by fun_prop) (zero_line (fun t => ∫ k : Kc, conj (I (a t₀ * k)) * I (a t * k) ∂κ)
    (cont_cpt κ (h := fun z : ℝ × Kc => conj (I (a t₀ * z.2)) * I (a z.1 * z.2)) (by fun_prop)) (fun β hβ hβc => ?_) t₀) k₀
  rw [← h0 β hβ hβc]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [← avg_cpt U _ hUK lam κ (fun g => conj (I (a t₀ * g)) * I (a t * g)) (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only
  rw [← inner t k, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun m => ?_)
  simp only [map_mul, mul_assoc]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX
