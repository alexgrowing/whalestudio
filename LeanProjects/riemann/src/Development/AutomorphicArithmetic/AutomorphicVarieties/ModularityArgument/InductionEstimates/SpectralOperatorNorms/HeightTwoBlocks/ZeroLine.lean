import Mathlib

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

theorem cont_cpt {X Y : Type} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {h : X × Y → ℂ} (hc : Continuous h) : Continuous fun x => ∫ y, h (x, y) ∂ν := by
  have := continuous_parametric_integral_of_continuous (μ := ν) (f := fun x y => h (x, y)) hc isCompact_univ
  simpa only [Measure.restrict_univ] using this

theorem int_cpt {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] {h : Y → ℂ} (hc : Continuous h) : Integrable h ν :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)

theorem cont_loc {X Y : Type} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {h : X × Y → ℂ} (hc : Continuous h) (hb : ∀ C : Set X, IsCompact C → ∃ B : ℝ, ∀ y, ∀ x ∈ C, ‖h (x, y)‖ ≤ B) :
    Continuous fun x => ∫ y, h (x, y) ∂ν := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨B, hB⟩ := hb C hC
  refine continuousAt_of_dominated (bound := fun _ => B) (Eventually.of_forall fun x => ?_) ?_ (integrable_const B)
    (ae_of_all _ fun y => (hc.comp (by fun_prop)).continuousAt)
  · exact (hc.comp (Continuous.prodMk_right x)).aestronglyMeasurable
  · filter_upwards [hx] with x hx using ae_of_all _ fun y => hB y x hx

theorem indSec {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    (S Kc : Subgroup G) (hS : IsClosed (S : Set G)) (hK : IsCompact (Kc : Set G)) (hs : ∀ g, ∃ p ∈ S, ∃ k ∈ Kc, g = p * k)
    (π : S →* M) (hπ : Continuous π) (F : M → ℂ) (hF : Continuous F) (ψ : G → ℂ) (hψ : Continuous ψ)
    (lam : Measure (S ⊓ Kc : Subgroup G)) [IsFiniteMeasure lam] [lam.IsMulLeftInvariant] :
    ∃ f : G → ℂ, Continuous f ∧ ∀ (p : S), ∀ k ∈ Kc,
      f (p * k) = ∫ u : (S ⊓ Kc : Subgroup G), F (π p * π ⟨u, u.2.1⟩) * ψ ((u : G)⁻¹ * k) ∂lam := by
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.1 hK
  haveI : CompactSpace (S ⊓ Kc : Subgroup G) := isCompact_iff_compactSpace.1 (hK.inter_left hS)
  haveI : LocallyCompactSpace S := hS.locallyCompactSpace
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (S ⊓ Kc : Subgroup G) := TopologicalSpace.Subtype.secondCountableTopology _
  choose p hp k hk he using hs
  set Φ : S × G → ℂ := fun q => ∫ u : (S ⊓ Kc : Subgroup G), F (π q.1 * π ⟨u, u.2.1⟩) * ψ ((u : G)⁻¹ * q.2) ∂lam with hΦ
  have hc : Continuous Φ := by
    refine cont_cpt lam (h := fun z : (S × G) × (S ⊓ Kc : Subgroup G) => F (π z.1.1 * π ⟨z.2, z.2.2.1⟩) * ψ ((z.2 : G)⁻¹ * z.1.2)) ?_
    have : Continuous fun z : (S × G) × (S ⊓ Kc : Subgroup G) => (⟨z.2, z.2.2.1⟩ : S) :=
      (continuous_subtype_val.comp continuous_snd).subtype_mk _
    fun_prop
  have hw : ∀ (q : S), ∀ c ∈ Kc, Φ (⟨p (q * c), hp _⟩, k (q * c)) = Φ (q, c) := by
    intro q c hc
    have e := he (q * c)
    have e1 : (q : G)⁻¹ * p (q * c) = c * (k (q * c))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]; exact e.symm
    let u₀ : (S ⊓ Kc : Subgroup G) := ⟨(q : G)⁻¹ * p (q * c), S.mul_mem (S.inv_mem q.2) (hp _), e1 ▸ Kc.mul_mem hc (Kc.inv_mem (hk _))⟩
    simp only [hΦ]
    rw [← integral_mul_left_eq_self (fun u : (S ⊓ Kc : Subgroup G) => F (π q * π ⟨u, u.2.1⟩) * ψ ((u : G)⁻¹ * c)) u₀]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    have a1 : π q * π ⟨(u₀ * u : (S ⊓ Kc : Subgroup G)), (u₀ * u).2.1⟩ = π ⟨p (q * c), hp _⟩ * π ⟨u, u.2.1⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (by show (q : G) * ((q : G)⁻¹ * p (q * c) * u) = p (q * c) * u; group))
    have a2 : ((u₀ * u : (S ⊓ Kc : Subgroup G)) : G)⁻¹ * c = (u : G)⁻¹ * k (q * c) := by
      show ((q : G)⁻¹ * p (q * c) * u)⁻¹ * c = _
      rw [e1]; group
    simp only [a1, a2]
  refine ⟨fun g => Φ (⟨p g, hp g⟩, k g), ?_, fun q c hc => hw q c hc⟩
  have hm : Continuous fun z : S × Kc => (z.1 : G) * z.2 := by fun_prop
  have hcl : IsClosedMap fun z : S × Kc => (z.1 : G) * z.2 := by
    have h1 : IsClosedMap (Prod.map (Subtype.val : S → G) (id : Kc → Kc)) :=
      (hS.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id).isClosedMap
    let e : G × Kc ≃ₜ G × Kc :=
      { toFun := fun z => (z.1 * z.2, z.2), invFun := fun z => (z.1 * (z.2 : G)⁻¹, z.2)
        left_inv := fun z => by simp, right_inv := fun z => by simp }
    exact (isClosedMap_fst_of_compactSpace.comp e.isClosedMap).comp h1
  have hq := hcl.isQuotientMap hm fun g => ⟨(⟨p g, hp g⟩, ⟨k g, hk g⟩), (he g).symm⟩
  rw [hq.continuous_iff]
  have : (fun g => Φ (⟨p g, hp g⟩, k g)) ∘ (fun z : S × Kc => (z.1 : G) * z.2) = fun z => Φ (z.1, z.2) :=
    funext fun z => hw z.1 z.2 z.2.2
  rw [this]
  fun_prop

theorem fub5 {A B T K N : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace T] [MeasurableSpace K] [MeasurableSpace N]
    (a : Measure A) (b : Measure B) (c : Measure T) (d : Measure K) (e : Measure N) [SFinite a] [SFinite b] [SFinite c] [SFinite d]
    [SFinite e] (Ψ : A × B × T × K × N → ℂ) (h : Integrable Ψ (a.prod (b.prod (c.prod (d.prod e))))) :
    ∫ p, Ψ p ∂a.prod (b.prod (c.prod (d.prod e))) = ∫ t, ∫ k, ∫ m : A × B, ∫ x, Ψ (m.1, m.2, t, k, x) ∂e ∂a.prod b ∂d ∂c := by
  have m1 := measurePreserving_prodAssoc (a.prod b) (c.prod d) e
  have m2 : MeasurePreserving ((MeasurableEquiv.refl (A × B)).prodCongr (MeasurableEquiv.prodAssoc (α := T) (β := K) (γ := N)))
      ((a.prod b).prod ((c.prod d).prod e)) ((a.prod b).prod (c.prod (d.prod e))) :=
    (MeasurePreserving.id _).prod (measurePreserving_prodAssoc c d e)
  have m3 := measurePreserving_prodAssoc a b (c.prod (d.prod e))
  have m := (m1.trans m2).trans m3
  have h1 := (m.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h
  rw [← m.integral_comp', show (fun x => Ψ _) = Ψ ∘ _ from rfl, integral_prod _ h1, integral_prod_symm _ h1.integral_prod_left,
    integral_prod _ h1.integral_prod_left.integral_prod_right]
  rfl

theorem zero_line (J : ℝ → ℂ) (hJ : Continuous J) (h : ∀ β : ℝ → ℂ, Continuous β → HasCompactSupport β →
    ∫ t, conj (β t * Complex.exp ((2 * t : ℝ) : ℂ)) * J t
      ∂(volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal (Real.exp (-4 * t))) = 0) (t₀ : ℝ) : J t₀ = 0 := by
  by_contra h0
  obtain ⟨b, hb1, -, hbc, hb⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := t₀)) isClosed_empty
    (disjoint_empty _)
  have hs : HasCompactSupport fun t => (b t : ℂ) * J t := (hbc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right
  have := h (fun t => b t * J t) (by fun_prop) hs
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at this
  have e : ∀ t, (ENNReal.ofReal (Real.exp (-4 * t))).toReal • (conj ((b t : ℂ) * J t * Complex.exp ((2 * t : ℝ) : ℂ)) * J t) =
      ((b t * (Real.exp (-4 * t) * Real.exp (2 * t) * Complex.normSq (J t)) : ℝ) : ℂ) := by
    intro t
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Complex.ofReal_exp, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.real_smul]
    simp only [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  simp only [e] at this
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at this
  have hn := Complex.continuous_normSq
  refine ne_of_gt (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := t₀)
    (f := fun t => b t * (Real.exp (-4 * t) * Real.exp (2 * t) * Complex.normSq (J t))) (by fun_prop) hbc.mul_right
    (fun t => mul_nonneg (hb t).1 (mul_nonneg (by positivity) (Complex.normSq_nonneg _))) ?_) this
  have : b t₀ = 1 := hb1 rfl
  rw [this, one_mul]
  exact mul_ne_zero (by positivity) (by simpa using h0)

theorem zero_cpt {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    [ν.IsOpenPosMeasure] {h : Y → ℂ} (hc : Continuous h) (h0 : ∫ y, conj (h y) * h y ∂ν = 0) (y : Y) : h y = 0 := by
  by_contra hy
  simp only [← Complex.normSq_eq_conj_mul_self] at h0
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h0
  exact ne_of_gt (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := y) (f := fun y => Complex.normSq (h y))
    (Complex.continuous_normSq.comp hc)
    (HasCompactSupport.of_compactSpace _) (fun t => Complex.normSq_nonneg _) (by simpa using hy)) h0

theorem avg_cpt {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (U Kc : Subgroup G) [CompactSpace U] [CompactSpace Kc] (hU : U ≤ Kc) (lam : Measure U) [IsProbabilityMeasure lam]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsMulLeftInvariant] (h : G → ℂ) (hc : Continuous h) :
    ∫ k : Kc, ∫ u : U, h ((u : G)⁻¹ * k) ∂lam ∂κ = ∫ k : Kc, h k ∂κ := by
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  rw [integral_integral_swap (int_cpt _ (by fun_prop))]
  have : ∀ u : U, ∫ k : Kc, h ((u : G)⁻¹ * k) ∂κ = ∫ k : Kc, h k ∂κ := fun u =>
    integral_mul_left_eq_self (fun k : Kc => h k) (⟨u, hU u.2⟩⁻¹ : Kc)
  simp [this]

theorem swap_sec {M U : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace U] [CompactSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (ν : Measure M) [IsFiniteMeasure ν] (lam : Measure U) [IsFiniteMeasure lam] (F : M × U → ℂ) (c : U → ℂ) (W : M → ℂ)
    (hF : Continuous F) (hc : Continuous c) (hW : Continuous W) (B : ℝ) (hB : ∀ m u, ‖F (m, u)‖ * ‖W m‖ ≤ B) :
    ∫ m, conj (∫ u, F (m, u) * c u ∂lam) * W m ∂ν = ∫ u, conj (c u) * ∫ m, conj (F (m, u)) * W m ∂ν ∂lam := by
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hi : Integrable (Function.uncurry fun m u => conj (c u) * (conj (F (m, u)) * W m)) (ν.prod lam) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (D * B) (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hD _ trivial) (hB _ _) (by positivity) ((norm_nonneg _).trans (hD z.2 trivial))
  simp only [← integral_const_mul]
  rw [← integral_integral_swap hi]
  refine integral_congr_ae (ae_of_all _ fun m => ?_)
  simp only [← integral_conj, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [map_mul]
  ring

theorem fix_swap {G Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure G) [IsFiniteMeasure ν]
    (U : Set G) (hU : IsCompact U) (hν : ∀ᵐ k ∂ν, k ∈ U) (e : G → ℂ) (he : Continuous e) (ρ : Measure Y) [IsFiniteMeasure ρ]
    (H : G × Y → ℂ) (hH : Continuous H) (hb : ∀ C : Set G, IsCompact C → ∃ B : ℝ, ∀ᵐ y ∂ρ, ∀ x ∈ C, ‖H (x, y)‖ ≤ B)
    (g : G) (hf : ∀ y, ∫ k, e k * H (g * k, y) ∂ν = H (g, y)) :
    ∫ k, e k * ∫ y, H (g * k, y) ∂ρ ∂ν = ∫ y, H (g, y) ∂ρ := by
  obtain ⟨B, hB⟩ := hb _ (hU.image (continuous_const_mul g))
  obtain ⟨D, hD⟩ := hU.exists_bound_of_continuousOn he.continuousOn
  have hi : Integrable (Function.uncurry fun k y => e k * H (g * k, y)) (ν.prod ρ) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (D * B) ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν, Measure.quasiMeasurePreserving_snd.ae hB] with z h1 h2
    simp only [Function.uncurry, norm_mul]
    exact mul_le_mul (hD _ h1) (h2 _ ⟨_, h1, rfl⟩) (norm_nonneg _) ((norm_nonneg _).trans (hD _ h1))
  simp only [← integral_const_mul]
  rw [integral_integral_swap hi]
  simp only [hf]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX
