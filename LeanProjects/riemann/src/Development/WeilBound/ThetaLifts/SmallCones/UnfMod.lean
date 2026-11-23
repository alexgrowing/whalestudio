import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ModulusCharacterUnitActionProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitsDecompositionFlowCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnitsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelicStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberFieldStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.Doubling (absE)

noncomputable section

namespace PositivityTheory.ThKCT.Unf

theorem lattice_one {V Λ : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddRightInvariant]
    (h0 : μ ≠ 0) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) {C : Set V} (hC : MeasurableSet C) (hf : μ C ≠ ⊤)
    (cov : ∀ y, ∃ l, y + j l ∈ C) (fin : ∀ y, {l | y + j l ∈ C}.Finite) (T : V →+ V) (hT : Measurable T) (t : Λ ≃ Λ)
    (ht : ∀ l, T (j l) = j (t l)) {c : ℝ≥0} (hc : μ.map T = c • μ) : c = 1 := by
  let S : V → ℝ≥0∞ := fun y => ∑' l, C.indicator 1 (y + j l)
  have hi : Measurable (C.indicator (1 : V → ℝ≥0∞)) := measurable_one.indicator hC
  have hS : Measurable S := Measurable.tsum fun l => hi.comp (measurable_add_const _)
  have S1 : ∀ y, 1 ≤ S y := fun y => by
    obtain ⟨l, hl⟩ := cov y
    exact le_trans (by simp [hl]) (ENNReal.le_tsum l)
  have S2 : ∀ y, S y ≠ ⊤ := fun y => by
    simp only [S]
    rw [tsum_eq_sum (s := (fin y).toFinset) fun l hl => Set.indicator_of_notMem (by simpa using hl) _]
    exact ENNReal.sum_ne_top.2 fun l _ => by by_cases h : y + j l ∈ C <;> simp [h]
  have S3 : ∀ y l, S (y + j l) = S y := fun y l => by
    simp only [S, add_assoc, ← map_add]
    exact (Equiv.addLeft l).tsum_eq fun m => C.indicator 1 (y + j m)
  let β : V → ℝ≥0∞ := fun y => C.indicator 1 y * (S y)⁻¹
  have hβ : Measurable β := hi.mul hS.inv
  have b1 : ∀ y, ∑' l, β (y + j l) = 1 := fun y => by
    simp only [β, S3]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel (zero_lt_one.trans_le (S1 y)).ne' (S2 y)
  have b2 : ∀ y, ∑' l, β (T (y + j l)) = 1 := fun y => by
    simp only [map_add, ht]
    exact (t.tsum_eq fun l => β (T y + j l)).trans (b1 _)
  have half : ∀ f g : V → ℝ≥0∞, Measurable f → Measurable g → (∀ y, ∑' l, g (y + j l) = 1) →
      ∫⁻ y, f y ∂μ = ∑' l, ∫⁻ y, f y * g (y + j l) ∂μ := fun f g h1 h2 h3 => by
    rw [← lintegral_tsum (f := fun l y => f y * g (y + j l)) fun l => (h1.mul (h2.comp (measurable_add_const _))).aemeasurable]
    simp only [ENNReal.tsum_mul_left, h3, mul_one]
  have e : ∫⁻ y, β (T y) ∂μ = ∫⁻ y, β y ∂μ := by
    rw [half (fun y => β (T y)) β (hβ.comp hT) hβ b1, half β (fun y => β (T y)) hβ (hβ.comp hT) b2, ← (Equiv.neg Λ).tsum_eq]
    refine tsum_congr fun l => ?_
    rw [← lintegral_add_right_eq_self _ (j l)]
    simp [mul_comm]
  rw [← lintegral_map hβ hT, hc, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul] at e
  have n0 : ∫⁻ y, β y ∂μ ≠ 0 := fun h => h0 (by
    rw [← Measure.measure_univ_eq_zero, ← lintegral_one, half _ β measurable_const hβ b1]
    simp [lintegral_add_right_eq_self β, h])
  have n1 : ∫⁻ y, β y ∂μ ≠ ⊤ := ne_top_of_le_ne_top hf (by
    rw [← lintegral_indicator_one hC]
    exact lintegral_mono fun y => mul_le_of_le_one_right' (ENNReal.inv_le_one.2 (S1 y)))
  exact_mod_cast (ENNReal.mul_left_inj n0 n1).1 (e.trans (one_mul _).symm)

theorem eq_one_of_bdd {T : Type} [Group T] (φ : T →* ℝ≥0) {b : ℝ≥0} (h : ∀ t, φ t ≤ b) (t : T) : φ t = 1 := by
  have k : ∀ t, φ t ≤ 1 := fun t => not_lt.1 fun h1 => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b h1
    exact absurd (h (t ^ n)) (by rw [map_pow]; exact not_le.2 hn)
  refine le_antisymm (k t) ?_
  calc 1 = φ t * φ t⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ φ t := mul_le_of_le_one_right' (k _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_flow (h : IsCMExt F E σ) {τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ} (hτ : IsFlow τ) (x : ℝ) :
    (absE F E (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (2 * Module.finrank ℚ F * x) := by
  obtain ⟨-, θ, hθ, hv⟩ := hτ
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have e := GlobalTheory.CompanionTheory.SW.FChi.norm_tmul_one h.2.2.1 (AF F) (pairA F (θ (Real.exp x)) 1)
  rw [← hv] at e
  simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, e, map_pow]
  have e1 : ∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.AdelicU.evFin F v (pairA F (θ (Real.exp x)) 1) = 1 := fun v =>
    map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
  have e2 : ∀ w : InfinitePlace F, ‖GlobalTheory.AdelicU.evInf F w (pairA F (θ (Real.exp x)) 1)‖ = Real.exp x := fun w => by
    have := Complex.ringHom_eq_ofReal_of_continuous (f := (InfinitePlace.Completion.extensionEmbedding w).comp
      ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp θ))
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp hθ))
    have h2 := congrArg (fun f : ℝ →+* ℂ => ‖f (Real.exp x)‖) this
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    refine Eq.trans h2 ?_
    simp
  simp only [e1, one_pow, nnnorm_one, finprod_one, mul_one, NNReal.coe_prod, NNReal.coe_pow, nnnorm_pow, coe_nnnorm, e2,
    Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  rw [← pow_mul, ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem modulus (h : IsCMExt F E σ) (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F))
    (hW : μW.IsAddHaarMeasure) (hA : μA.IsAddHaarMeasure) : ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧
      (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1,
        Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ a, χ a * absE F E a ^ (M + 1) = 1 := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)
  have := hB 1 M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable F := Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ h
  obtain ⟨χ, χc, χ1, χ2⟩ := GlobalTheory.T.modulus_character_unit_action_product F E σ h τ hτ M μW μA hW hA
  obtain ⟨ω, hω, hid⟩ := GlobalTheory.T.adelic_units_decomposition_flow_compact F E σ h τ hτ
  obtain ⟨⟨CW, hCW, cW⟩, fW, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ h 1 M
  obtain ⟨⟨CA, hCA, cA⟩, fA, -⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  have rt : ∀ X Y : Fin 1 → Fin M → E, ratTup (F := F) (AF F) (X + Y) = ratTup (AF F) X + ratTup (AF F) Y :=
    fun X Y => funext fun a => funext fun i => map_add _ _ _
  have rat : ∀ (l : Eˣ) (a : (AF F ⊗[F] E)ˣ), (a : AF F ⊗[F] E) = inclR (AF F) (l : E) → χ a = 1 := fun l a hl => by
    have hs : σ l ≠ 0 := (map_ne_zero σ).2 l.ne_zero
    have hn : Algebra.norm F (l : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 l.ne_zero
    let j : (Fin 1 → Fin M → E) × F →+ (Fin 1 → Fin M → AF F ⊗[F] E) × AF F :=
      (AddMonoidHom.mk' _ rt).prodMap (algebraMap F (AF F)).toAddMonoidHom
    refine lattice_one (μW.prod μA) (NeZero.ne _) j (hCW.prod hCA).measurableSet (hCW.prod hCA).measure_lt_top.ne
      (fun y => ?_) (fun y => ?_) ((DistribSMul.toAddMonoidHom _ (sigR (AF F) σ (a : AF F ⊗[F] E))).prodMap
        (AddMonoidHom.mulLeft (Algebra.norm (AF F) (a : AF F ⊗[F] E)))) ?_
      ((MulAction.toPerm (Units.mk0 _ hs)).prodCongr (Equiv.mulLeft₀ _ hn)) (fun l' => Prod.ext ?_ ?_) (χ1 a)
    · obtain ⟨X, hX⟩ := cW y.1
      obtain ⟨r, hr⟩ := cA y.2
      exact ⟨-(X, r), by rw [map_neg, ← sub_eq_add_neg]; exact ⟨hX, hr⟩⟩
    · refine ((fW _ (hCW.image (continuous_add_left (-y.1)))).prod (fA _ (hCA.image (continuous_add_left (-y.2))))).subset ?_
      exact fun l' hl' => ⟨⟨_, hl'.1, neg_add_cancel_left _ _⟩, ⟨_, hl'.2, neg_add_cancel_left _ _⟩⟩
    · exact ((continuous_const_smul _ : Continuous fun x : Fin 1 → Fin M → AF F ⊗[F] E => (_ : AF F ⊗[F] E) • x).prodMap (continuous_const.mul continuous_id : Continuous fun x : AF F => _ * x)).measurable
    · funext b i
      show sigR (AF F) σ (a : AF F ⊗[F] E) * inclR (AF F) (l'.1 b i) = inclR (AF F) (σ l * l'.1 b i)
      rw [hl, map_mul]; rfl
    · show Algebra.norm (AF F) (a : AF F ⊗[F] E) * algebraMap F (AF F) l'.2 = algebraMap F (AF F) (Algebra.norm F (l : E) * l'.2)
      rw [hl, map_mul]
      exact congrArg (· * _) (GlobalTheory.Doubling.norm_inclR _)
  have hc : Continuous fun a => χ a * absE F E a ^ (M + 1) := χc.mul (GlobalTheory.Doubling.continuous_absE.pow _)
  obtain ⟨b, hb⟩ := (hω.image hc).bddAbove
  refine ⟨χ, χc, χ1, eq_one_of_bdd (χ * (powMonoidHom (M + 1)).comp (absE F E)) (b := b) fun a => ?_⟩
  obtain ⟨l, a', x, j, hl, hx, rfl⟩ := hid a
  have e1 : absE F E a' = 1 := by
    rw [← GlobalTheory.Doubling.absE_inclR (F := F) l]
    exact congrArg _ (Units.ext hl)
  have e2 : χ (τ (Multiplicative.ofAdd (j : ℝ))) * absE F E (τ (Multiplicative.ofAdd (j : ℝ))) ^ (M + 1) = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_pow, χ2, absE_flow h hτ, ← Real.exp_nat_mul, ← Real.exp_add, NNReal.coe_one, Real.exp_eq_one_iff]
    push_cast
    ring
  rw [map_mul, map_mul]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, powMonoidHom_apply, rat l a' hl, e1, e2, one_pow, one_mul]
  exact hb ⟨x, hx, rfl⟩

end PositivityTheory.ThKCT.Unf
