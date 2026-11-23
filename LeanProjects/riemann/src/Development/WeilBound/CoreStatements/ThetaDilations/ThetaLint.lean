import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodularStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscreteStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobalStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem theta_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ 𝓕 hμ h𝓕 n S Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  have hm : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  rw [thetaMeas, lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul,
    lintegral_tsum (f := fun (X : S) h => Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)))
      fun X => (hΦ.comp (hm _)).aemeasurable]
  simp only [lintegral_map hΦ (hm _)]

theorem theta_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ 𝓕 hμ h𝓕 n S Φ hΦ hint
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  have hm : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have hi : (μ 𝓕)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin.ne
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin).1
  have h1 := hint.2
  rw [hasFiniteIntegral_iff_enorm, theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n S _ hΦ.enorm,
    lintegral_tsum (f := fun (X : S) h => ‖Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1))‖ₑ)
      fun X => (hΦ.enorm.comp (hm _)).aemeasurable] at h1
  have h2 := (ENNReal.lt_top_of_mul_ne_top_right h1.ne hi).ne
  rw [thetaMeas, integrable_smul_measure hi (ENNReal.inv_ne_top.2 h0)] at hint
  rw [thetaMeas, integral_smul_measure, integral_sum_measure hint, meanC, ENNReal.toReal_inv]
  simp only [integral_map (hm _).aemeasurable hΦ.aestronglyMeasurable]
  exact congrArg _ (integral_tsum (fun X => (hΦ.comp (hm _)).aestronglyMeasurable) h2)

theorem act_rat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E) :
    ∃ X' : Fin n → Fin M → E, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm
  simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem theta_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}) ∧ thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ 𝓕 hμ h𝓕 n T
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ n 0 T).2
  have hl := theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n {X | gramE σ J X = T}
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  refine ⟨fun h => ?_, ?_⟩
  · have hm : Measurable (actW (AF F) σ J h : (Fin n → Fin M → _) → _) :=
      (ac.comp (continuous_const.prodMk continuous_id)).measurable
    have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
    have : μ.IsHaarMeasure := hμ
    let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
    have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
    have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
    obtain ⟨-, _, -⟩ := GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin
    refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
    rw [lintegral_map hΦ hm, hl (fun X => Φ (actW (AF F) σ J h X)) (hΦ.comp hm), hl _ hΦ]
    congr 1
    set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : {X | gramE σ J X = T},
      Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
    have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
      choose t ht using fun X : {X | gramE σ J X = T} => act_rat (n := n) γ⁻¹ X.1
      have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
      have hT : ∀ X, gramE σ J (t X) = T := fun X =>
        Matrix.map_injective hinj (by simp only [← hrat, ← ht', ag]; rw [hrat, X.2])
      have hti : Function.Injective fun X => (⟨t X, hT X⟩ : {X | gramE σ J X = T}) := fun X Y e => by
        have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
        simp only [← a2, mul_inv_cancel, a1] at h1
        exact Subtype.ext (hri h1)
      refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
      rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
    have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
      (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
    have hD := h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ h).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ g => (mul_assoc _ _ _)
    rw [h𝓕'.setLIntegral_eq hD f hinv, ← (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulRight _)]
    simp only [hf, mul_inv_rev, ← a2, mul_inv_cancel_left]
  · have hc : MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ :=
      (isClosed_eq (hg n M J) continuous_const).measurableSet.compl
    rw [← lintegral_indicator_one hc, hl _ (measurable_one.indicator hc)]
    have e : ∀ (h : HA (AF F) σ J) (X : {X | gramE σ J X = T}), Set.indicator
        {X : Fin n → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) = 0 := fun h X =>
      Set.indicator_of_notMem (Set.notMem_compl_iff.2 (by rw [Set.mem_setOf_eq, ag, hrat, X.2])) _
    simp [e]

end PositivityTheory.PlacePermOperatorBicommutantSpan
