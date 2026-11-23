import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockOneStepConst

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

theorem smul_indicator_mass {α : Type} [MeasurableSpace α] {β : Type} (k : ℝ≥0) (μ : Measure α) (A B : Set α)
    (L : Set β) (y : β) (h : μ A = L.indicator (fun _ => μ B) y) :
    (k • μ) A = L.indicator (fun _ => (k • μ) B) y := by
  by_cases hy : y ∈ L
  · rw [Set.indicator_of_mem hy] at h ⊢
    rw [Measure.smul_apply, Measure.smul_apply, h]
  · rw [Set.indicator_of_notMem hy] at h ⊢
    rw [Measure.smul_apply, h, smul_zero]

theorem stepC_of (hE1 : PositivityTheory.PfSWUS.HMass.OneVecBinary) (hM : MassCAll) : StepC := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM1 t ht hA T hT hdet hT' hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩
  have hdet' : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [(GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M T t).1]; exact mul_ne_zero hta hdet

  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  obtain ⟨m'inf, hm'inf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Ainf F) hLi b laminf hinf.1 M
  choose m' hm' using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hlam v).1 M
  obtain ⟨c₀, hE', hc₀⟩ := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf m' hm'inf hm'
  refine ⟨c₀, ?_, hc₀⟩

  obtain ⟨m₁inf, hm₁inf⟩ := GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  choose m₁ hm₁ using fun v => GlobalTheory.CompanionTheory.SW.Step.loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := PositivityTheory.PfSWUS.HMass.one_vec_sw hE1 F E σ hCM (M + 1) _ hJ' (by omega) (Or.inr hA) T1 hT1 hdet1
    d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hgood := hM F E σ hCM (M + 1) (by omega) _ hJ' _ hT' hdet' d b lam hlam m hm
  refine ⟨hgood.1, hgood.2, ?_⟩
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.CompanionTheory.SW.StepC.theta_hypothesis_c F E σ hCM M J hJ t ht M d b _ _ _ _ hE'
  have hG := GlobalTheory.T.local_density_block_one_eventually F E σ hCM M J hJ t ht M T hT hdet hT' d b
  have hSG := GlobalTheory.T.local_measures_orthogonal_sum_almost_all_places F E σ hCM M J hJ t ht M T hT hdet d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht M T hT hdet hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ₀ hΨm₀ hΨ1₀ hΨ2₀ using fun v => GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht M T hT hdet hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (fun y => (cfac E v : ℝ≥0∞) * φ v y)
    ((hφ v).const_mul _)

  have hΨ1 : ∀ v, ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J),
      Ψ₀ v (actW (Fv F v) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) =
        ∫⁻ X, φ v (actW (Fv F v) σ _ g (consTup X)) ∂(cfac E v • m' v (hermOf (Fv F v) σ T hT)) := by
    intro v g
    rw [hΨ1₀ v g, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, lintegral_const_mul']
    exact ENNReal.coe_ne_top
  have hΨ2 : ∀ v, ∫⁻ X, φ v X ∂(cfac E v • m v (hermOf (Fv F v) σ _ hT')) =
      (c v : ℝ≥0∞) ^ M * ∫⁻ y, Ψ₀ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    intro v
    rw [← hΨ2₀ v, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, lintegral_const_mul']
    exact ENNReal.coe_ne_top
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) M M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) M).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 M M, hh.2.2 M⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ₀ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    smul_indicator_mass _ _ _ _ _ _ (GlobalTheory.CompanionTheory.SW.Step.of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g))
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, ((cfac E v.1 • m' v.1 (hermOf (Fv F v.1) σ T hT)) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ₀) := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ₀ hΨinfm hΨm₀
  have hth := GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one F E σ hCM M J hJ t ht M T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => ((c₀ : ℝ≥0∞) * τ') * pureL b S Ψinf Ψ₀ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (M + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul _) hHyp
  have hone := hS₁ S hS1 Ψinf Ψ₀ hΨinfm hΨm₀
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ₀ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) *
      ∏ v ∈ S, ∫⁻ X, φ v X ∂(cfac E v • m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ₀ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ M * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ₀ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, ((cfac E v.1 • m v.1 (hermOf (Fv F v.1) σ _ hT')) (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => ((cfac E v.1 • m' v.1 (hermOf (Fv F v.1) σ T hT)) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, ((cfac E v.1 • m v.1 (hermOf (Fv F v.1) σ _ hT')) (latV b v.1)).toReal =
        ((cfac E v.1 • m' v.1 (hermOf (Fv F v.1) σ T hT)) (latV b v.1)).toReal *
          (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [Measure.smul_apply, Measure.smul_apply, GlobalTheory.CompanionTheory.SW.Step.of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul, ENNReal.smul_def, mul_assoc]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end PositivityTheory.SiegelWeilFormula.Densx

end
