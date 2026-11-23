import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPsiKOverScaledIntegersEqVolumeIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerSwapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledIntegersKAnnihilatorSmallNearZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenCompactAnnihilatorScaledIntegersKStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleExistsSqRootNearOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneEtaleAlgebraMulInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedSetEmptyOutsideNormCosetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianPairNormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMultiplicativeUnitOneHaarScalingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedIntegralEqVolMulOrbitalIntegralStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WhitX

theorem u_formula (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ω : A.K → ℂ) (μ : Measure A.L) (γ : ℂ)
    (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ) (hW : A.IsWeil ψ x ω μ γ W)
    (φ : A.L → ℂ) (hφ : IsTest φ) (z : A.K) :
    W (wS A.K * nS z) φ 0 = γ * ∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ := by
  obtain ⟨hrep, hform⟩ := hW
  rw [hrep.2.2.1 _ _ _ hφ, (hform _ (hrep.1 _ _ hφ)).2.2 0]
  congr 1
  unfold fourB
  congr 1
  funext y
  rw [(hform φ hφ).1 z y]
  simp [Et.kerL, Et.psiK, mul_comm]

theorem M_sub (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (c : F) (hc : c ≠ 0) :
    ∃ M : AddSubgroup A.K, (M : Set A.K) = {z : A.K | c • z ∈ A.OK} ∧ IsOpen (M : Set A.K) ∧ IsCompact (M : Set A.K) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  refine ⟨(R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c), ?_, ?_, ?_⟩
  · ext z; simp [← hR]
  · have : ((R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c) : Set A.K) = (fun z => c • z) ⁻¹' A.OK := by
      ext z; simp [← hR]
    rw [this]; exact hOo.preimage (continuous_const_smul c)
  · have : ((R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c) : Set A.K) = (fun z => c⁻¹ • z) '' A.OK := by
      ext z; simp only [AddSubgroup.coe_comap, Set.mem_preimage, Set.mem_image, DistribMulAction.toAddMonoidHom_apply]
      constructor
      · intro h; exact ⟨c • z, by simpa [← hR] using h, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_smul, mul_inv_cancel₀ hc, ← hR] using hw
    rw [this]; exact hOc.image (continuous_const_smul c⁻¹)

theorem lam_weil_eventually : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (γ : ℂ) W, A.IsWeil ψ x A.etaK (m.μL x) γ W → ∀ φ, IsTest φ → ∀ a : A.K, IsUnit a → (∀ y : A.L, IsUnit y → a = x * A.NL y → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = γ * A.orbL m.ν φ y) ∧ ((¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = 0) := by
  intro F E _ _ _ _ _ A ψ hψ m x γ W hW φ hφ a ha
  haveI := m.sdK.1
  haveI := (m.sdL x).1
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOo, -, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have key : ∀ c : F, c ≠ 0 → A.abelian₂ m.μK ψ a (fun g => W g φ 0) c =
      γ * ((m.μK {z | c • z ∈ A.OK}).toReal : ℂ) *
        ∫ y, φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => (1 : ℂ))
          ((x : A.K) * A.NL y - a) ∂(m.μL x) := by
    intro c hc
    unfold Et.abelian₂
    simp_rw [u_formula F E A ψ x A.etaK (m.μL x) γ W hW φ hφ, mul_assoc γ]
    rw [integral_const_mul, GlobalTheory.T.setIntegral_integral_psiK_swap F E A ψ hψ m.μK inferInstance (m.μL x) inferInstance φ hφ x a c hc]
    simp_rw [GlobalTheory.T.integral_psiK_over_scaled_integers_eq_volume_indicator F E A ψ hψ m.μK inferInstance c hc]
    congr 1
    rw [← integral_const_mul]
    congr 1; funext y
    simp only [Set.indicator]
    split_ifs <;> ring
  obtain ⟨U1, hU1, hinv⟩ := GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant F E A φ hφ
  have hOK1 : A.OK ∈ 𝓝 (1 : A.K) := hOo.mem_nhds (by rw [← hR]; exact R.one_mem)
  have hsq := GlobalTheory.T.finiteEtale_exists_sq_root_near_one F E A (U1 ∩ A.OK) (inter_mem hU1 hOK1)
  have hcont : Tendsto (fun b : A.K => 1 + Ring.inverse a * b) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun b : A.K => 1 + Ring.inverse a * b) := by fun_prop
    simpa using this.tendsto 0
  have hU : {b : A.K | ∃ s ∈ U1 ∩ A.OK, ∃ s' ∈ U1 ∩ A.OK, s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse a * b} ∈ 𝓝 (0 : A.K) :=
    hcont hsq
  have hev := GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero F E A ψ hψ _ hU
  have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
  constructor
  · intro y hy hay
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    obtain ⟨D, hDset, hDo, hDc⟩ := GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK F E A ψ hψ c hc0
    obtain ⟨M, hMset, hMo, hMc⟩ := M_sub F E A c hc0
    have hMD : m.μK M * m.μK D = 1 := by
      have h := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd m.μK
        inferInstance).1 M hMo hMc).1
      have hk : A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
        funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
      have hsd : SelfDual m.μK (fun x y => ψ (Algebra.traceForm F A.K x y)) := hk ▸ m.sdK
      have hDeq : (D : Set A.K) = {y | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} := by
        rw [hDset]; ext b; simp [← SetLike.mem_coe, hMset, Et.psiK, Algebra.traceForm_apply]
      rw [hDeq]; exact h.1 hsd
    rw [← hDset, ← hMset]
    subst hay
    rw [GlobalTheory.T.truncatedIntegral_eq_vol_mul_orbitalIntegral F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) (GlobalTheory.T.absK_multiplicative_unitOne_haarScaling F E A) ψ hψ m x y hy D hDo hDc φ hφ ?_]
    · have : (m.μK M).toReal * (m.μK D).toReal = 1 := by rw [← ENNReal.toReal_mul, hMD]; simp
      have : ((m.μK M).toReal : ℂ) * ((m.μK D).toReal : ℂ) = 1 := by exact_mod_cast this
      linear_combination (γ * A.orbL m.ν φ y) * this
    · intro b hb
      have hb' := hc b (by rw [← SetLike.mem_coe, hDset] at hb; exact hb)
      obtain ⟨s, ⟨hsU, hsO⟩, s', ⟨hsU', hsO'⟩, hss, hs2⟩ := hb'
      exact ⟨s, s', hsO, hsO', hss, hs2, hinv s hsU s' hsU' hss⟩
  · intro hno
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    have hz := GlobalTheory.T.truncated_set_empty_outside_norm_coset F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) x a {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      (fun b hb => by
        obtain ⟨s, -, s', -, hss, hs2⟩ := hc b hb
        exact ⟨s, s', hss, hs2⟩) ha hno
    have : (fun y => φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
        (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - a)) = fun _ => 0 := by
      funext y; rw [Set.indicator_of_notMem (hz y)]; simp
    rw [this]; simp

end GlobalTheory.JR.WhitX
