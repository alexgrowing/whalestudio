import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableProdPowMultiIndex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientHeckeDecayStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetVolumeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupFiniteVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientCartanTranslateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupBasisNhdsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupAntitoneStatement

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SqIntHecke

theorem lintegral_sq_lt_top_of_cover {X ι κ : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) [Finite ι]
    [Countable κ] (A : ι → κ → Set X) (hcov : ∀ x, ∃ i j, x ∈ A i j) (b w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (E : ENNReal) (hE : E < ⊤) (hF : ∀ i j, ∀ x ∈ A i j, ‖F x‖ ≤ b i j)
    (hμ : ∀ i j, μ (A i j) ≤ ENNReal.ofReal (w i j) * E)
    (hsum : ∀ i, Summable fun j => b i j ^ 2 * w i j) :
    ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hu : (⋃ p : ι × κ, A p.1 p.2) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, j, h⟩ := hcov x
    exact ⟨(i, j), h⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∑' p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
    conv_lhs => rw [← setLIntegral_univ, ← hu]
    exact lintegral_iUnion_le _ _
  have h2 : ∀ p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal (b p.1 p.2 ^ 2 * w p.1 p.2) * E := by
    rintro ⟨i, j⟩
    have h3 : ∫⁻ x in A i j, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ x in A i j, ENNReal.ofReal (b i j ^ 2) ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hF i j x hx) 2)
    refine h3.trans ?_
    rw [setLIntegral_const, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
    gcongr
    exact hμ i j
  refine (h1.trans (ENNReal.tsum_le_tsum h2)).trans_lt ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (b i j ^ 2 * w i j))]
  refine ENNReal.mul_lt_top ?_ hE
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (hw i j)) (hsum i)]
  exact ENNReal.ofReal_lt_top

theorem sq_mul_pow_eq {r : ℕ} (q : ℝ) (e g : Fin r → ℕ) (ρ : Fin r → ℝ) (C : ℝ) :
    (C * ∏ j, ρ j ^ g j) ^ 2 * q ^ (∑ j, g j * e j) = C ^ 2 * ∏ j, (q ^ e j * ρ j ^ 2) ^ g j := by
  have h1 : ∏ j, (q ^ e j) ^ g j = q ^ (∑ j, g j * e j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have h2 : ∏ j, (ρ j ^ 2) ^ g j = (∏ j, ρ j ^ g j) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [mul_pow _ _ (g _)]
  rw [Finset.prod_mul_distrib, h1, h2, mul_pow C, mul_assoc, mul_comm (q ^ _)]

theorem isSqIntCoeff_of_heckeSpectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π →
    Zls.HeckeSpectral π → IsSqIntCoeff π := by
  intro k _ _ _ _ N V _ _ π hs hi ha hu hH
  unfold IsSqIntCoeff CoeffLp
  intro _ _ μ hμ v l hl
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ w, ‖l (π z w)‖ = ‖l w‖ := by
    intro z hz w
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨c, hc⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k N V π hs hi ha t
    rw [hc, map_smul, norm_smul, hu t c hc, one_mul]
  have hF : ∀ g : GL (Fin N) k, ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    rw [hz, Subgroup.mem_center_iff.1 z.2 g, map_mul, Module.End.mul_apply, hcen _ z.2]
  refine ⟨fun q => ‖l (π q.out v)‖, hF, ?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k N => ‖l (π q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (π g v)‖ from funext hF]
    exact ((SqIntBridge.isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  rw [show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (GL (Fin 0) k) := inferInstance
    have h1 : Subsingleton (AdGL k 0) := inferInstance
    have h2 : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
    refine lintegral_sq_lt_top_of_cover μ _ (fun _ _ : Unit => Set.univ) (fun _ => ⟨(), (), trivial⟩)
      (fun _ _ => ‖l (π (1 : AdGL k 0).out v)‖) (fun _ _ => 1) (fun _ _ => zero_le_one) _ h2 ?_ (by simp)
      (fun _ => (hasSum_fintype _).summable)
    intro _ _ x _
    rw [Subsingleton.elim x 1, norm_norm]
  obtain ⟨m1, hm1, hK1⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ (hs v) (by simp)
  obtain ⟨m2, hm2, hK2⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ hl (by simp [Module.End.one_eq_id])
  have hm : 1 ≤ max m1 m2 := hm1.trans (le_max_left _ _)
  obtain ⟨m, hmm⟩ : ∃ m, m = max m1 m2 := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hv : v ∈ fixed π (Zls.Km k N m) := by
    rintro ⟨x, hx⟩
    have : π x v = v := hK1 (GlobalTheory.T.congruence_subgroup_antitone k N m1 m (hmm ▸ le_max_left _ _) hx)
    simpa using this
  have hlK : ∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l := fun x hx =>
    hK2 (GlobalTheory.T.congruence_subgroup_antitone k N m2 m (hmm ▸ le_max_right _ _) hx)
  obtain ⟨s, hsK, hcov⟩ := GlobalTheory.T.cartan_decomposition_congruence k N m hm hN
  have key : ∀ p : s, ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧
      (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧
      ∀ g : Fin (N - 1) → ℕ, ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m,
        ‖l (π (p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
    rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := hsK p hp
    obtain ⟨hf, hli, heq⟩ := GlobalTheory.T.matrix_coefficient_cartan_translate k N V π m v hv l hlK p.1 p.2 h1 h2
    obtain ⟨C, ρ, hρ0, hρ1, hb⟩ := GlobalTheory.T.matrix_coefficient_hecke_decay k N V π hs ha hH m hm (π p.2 v) hf (l ∘ₗ π p.1) hli
    refine ⟨C, ρ, hρ0, hρ1, fun g x hx y hy => ?_⟩
    rw [heq _ x hx y hy]
    exact hb g
  choose C ρ hρ0 hρ1 hbound using key
  refine lintegral_sq_lt_top_of_cover μ _
    (fun (p : s) (g : Fin (N - 1) → ℕ) => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2})
    ?_ (fun p g => C p * ∏ j, ρ p j ^ g j)
    (fun _ g => (Nat.card 𝓀[k] : ℝ) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))))
    (fun _ _ => by positivity)
    (μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))))
    (GlobalTheory.T.congruence_subgroup_finite_volume k N μ hμ m) ?_ ?_ ?_
  · intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨p, hp, g, a, ha', b, hb, z, hz, rfl⟩ := hcov h
    exact ⟨⟨p, hp⟩, g, _, ⟨a, ha', b, hb, rfl⟩, (QuotientGroup.mk_mul_of_mem _ hz).symm⟩
  · rintro p g _ ⟨h, ⟨a, ha', b, hb, rfl⟩, rfl⟩
    show ‖‖l (π (QuotientGroup.mk _ : AdGL k N).out v)‖‖ ≤ _
    rw [norm_norm, hF]
    exact hbound p g a ha' b hb
  · intro p g
    obtain ⟨h1, h2⟩ := hsK p.1 p.2
    refine (GlobalTheory.T.double_coset_volume_le k N μ hμ m hm p.1.1 p.1.2 h1 h2 g).trans_eq ?_
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro p
    have h := GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex (N - 1)
      (fun j => (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ p j ^ 2)
      (fun j => by positivity) (hρ1 p)
    exact (h.mul_left (C p ^ 2)).congr fun g => (sq_mul_pow_eq _ _ g _ _).symm

end GlobalTheory.CompanionTheory.SqIntHecke
