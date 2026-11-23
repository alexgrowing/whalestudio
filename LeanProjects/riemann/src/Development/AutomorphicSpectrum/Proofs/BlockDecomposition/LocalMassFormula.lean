import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityBoundNonzero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityUnitLattice
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocBin

open GlobalTheory.CompanionTheory.SW.GBall

theorem bound_step_two {q : ℝ} (hq : 2 ≤ q) {Dp D' : ℝ} (hD' : |D' - 1| ≤ 3 / q)
    (hDp : |Dp - 1| ≤ 1 / q ^ (2 - 1) + 1 / q ^ (2 * 2 - 1)) :
    |Dp + q ^ 2 / q ^ (2 * 2) * D' - 1| ≤ 3 / q := by
  have hq0 : 0 < q := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = 1 / q := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hw2 : w ≤ 1 / 2 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hq
  have e1 : 3 / q = 3 * w := by rw [hw]; ring
  have e2 : q ^ 2 / q ^ (2 * 2) = w * w := by
    rw [hw]; field_simp
  have e3 : 1 / q ^ (2 - 1) + 1 / q ^ (2 * 2 - 1) = w + w * w * w := by
    rw [hw]; norm_num; field_simp
  rw [e1] at hD' ⊢
  rw [e2]
  rw [e3] at hDp
  obtain ⟨a1, a2⟩ := abs_le.1 hD'
  obtain ⟨b1, b2⟩ := abs_le.1 hDp
  have hww : 0 < w * w := mul_pos hw0 hw0
  have c1 : w * w * D' ≤ w * w * (1 + 3 * w) := mul_le_mul_of_nonneg_left (by linarith) hww.le
  have c1' : w * w * (1 - 3 * w) ≤ w * w * D' := mul_le_mul_of_nonneg_left (by linarith) hww.le
  have c3 : w * w ≤ w * (1 / 2) := mul_le_mul_of_nonneg_left hw2 hw0.le
  have c4 : w * w * w ≤ w * w * (1 / 2) := mul_le_mul_of_nonneg_left hw2 hww.le
  rw [abs_le]
  constructor <;> nlinarith

theorem local_density_binary_unimodular {ι : Type} [Fintype ι] {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam)
    (h2 : Valued.v (2 : Fv F v) = 1)
    [DecidableEq ι] (B : Matrix ι ι (Fv F v)) (hsym : B.IsSymm)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hdet : Valued.v B.det = 1)
    (hc : Fintype.card ι = 2 * 2) (n : ℕ) :
    ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → WithZero.exp (-(n : ℤ)) ≤ Valued.v s →
      ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 3 / (Ideal.absNorm v.asIdeal : ℝ) ∧
        ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
          (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
            (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hs0 hn
  obtain ⟨Dp, hDp, hprim⟩ := GlobalTheory.T.local_quadratic_density_near_one F v lam hstd h2 ι B hsym hB hdet 2 hc (by omega) s hs
  obtain ⟨π, hπ⟩ := exists_unif v
  have hπ0 := pi_ne_zero hπ
  have hs1 : Valued.v s ≤ 1 := mem_int.1 hs
  have hball : ∀ A : Set (Fv F v), A ⊆ {z | Valued.v (z - s) < Valued.v s} →
      A ⊆ {z | Valued.v (z - s) < 1} := fun A h z hz => lt_of_lt_of_le (h hz) hs1
  have hqN : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hqN
  by_cases hcase : WithZero.exp (-2 : ℤ) < Valued.v s
  · refine ⟨Dp, ?_, fun A hA hsub => ?_⟩
    · refine hDp.trans ?_
      have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
      have h3 : 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * 2 - 1) ≤
          1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 - 1) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
      have h4 : 3 / (Ideal.absNorm v.asIdeal : ℝ) =
          1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 - 1) + 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 - 1) +
            1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 - 1) := by
        norm_num
        ring
      have h5 : 0 ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ (2 - 1) := by positivity
      rw [h4]
      linarith
    · rw [← hprim A hA (hball A hsub)]
      congr 1
      ext x
      constructor
      · rintro ⟨hx, hQ⟩
        refine ⟨hx, ?_, hQ⟩
        by_contra hnp
        have h5 := q_nonprim h2 hB hπ hx hnp
        have hlt : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) - s) < Valued.v s := hsub hQ
        have hv := Valuation.map_eq_of_sub_lt Valued.v hlt
        rw [hv] at h5
        exact absurd h5 (not_le.2 hcase)
      · rintro ⟨hx, -, hQ⟩
        exact ⟨hx, hQ⟩
  · have hcase' : Valued.v s ≤ WithZero.exp (-2 : ℤ) := not_lt.1 hcase
    obtain ⟨s', hs'⟩ : ∃ s', s' = π⁻¹ * (π⁻¹ * s) := ⟨_, rfl⟩
    have hss : π * (π * s') = s := by
      rw [hs', mul_inv_cancel_left₀ hπ0, mul_inv_cancel_left₀ hπ0]
    have hvs' : Valued.v s' = WithZero.exp (2 : ℤ) * Valued.v s := by
      rw [hs', map_mul, map_mul, val_inv hπ, ← mul_assoc, ← WithZero.exp_add]
      norm_num
    have hvs : Valued.v s = WithZero.exp (-2 : ℤ) * Valued.v s' := by
      rw [← val_pp hπ, hss]
    have hs'1 : Valued.v s' ≤ 1 := by
      rw [hvs']
      calc WithZero.exp (2 : ℤ) * Valued.v s ≤ WithZero.exp (2 : ℤ) * WithZero.exp (-2 : ℤ) :=
            mul_le_mul' le_rfl hcase'
        _ = 1 := by rw [← WithZero.exp_add]; simp
    have hs'0 : s' ≠ 0 := by
      intro h
      rw [h] at hss
      simp at hss
      exact hs0 hss.symm
    have hn2 : 2 ≤ n := by
      have h6 := WithZero.exp_le_exp.1 (hn.trans hcase')
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hm : WithZero.exp (-(m : ℤ)) ≤ Valued.v s' := by
      rw [hvs']
      calc WithZero.exp (-(m : ℤ)) = WithZero.exp (2 : ℤ) * WithZero.exp (-((m + 2 : ℕ) : ℤ)) := by
            rw [← WithZero.exp_add]
            congr 1
            push_cast
            ring
        _ ≤ _ := mul_le_mul' le_rfl hn
    obtain ⟨D', hD', hdens⟩ := ih m (by omega) s' (mem_int.2 hs'1) hs'0 hm
    obtain ⟨q, hqq⟩ : ∃ q : ℝ≥0, q = (Ideal.absNorm v.asIdeal : ℝ≥0) := ⟨_, rfl⟩
    have hqR : (q : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by rw [hqq]; simp
    have hqE : (q : ℝ≥0∞) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by rw [hqq]; simp
    have hq0 : q ≠ 0 := by
      intro h
      rw [h] at hqR
      rw [← hqR] at hq
      norm_num at hq
    refine ⟨Dp + q ^ 2 / q ^ (2 * 2) * D', ?_, fun A hA hsub => ?_⟩
    · have h7 := bound_step_two hq hD' hDp
      rw [← hqR] at h7 ⊢
      push_cast
      exact h7
    · obtain ⟨T, hT⟩ : ∃ T : Set (ι → Fv F v), T = {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} := ⟨_, rfl⟩
      rw [← hT]
      have hsplit := measure_inter_add_sdiff (μ := Measure.pi fun _ : ι => lam) T
        (meas_prim (ι := ι) (v := v))
      have hTP : T ∩ {x : ι → Fv F v | ∃ i, Valued.v (x i) = 1} =
          {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧
            (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} := by
        rw [hT]
        ext x
        constructor
        · rintro ⟨⟨a, b⟩, c⟩
          exact ⟨a, c, b⟩
        · rintro ⟨a, c, b⟩
          exact ⟨⟨a, b⟩, c⟩
      rw [hTP, hprim A hA (hball A hsub)] at hsplit
      obtain ⟨hAm, hAl⟩ := lam_scale hstd hπ hA
      have hsub' : {z | π * (π * z) ∈ A} ⊆ {z | Valued.v (z - s') < Valued.v s'} := by
        intro z hz
        have h8 : Valued.v (π * (π * z) - s) < Valued.v s := hsub hz
        have h9 : π * (π * z) - s = π * (π * (z - s')) := by
          rw [← hss]; ring
        rw [h9, val_pp hπ, hvs] at h8
        by_contra h10
        exact absurd (mul_le_mul' (le_refl (WithZero.exp (-2 : ℤ))) (not_lt.1 h10)) (not_le.2 h8)
      have hS := hdens _ hAm hsub'
      have hpre : {y : ι → Fv F v | (fun i => π * y i) ∈ T \ {x | ∃ i, Valued.v (x i) = 1}} =
          {y | (∀ i, y i ∈ v.adicCompletionIntegers F) ∧
            (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ {z | π * (π * z) ∈ A}} := by
        rw [hT]
        ext y
        constructor
        · rintro ⟨⟨hx, hQ⟩, hnp⟩
          refine ⟨fun i => ?_, ?_⟩
          · have h11 := div_int hπ (mem_int.1 (hx i)) fun h => hnp ⟨i, h⟩
            rw [inv_mul_cancel_left₀ hπ0] at h11
            exact mem_int.2 h11
          · change π * (π * _) ∈ A
            rw [← q_smul]
            exact hQ
        · rintro ⟨hy, hQ⟩
          refine ⟨⟨fun i => mem_int.2 (pi_mul_lt hπ (mem_int.1 (hy i))).le, ?_⟩, ?_⟩
          · rw [q_smul]
            exact hQ
          · rintro ⟨i, hi⟩
            exact absurd hi (pi_mul_lt hπ (mem_int.1 (hy i))).ne
      have hscale := pi_scale hstd hπ (ι := ι) (T \ {x | ∃ i, Valued.v (x i) = 1})
      rw [hpre, hS, hAl, hc, ← hqE] at hscale
      have hne : (q : ℝ≥0∞) ^ (2 * 2) ≠ 0 := pow_ne_zero _ (by simpa using hq0)
      have htop : (q : ℝ≥0∞) ^ (2 * 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
      have hX : (Measure.pi fun _ : ι => lam) (T \ {x | ∃ i, Valued.v (x i) = 1}) =
          ((q : ℝ≥0∞) ^ (2 * 2))⁻¹ * ((D' : ℝ≥0∞) * ((q : ℝ≥0∞) ^ 2 * lam A)) := by
        rw [hscale, ← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul]
      rw [← hsplit, hX]
      have hq2 : q ^ (2 * 2) ≠ 0 := pow_ne_zero _ hq0
      push_cast [ENNReal.coe_div hq2]
      rw [div_eq_mul_inv]
      ring

theorem density_near_value_two {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam)
    (h2 : Valued.v (2 : Fv F v) = 1) (B : Matrix ι ι (Fv F v)) (hsym : B.IsSymm)
    (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hdet : Valued.v B.det = 1)
    (hc : Fintype.card ι = 2 * 2) (s : Fv F v) (hs : s ∈ v.adicCompletionIntegers F) (hs0 : s ≠ 0) :
    ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 3 / (Ideal.absNorm v.asIdeal : ℝ) ∧
      ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
        (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  have hv0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).2 hs0
  refine local_density_binary_unimodular hstd h2 B hsym hB hdet hc (-(Valued.v s).log).toNat s hs hs0 ?_
  conv_rhs => rw [← WithZero.exp_log hv0]
  rw [WithZero.exp_le_exp]
  have := Int.self_le_toNat (-(Valued.v s).log)
  omega

theorem density_nonint {ι : Type} [Fintype ι] {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (h2 : Valued.v (2 : Fv F v) = 1)
    (B : Matrix ι ι (Fv F v)) (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (s : Fv F v)
    (hs : s ∉ v.adicCompletionIntegers F) (A : Set (Fv F v))
    (hA : A ⊆ {z | Valued.v (z - s) < Valued.v s}) :
    (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
      (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = ((0 : ℝ≥0) : ℝ≥0∞) * lam A := by
  have hemp : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
      (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro x ⟨hx, hQ⟩
    have hlt : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) - s) < Valued.v s := hA hQ
    have hv := Valuation.map_eq_of_sub_lt Valued.v hlt
    have h1 := q_int h2 hB hx
    rw [hv] at h1
    exact hs (mem_int.2 h1)
  rw [hemp]
  simp

theorem locMass : PositivityTheory.Rg.Mass.LocMass := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ hlam _ _ _ hm
  classical
  refine ⟨3, ?_⟩
  obtain ⟨B, hBs, hBd, hBt⟩ := GlobalTheory.CompanionTheory.SW.trace_form_coords F E σ hCM 2 J hJ d b
  obtain ⟨-, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at h1
    exact h1.symm
  have hcard : Fintype.card (Fin 2 × Fin d) = 2 * 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hd]
  have hent : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, algebraMap F (Fv F v) (B i j) ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases h0 : B i j = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · refine (hun _ h0).mono fun v hv => ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hv.le
  filter_upwards [hun 2 two_ne_zero, hun _ hBd, hent,
    GlobalTheory.CompanionTheory.SW.UnitVal.density_unit_lattice F E σ hCM 2 J hJ (by norm_num) d b] with v hv2 hvd hve hunit
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  have hdet : Valued.v (B.map (algebraMap F (Fv F v))).det = 1 := by
    have h1 := (algebraMap F (Fv F v)).map_det B
    rw [h1] at hvd
    exact hvd
  have hmass := fun s hs0 D hD => GlobalTheory.CompanionTheory.SW.LocGood.local_mass σ hCM 2 J hJ d b v
    (B.map (algebraMap F (Fv F v))) (fun x y => hBt (Fv F v) x y) (lam v) (hlam v) (m v) (hm v) s hs0 D hD
  refine ⟨fun s hs hs0 => ?_, fun s hs hs0 => ?_, fun s hsu => ?_⟩
  · have h0 := hmass s hs0 0 fun A _ hA => density_nonint hv2' _ (fun i j => hve i j) s hs A hA
    have hfin : m v (hermScal (Fv F v) σ s) (latV b v) ≠ ⊤ := by
      have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
      obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
      haveI := hTR
      haveI := hLC
      haveI := hSC
      haveI := hT2
      haveI : BorelSpace (Fv F v) := ⟨rfl⟩
      have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
      haveI hW := hh.2.1 1 2
      haveI hH := hh.2.2 1
      have hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM 2 J hJ (Fv F v) hloc 1 _ _ (m v) hW hH (hm v)
        (hermScal (Fv F v) σ s)).1
      exact (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 2 v).1.measure_lt_top.ne
    simpa [ENNReal.toReal_eq_zero_iff, hfin] using h0
  · obtain ⟨D, hD1, hD⟩ := density_near_value_two (hlam v) hv2' (B.map (algebraMap F (Fv F v)))
      (hBs.map _) (fun i j => hve i j) hdet hcard s hs hs0
    rw [hmass s hs0 D hD]
    exact hD1
  · have h1 := hunit (lam v) (hlam v) (m v) (hm v) s hsu
    refine h1.trans ?_
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

end GlobalTheory.CompanionTheory.SW.LocBin
