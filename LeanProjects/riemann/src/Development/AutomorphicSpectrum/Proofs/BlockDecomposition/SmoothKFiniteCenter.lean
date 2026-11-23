import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteZSpanIntegralRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicRestrictionMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCountBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicIntegralDenominatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegersBoundedArchimedeanCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateCentrePowerBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBoundedStatement

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Growth

theorem count_rational (E : Type) [Field E] [NumberField E] (Q : Set (Af E)) (hQ : IsCompact Q) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      {x : E | algebraMap E (Af E) x ∈ Q ∧ ∀ w : InfinitePlace E, w x ≤ R}.Finite ∧
      ({x : E | algebraMap E (Af E) x ∈ Q ∧ ∀ w : InfinitePlace E, w x ≤ R}.ncard : ℝ) ≤ C * R ^ N := by
  obtain ⟨D, hD, hden⟩ := GlobalTheory.T.compact_adelic_integral_denominator E Q hQ
  obtain ⟨C, N, hC⟩ := GlobalTheory.T.integers_bounded_archimedean_count E
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hD
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD
  refine ⟨|C| * (D : ℝ) ^ N, N, by positivity, fun R hR => ?_⟩
  obtain ⟨hf, hc⟩ := hC (D * R) (by nlinarith)
  set A := {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ D * R}
  set B := {x : E | algebraMap E (Af E) x ∈ Q ∧ ∀ w : InfinitePlace E, w x ≤ R}
  have hsub : B ⊆ (fun r : 𝓞 E => (r : E) / D) '' A := by
    rintro x ⟨hx, hw⟩
    obtain ⟨r, hr⟩ := hden x hx
    refine ⟨r, fun w => ?_, by simp only [hr]; field_simp⟩
    rw [hr, map_mul]
    have : w (D : E) = D := by simpa using map_natCast w D
    rw [this]
    exact mul_le_mul_of_nonneg_left (hw w) (by positivity)
  have hfin : B.Finite := (hf.image _).subset hsub
  refine ⟨hfin, ?_⟩
  have h1 : B.ncard ≤ A.ncard := (Set.ncard_le_ncard hsub (hf.image _)).trans (Set.ncard_image_le hf)
  calc (B.ncard : ℝ) ≤ A.ncard := by exact_mod_cast h1
    _ ≤ C * (D * R) ^ N := hc
    _ ≤ |C| * (D * R) ^ N := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ = |C| * (D : ℝ) ^ N * R ^ N := by rw [mul_pow]; ring

theorem count_lattice (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)) (hQ : IsCompact Q) :
    ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin a) (Cinf E),
      {γ : GA E a | γ ∈ latticeGL E a ∧ (g₀ * infGL E a y)⁻¹ * γ * (g₀ * infGL E a y) ∈ Q}.Finite ∧
      ({γ : GA E a | γ ∈ latticeGL E a ∧ (g₀ * infGL E a y)⁻¹ * γ * (g₀ * infGL E a y) ∈ Q}.ncard : ℝ) ≤
        C * height y ^ N := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : Subsingleton (GA E 0) := inferInstance
    refine ⟨1, 0, fun y => ⟨Set.toFinite _, ?_⟩⟩
    have := Set.ncard_le_ncard (Set.subset_univ {γ : GA E 0 | γ ∈ latticeGL E 0 ∧ (g₀ * infGL E 0 y)⁻¹ * γ * (g₀ * infGL E 0 y) ∈ Q}) (Set.toFinite _)
    have h2 : (Set.univ : Set (GA E 0)).ncard = 1 := by
      rw [Set.ncard_univ, Nat.card_unique]
    rw [h2] at this
    rw [pow_zero, mul_one]
    exact_mod_cast this
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.compact_conjugate_centre_power_bounded E a ha Q hQ
  obtain ⟨Qf, C₁, hQf, hC₁, hent⟩ := GlobalTheory.T.compact_conjugate_rational_entries_bounded E a g₀ Q hQ n₀
  obtain ⟨C₂, N₂, hC₂, hcount⟩ := count_rational E Qf hQf
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : ℝ, c₃ = C₂ * (C₁ + 1) ^ N₂ := ⟨_, rfl⟩
  have hc₃0 : 0 ≤ c₃ := by rw [hc₃]; positivity
  refine ⟨(2 * n₀ + 1) * c₃ ^ (a * a), 2 * N₂ * (a * a), fun y => ?_⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = height y := ⟨_, rfl⟩
  rw [← hH]
  have hH1 : 1 ≤ H := hH ▸ one_le_height y
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (C₁ + 1) * H ^ 2 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    have : 1 ≤ H ^ 2 := one_le_pow₀ hH1
    nlinarith
  obtain ⟨hBf, hBc⟩ := hcount R hR1
  obtain ⟨B, hB⟩ : ∃ B : Finset E, B = hBf.toFinset := ⟨_, rfl⟩
  have hBmem : ∀ x, x ∈ B ↔ algebraMap E (Af E) x ∈ Qf ∧ ∀ w : InfinitePlace E, w x ≤ R := fun x => by
    rw [hB, Set.Finite.mem_toFinset]; rfl
  have hBcard : (B.card : ℝ) ≤ c₃ * H ^ (2 * N₂) := by
    have : B.card = {x : E | algebraMap E (Af E) x ∈ Qf ∧ ∀ w : InfinitePlace E, w x ≤ R}.ncard := by
      rw [hB]; exact (Set.ncard_eq_toFinset_card _ hBf).symm
    rw [this]
    refine hBc.trans_eq ?_
    rw [hR, mul_pow, hc₃, ← pow_mul]
    ring

  obtain ⟨P, hP⟩ : ∃ P : Finset (Fin a × Fin a → E), P = Fintype.piFinset fun _ => B := ⟨_, rfl⟩
  have hPcard : P.card = B.card ^ (a * a) := by
    simp [hP, Fintype.card_prod]
  have hinj : Function.Injective (fun (δ : GL (Fin a) E) (p : Fin a × Fin a) => δ.val p.1 p.2) := fun x y e =>
    Units.ext (Matrix.ext fun i j => congrFun e (i, j))
  obtain ⟨D, hD⟩ : ∃ D : Finset (GL (Fin a) E), D = P.preimage (fun (δ : GL (Fin a) E) (p : Fin a × Fin a) => δ.val p.1 p.2) hinj.injOn := ⟨_, rfl⟩
  have hDmem : ∀ δ : GL (Fin a) E, δ ∈ D ↔ (fun p : Fin a × Fin a => δ.val p.1 p.2) ∈ P := fun δ => by
    rw [hD, Finset.mem_preimage]
  have hDcard : D.card ≤ P.card :=
    Finset.card_le_card_of_injOn (fun (δ : GL (Fin a) E) (p : Fin a × Fin a) => δ.val p.1 p.2)
      (fun δ hδ => (hDmem δ).1 hδ) hinj.injOn
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℤ, J = Finset.Icc (-(n₀ : ℤ)) n₀ := ⟨_, rfl⟩
  have hJcard : (J.card : ℝ) = 2 * n₀ + 1 := by
    rw [hJ, Int.card_Icc]
    have : ((n₀ : ℤ) + 1 - -(n₀ : ℤ)).toNat = 2 * n₀ + 1 := by omega
    rw [this]; push_cast; ring
  obtain ⟨W, hW⟩ : ∃ W : Finset (GA E a), W = Finset.image₂ (fun (δ : GL (Fin a) E) (n : ℤ) => ratGL E a δ * splitCentre E a 1 ^ n) D J := ⟨_, rfl⟩
  have hsub : {γ : GA E a | γ ∈ latticeGL E a ∧ (g₀ * infGL E a y)⁻¹ * γ * (g₀ * infGL E a y) ∈ Q} ⊆ (W : Set (GA E a)) := by
    rintro γ ⟨hγ, hq⟩
    obtain ⟨δ, n, rfl⟩ := mem_latticeGL_iff.1 hγ
    have hn := hn₀ δ n _ hq
    have he := hent y δ n hn hq
    rw [Finset.mem_coe, hW, Finset.mem_image₂]
    refine ⟨δ, ?_, n, ?_, rfl⟩
    · refine (hDmem δ).2 ?_
      rw [hP, Fintype.mem_piFinset]
      rintro ⟨i, j⟩
      refine (hBmem _).2 ⟨(he i j).1, fun w => ((he i j).2 w).trans ?_⟩
      rw [hR, ← hH]
      have : 0 ≤ H ^ 2 := by positivity
      nlinarith
    · rw [hJ, Finset.mem_Icc]
      exact abs_le.1 hn
  refine ⟨W.finite_toSet.subset hsub, ?_⟩
  have h1 := Set.ncard_le_ncard hsub W.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  have h2 : W.card ≤ D.card * J.card := hW ▸ Finset.card_image₂_le _ _ _
  have h3 : (D.card : ℝ) ≤ (c₃ * H ^ (2 * N₂)) ^ (a * a) := by
    calc (D.card : ℝ) ≤ P.card := by exact_mod_cast hDcard
      _ = (B.card : ℝ) ^ (a * a) := by rw [hPcard]; push_cast; rfl
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hBcard _
  calc (_ : ℝ) ≤ W.card := by exact_mod_cast h1
    _ ≤ D.card * J.card := by exact_mod_cast h2
    _ ≤ (c₃ * H ^ (2 * N₂)) ^ (a * a) * (2 * n₀ + 1) := by
        rw [hJcard]; exact mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (2 * n₀ + 1) * c₃ ^ (a * a) * H ^ (2 * N₂ * (a * a)) := by
        rw [mul_pow, ← pow_mul]; ring

theorem moderate_growth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : Sm E a), (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) → MemL2Quotient (latticeGL E a) μ φ.1 → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a μ _ _ φ hl hc hlev hK hZ hL g
  classical
  letI : MeasurableSpace (AutomorphicForm.archGroup E a) := borel _
  haveI : BorelSpace (AutomorphicForm.archGroup E a) := ⟨rfl⟩
  have hφc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hlev
  have h1O : (1 : AdelicGLn.FiniteAdelicGL E a) ∈ {k | finRep E a k φ = φ} := by
    change finRep E a 1 φ = φ
    rw [map_one]; rfl
  obtain ⟨U, hU1, hUO, hUc⟩ := local_compact_nhds (hlev.mem_nhds h1O)
  obtain ⟨p, hpdef⟩ : ∃ p : GA E a → AutomorphicForm.archGroup E a,
      p = fun h => AutomorphicForm.archEquiv E a (AdelicGLn.prodEquiv E a h).1 := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : GA E a → AdelicGLn.FiniteAdelicGL E a,
      q = fun h => (AdelicGLn.prodEquiv E a h).2 := ⟨_, rfl⟩
  have hp : Continuous p := by
    rw [hpdef]
    exact (AutomorphicForm.archEquiv E a).continuous.comp
      (continuous_fst.comp (AdelicGLn.prodEquiv E a).continuous)
  have hq : Continuous q := by
    rw [hqdef]
    exact continuous_snd.comp (AdelicGLn.prodEquiv E a).continuous
  have hsplit : ∀ h, AutomorphicForm.infEmb E a (p h) * AutomorphicForm.finEmb E a (q h) = h := fun h => by
    rw [hpdef, hqdef]; exact AutomorphicForm.infEmb_mul_finEmb h
  have hright : ∀ x h, q h ∈ U → φ.1 (x * AutomorphicForm.infEmb E a (p h)) = φ.1 (x * h) := fun x h hh => by
    have hk : finRep E a (q h) φ = φ := hUO hh
    have := congrFun (congrArg Subtype.val hk) (x * AutomorphicForm.infEmb E a (p h))
    have e : x * AutomorphicForm.infEmb E a (p h) * finGL E a (q h) = x * h := by
      rw [mul_assoc, ← GlobalTheory.CompanionTheory.AutLevel.finEmb_eq_finGL, hsplit]
    exact this.symm.trans (congrArg φ.1 e)
  have hQm : MeasurableSet (q ⁻¹' U) := (hUc.isClosed.preimage hq).measurableSet
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (AutomorphicForm.archGroup E a), ν = (μ.restrict (q ⁻¹' U)).map p := ⟨_, rfl⟩
  haveI : ν.IsHaarMeasure := by
    rw [hν, hpdef, hqdef]
    exact GlobalTheory.T.finite_adelic_restriction_measure E a μ U hUc hU1
  obtain ⟨κ, hκc, hκs, hκ⟩ := GlobalTheory.T.finite_z_span_integral_representation E a φ hK hZ ν
  obtain ⟨S, hS⟩ : ∃ S, S = tsupport κ := ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸ hκs
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  obtain ⟨T, hT⟩ : ∃ T : Set (GA E a), T = p ⁻¹' S ∩ q ⁻¹' U := ⟨_, rfl⟩
  have hTc : IsCompact T := by
    let Φ : GA E a ≃ₜ AutomorphicForm.archGroup E a × AdelicGLn.FiniteAdelicGL E a :=
      (AdelicGLn.prodEquiv E a).toHomeomorph.trans
        ((AutomorphicForm.archEquiv E a).toHomeomorph.prodCongr (Homeomorph.refl _))
    have e : T = Φ ⁻¹' (S ×ˢ U) := by
      rw [hT, hpdef, hqdef]
      rfl
    rw [e]
    exact Φ.isCompact_preimage.2 (hSc.prod hUc)
  have hTm : MeasurableSet T := hTc.isClosed.measurableSet
  obtain ⟨Q, hQ⟩ : ∃ Q : Set (GA E a), Q = (fun x : GA E a × GA E a => x.1 * x.2⁻¹) '' (T ×ˢ T) := ⟨_, rfl⟩
  have hQc : IsCompact Q := hQ ▸ (hTc.prod hTc).image (by fun_prop)
  obtain ⟨C, N, hC⟩ := count_lattice E a g Q hQc

  have hF := isFundamentalDomain_stdDom (latticeGL E a) μ
  obtain ⟨hli, hmem⟩ := (memL2_iff_fundamental_domain hF).1 hL
  obtain ⟨I, hI⟩ : ∃ I, I = ∫⁻ x in stdDom (latticeGL E a), ‖φ.1 x‖ₑ ^ 2 ∂μ := ⟨_, rfl⟩
  have hItop : I ≠ ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num) (by norm_num)).1 hmem.eLpNorm_lt_top
    rw [hI]
    simpa using h.ne
  have hfm : Measurable fun x => ‖φ.1 x‖ₑ ^ 2 := (hφc.enorm.measurable).pow_const 2

  have hA : ∀ x, ∫⁻ s in S, ‖φ.1 (x * AutomorphicForm.infEmb E a s)‖ₑ ^ 2 ∂ν =
      ∫⁻ h in T, ‖φ.1 (x * h)‖ₑ ^ 2 ∂μ := by
    intro x
    have hG : Measurable fun s => ‖φ.1 (x * AutomorphicForm.infEmb E a s)‖ₑ ^ 2 :=
      ((hφc.comp (continuous_const.mul AutomorphicForm.continuous_infEmb)).enorm.measurable).pow_const 2
    rw [← lintegral_indicator hSm, hν, lintegral_map (hG.indicator hSm) hp.measurable, hT,
      ← Measure.restrict_restrict (hp.measurable hSm), ← lintegral_indicator (hp.measurable hSm)]
    refine lintegral_congr_ae ((ae_restrict_mem hQm).mono fun h hh => ?_)
    beta_reduce
    by_cases hs : p h ∈ S
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show h ∈ p ⁻¹' S from hs), hright x h hh]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (show h ∉ p ⁻¹' S from hs)]
  have hMm : ∀ x : GA E a, MeasurableSet ((fun h => x⁻¹ * h) ⁻¹' T) := fun x =>
    (continuous_const.mul continuous_id).measurable hTm
  have hB : ∀ x, ∫⁻ h in T, ‖φ.1 (x * h)‖ₑ ^ 2 ∂μ = ∫⁻ h in (fun h => x⁻¹ * h) ⁻¹' T, ‖φ.1 h‖ₑ ^ 2 ∂μ := by
    intro x
    rw [← lintegral_indicator hTm, ← lintegral_indicator (hMm x),
      ← lintegral_mul_left_eq_self (fun h => ((fun h => x⁻¹ * h) ⁻¹' T).indicator (fun h => ‖φ.1 h‖ₑ ^ 2) h) x]
    refine lintegral_congr fun h => ?_
    by_cases hh : h ∈ T
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (show x * h ∈ (fun h => x⁻¹ * h) ⁻¹' T by simpa using hh)]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (show x * h ∉ (fun h => x⁻¹ * h) ⁻¹' T by simpa using hh)]

  have hcnt : ∀ y, ∫⁻ h in (fun h => (g * infGL E a y)⁻¹ * h) ⁻¹' T, ‖φ.1 h‖ₑ ^ 2 ∂μ ≤
      ({γ : GA E a | γ ∈ latticeGL E a ∧ (g * infGL E a y)⁻¹ * γ * (g * infGL E a y) ∈ Q}.ncard : ℕ) * I := by
    intro y
    obtain ⟨x, hx⟩ : ∃ x, x = g * infGL E a y := ⟨_, rfl⟩
    rw [← hx, hI]
    refine GlobalTheory.T.fundamental_domain_integral_count_bound (latticeGL E a) μ _ hF _ (hMm x) _ hfm
      (fun γ hγ z => congrArg (fun u : ℂ => ‖u‖ₑ ^ 2) (hli γ hγ z)) _ fun z => ?_
    obtain ⟨hfin, -⟩ := hC y
    rw [← hx] at hfin
    rw [hfin.cast_ncard_eq]
    rcases Set.eq_empty_or_nonempty {γ : latticeGL E a | (γ : GA E a) * z ∈ (fun h => x⁻¹ * h) ⁻¹' T} with h0 | ⟨γ₀, h₀⟩
    · rw [h0]; simp
    have hinj : Set.InjOn (fun γ : latticeGL E a => (γ : GA E a) * (γ₀ : GA E a)⁻¹)
        {γ : latticeGL E a | (γ : GA E a) * z ∈ (fun h => x⁻¹ * h) ⁻¹' T} := fun u _ v _ e =>
      Subtype.ext (mul_right_cancel e)
    rw [← hinj.encard_image]
    refine Set.encard_le_encard ?_
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨mul_mem γ.2 (inv_mem γ₀.2), ?_⟩
    rw [hQ]
    refine ⟨(x⁻¹ * ((γ : GA E a) * z), x⁻¹ * ((γ₀ : GA E a) * z)), ⟨hγ, h₀⟩, ?_⟩
    simp only
    group

  obtain ⟨c₀, hc₀⟩ := hκc.bounded_above_of_compact_support hκs
  have hker : ∀ x, ‖φ.1 x‖ₑ ≤ ENNReal.ofReal c₀ * (ν S + ∫⁻ s in S, ‖φ.1 (x * AutomorphicForm.infEmb E a s)‖ₑ ^ 2 ∂ν) := by
    intro x
    have hG : Measurable fun s => ‖φ.1 (x * AutomorphicForm.infEmb E a s)‖ₑ ^ 2 :=
      ((hφc.comp (continuous_const.mul AutomorphicForm.continuous_infEmb)).enorm.measurable).pow_const 2
    have hsq : ∀ u : ℝ≥0∞, u ≤ 1 + u ^ 2 := fun u => by
      rcases le_total u 1 with h | h
      · exact h.trans le_self_add
      · calc u = u * 1 := (mul_one u).symm
          _ ≤ u * u := by gcongr
          _ = u ^ 2 := (sq u).symm
          _ ≤ 1 + u ^ 2 := le_add_self
    calc ‖φ.1 x‖ₑ = ‖∫ y, φ.1 (x * AutomorphicForm.infEmb E a y) * κ y ∂ν‖ₑ := by rw [← hκ x]
      _ ≤ ∫⁻ y, ‖φ.1 (x * AutomorphicForm.infEmb E a y) * κ y‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, S.indicator (fun s => ENNReal.ofReal c₀ * (1 + ‖φ.1 (x * AutomorphicForm.infEmb E a s)‖ₑ ^ 2)) y ∂ν := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ S
        · rw [Set.indicator_of_mem hy, enorm_mul, mul_comm]
          refine mul_le_mul' ?_ (hsq _)
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hc₀ y)
        · have h0 : κ y = 0 := image_eq_zero_of_notMem_tsupport (by rwa [← hS])
          rw [h0]
          simp
      _ = ENNReal.ofReal c₀ * ∫⁻ s in S, (1 + ‖φ.1 (x * AutomorphicForm.infEmb E a s)‖ₑ ^ 2) ∂ν := by
        rw [lintegral_indicator hSm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = _ := by
        rw [lintegral_add_left measurable_const, setLIntegral_one]
  have hc₀0 : 0 ≤ c₀ := (norm_nonneg _).trans (hc₀ 1)
  have hνS : ν S ≠ ⊤ := hSc.measure_lt_top.ne
  refine ⟨c₀ * ((ν S).toReal + C * I.toReal), N, fun y => ?_⟩
  obtain ⟨hfin, hn⟩ := hC y
  obtain ⟨n, hndef⟩ : ∃ n, n = {γ : GA E a | γ ∈ latticeGL E a ∧ (g * infGL E a y)⁻¹ * γ * (g * infGL E a y) ∈ Q}.ncard := ⟨_, rfl⟩
  have hbound := hcnt y
  rw [← hndef] at hbound hn
  have e1 : ‖φ.1 (g * infGL E a y)‖ₑ ≤ ENNReal.ofReal c₀ * (ν S + n * I) := by
    refine (hker _).trans ?_
    rw [hA, hB]
    gcongr
  have hH1 : 1 ≤ height y := one_le_height y
  have hHN : 1 ≤ height y ^ N := one_le_pow₀ hH1
  have e2 : ENNReal.ofReal c₀ * (ν S + n * I) = ENNReal.ofReal (c₀ * ((ν S).toReal + n * I.toReal)) := by
    rw [ENNReal.ofReal_mul hc₀0, ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
      ENNReal.ofReal_toReal hνS, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hItop,
      ENNReal.ofReal_natCast]
  rw [e2, ← ofReal_norm_eq_enorm] at e1
  have e3 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc₀0 (by positivity))).1 e1
  refine e3.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc₀0
  have hv : 0 ≤ (ν S).toReal := ENNReal.toReal_nonneg
  have hi : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  calc (ν S).toReal + n * I.toReal ≤ (ν S).toReal * height y ^ N + (C * height y ^ N) * I.toReal :=
        add_le_add (le_mul_of_one_le_right hv hHN) (mul_le_mul_of_nonneg_right hn hi)
    _ = ((ν S).toReal + C * I.toReal) * height y ^ N := by ring

end GlobalTheory.CompanionTheory.Growth

end
