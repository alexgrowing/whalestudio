import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneIsotropicStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SummableOneDivAbsNormSq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem lintegral_close {R : Type} [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) {S N : Set R}
    (hS : MeasurableSet S) (hfin : ν S ≠ ⊤) (hN : ν N = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ s ∈ S, s ∉ N → G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ) :
    |(∫⁻ s in S, G s ∂ν).toReal - (ν S).toReal| ≤ δ * (ν S).toReal := by
  have hae : ∀ᵐ s ∂(ν.restrict S), G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ := by
    rw [ae_restrict_iff' hS]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with s hs hsS
    exact h s hsS hs
  have hup : ∫⁻ s in S, G s ∂ν ≤ ENNReal.ofReal (1 + δ) * ν S := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).2])
  have hlo : ENNReal.ofReal (1 - δ) * ν S ≤ ∫⁻ s in S, G s ∂ν := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).1])
  have hfinU : ENNReal.ofReal (1 + δ) * ν S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hup' : (∫⁻ s in S, G s ∂ν).toReal ≤ (1 + δ) * (ν S).toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (1 - δ) * (ν S).toReal ≤ (∫⁻ s in S, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [abs_le]
  constructor <;> nlinarith

theorem density_close {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hM : 3 ≤ M) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lv : Measure (Fv F v)) (hlv : IsStdV v lv)
    (mv : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hmv : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M) (coordHerm (Fv F v) σ b lv 1) mv)
    {x δ : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 →
      |(mv (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ δ)
    (hav : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U →
      |(coordW (Fv F v) b lv 1 M (latV b v ∩ {X | algebraMap F (Fv F v) (1 / 2) *
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal -
        x * (lv V).toReal| ≤ ε * (lv V).toReal) :
    |x - 1| ≤ δ := by
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW 1 M
  obtain ⟨n1, n2⟩ := GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hσ M J hJ (by omega) v
    (coordW (Fv F v) b lv 1 M) lv (hW 1 M) hlv.1
  have hmv' : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M)
      (lv.map (hermScal (Fv F v) σ)) mv := by
    rw [(GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hσ (Fv F v) d b).2.2 lv hlv.1]
    exact hmv
  have FF := GlobalTheory.CompanionTheory.SW.isFibreFamily_length F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) _ lv
    (hW 1 M) hlv.1 n1 n2 mv hmv'
  have hqc : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0) :=
    GlobalTheory.CompanionTheory.SW.LenFib.continuous_qR (Fv F v) hσ J
  obtain ⟨hLc, hLo, -, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have hLm : MeasurableSet (latV (M := M) (n := 1) b v) := hLo.measurableSet

  let φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ := (latV b v).indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hLo.frontier_eq, hLc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hLc fun X hX => ?_
    exact Set.indicator_of_notMem hX _
  obtain ⟨hI, -⟩ := FF.2.2 φ hφc hφs (Set.subset_univ _)
  have hfinG : ∀ s : Fv F v, s ≠ 0 → mv (hermScal (Fv F v) σ s) (latV b v) ≠ ⊤ := by
    intro s hs
    have h := hI s (isUnit_iff_ne_zero.2 hs)
    rw [integrable_indicator_iff hLm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨U, hU, hUV⟩ := hav ε hε
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  set S : Set (Fv F v) := interior U ∩ (v.adicCompletionIntegers F : Set (Fv F v)) with hSdef
  have hSo : IsOpen S := isOpen_interior.inter hOo
  have h0S : (0 : Fv F v) ∈ S := ⟨mem_interior_iff_mem_nhds.2 hU, zero_mem _⟩
  have hSfin : lv S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [hlv.2]
    exact ENNReal.one_ne_top
  have hSpos : 0 < (lv S).toReal :=
    ENNReal.toReal_pos (hSo.measure_ne_zero lv ⟨0, h0S⟩) hSfin
  have h1 := hUV S hSo.measurableSet (Set.inter_subset_left.trans interior_subset)
  have h2 := lintegral_close lv (fun s => mv (hermScal (Fv F v) σ s) (latV b v)) hSo.measurableSet hSfin
    n1 hδ (fun s hs hs0 => ⟨hfinG s (not_not.1 hs0).ne_zero, hB s hs.2 (not_not.1 hs0).ne_zero⟩)
  rw [← GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.fibre_mass_eq _ lv _ hqc.measurable _ _ FF hLm hSo.measurableSet] at h2
  have h3 : |x - 1| * (lv S).toReal ≤ (δ + ε) * (lv S).toReal := by
    have e : (x - 1) * (lv S).toReal = (x * (lv S).toReal -
        (coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal) +
        ((coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        (lv S).toReal) := by ring
    rw [← abs_of_pos hSpos, ← abs_mul, abs_of_pos hSpos, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm]
    have h1' : |(coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        x * (lv S).toReal| ≤ ε * (lv S).toReal := h1
    linarith
  exact le_of_mul_le_mul_right h3 hSpos

end GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal - 1| := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b lam hlam m hm
  have hL := fun v => GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have avg := fun v => GlobalTheory.T.local_volume_rank_one_isotropic F E σ hσ M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v)
    (latV b v) (hL v).1 (hL v).2.1
  refine ⟨fun v => (avg v).1, ?_⟩
  refine Summable.of_norm_bounded_eventually
    (g := fun v : HeightOneSpectrum (𝓞 F) => 2 * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
    ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left 2) ?_
  filter_upwards [GlobalTheory.T.rank_one_local_density_almost_all F E σ hσ M J hJ hM d b] with v hv
  obtain ⟨m', hm'⟩ := GlobalTheory.CompanionTheory.SW.GoodMass.exists_family hσ hJ b v (lam v) (hlam v) 1
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := GlobalTheory.CompanionTheory.SW.GoodMass.absNorm_one_le v
  have hd := GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.density_close hσ hJ hM b v (lam v) (hlam v) m' hm'
    (x := (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal)
    (δ := 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1)) (by positivity)
    (hv (lam v) (hlam v) m' hm') (avg v).2
  rw [Real.norm_eq_abs, abs_abs]
  refine hd.trans ?_
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ hq (by omega))
