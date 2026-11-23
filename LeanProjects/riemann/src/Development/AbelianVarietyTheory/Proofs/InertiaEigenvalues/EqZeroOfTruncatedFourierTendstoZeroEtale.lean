import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_char (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := ψ x)).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
  have h1 : ψ (z - x) = 1 := hψ.1 _ (by simpa [dist_eq_norm] using hz)
  calc ψ x = ψ x * ψ (z - x) := by rw [h1, mul_one]
    _ = ψ z := by rw [← AddChar.map_add_eq_mul]; congr 1; abel

theorem kerK_eq (A : Et F E) (ψ : AddChar F ℂ) :
    A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
  funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]

theorem continuous_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (y : A.K) :
    Continuous fun x => A.kerK ψ x y := by
  have hl : Continuous ((Algebra.trace F A.K).comp (LinearMap.mulRight F y)) :=
    IsModuleTopology.continuous_of_linearMap _
  exact ((continuous_char ψ hψ).comp hl).congr (fun x => by simp [Et.kerK, Et.psiK])

theorem integrable_mul_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f : A.K → ℂ} (hf : IsTest f) (y : A.K) :
    Integrable (fun x => f x * A.kerK ψ x y) μ :=
  (hf.1.continuous.mul (continuous_kerK A ψ hψ y)).integrable_of_hasCompactSupport hf.2.mul_right

theorem fourB_sub (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f g : A.K → ℂ} (hf : IsTest f) (hg : IsTest g) (y : A.K) :
    fourB μ (A.kerK ψ) (f - g) y = fourB μ (A.kerK ψ) f y - fourB μ (A.kerK ψ) g y := by
  unfold fourB
  rw [← integral_sub (integrable_mul_kerK A ψ hψ μ hf y) (integrable_mul_kerK A ψ hψ μ hg y)]
  congr 1; funext x; simp [sub_mul]

theorem lintegral_sq_eq_ofReal {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {g : X → ℂ} (hg : IsTest g) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hc : Continuous fun x => ‖g x‖ ^ 2 := (hg.1.continuous.norm).pow 2
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ g) := hg.2.comp_left (by simp)
  rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hs)
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; positivity)]
  congr 1; funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable [Unram F E]

theorem isTest_fourB (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) : IsTest (fourB μK (A.kerK ψ) f) := by
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  rw [kerK_eq A ψ]
  exact (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd).2 μK hsd.1 f hf

theorem plancherel (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) :
    ∫⁻ y, ‖fourB μK (A.kerK ψ) f y‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μK := by
  haveI := hsd.1
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hB := kerK_eq A ψ
  have hP := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd μK
    hsd.1).2 (hB ▸ hsd) f hf
  rw [lintegral_sq_eq_ofReal μK (isTest_fourB A ψ hψ μK hsd hf), lintegral_sq_eq_ofReal μK hf, hB, hP]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def box (A : Et F E) (c : F) : Set A.K := {z | c • z ∈ A.OK}

theorem isOpen_box (A : Et F E) (hO : IsOpen A.OK) (c : F) : IsOpen (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isClosed_box (A : Et F E) (hO : IsClosed A.OK) (c : F) : IsClosed (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isCompact_box (A : Et F E) (hO : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsCompact (box A c) :=
  (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).2 hO

theorem isTest_indicator_box (A : Et F E) {u : A.K → ℂ} (hu : IsLocallyConstant u) (hOo : IsOpen A.OK)
    (hOc : IsClosed A.OK) (hOk : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsTest ((box A c).indicator u) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_box A hOk hc) (isClosed_box A hOc c)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ box A c
  · filter_upwards [(isOpen_box A hOo c).mem_nhds hx, (IsLocallyConstant.iff_eventually_eq u).1 hu x] with y hy h
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx, h]
  · filter_upwards [(isClosed_box A hOc c).isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem fourB_indicator_box (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.K) (u : A.K → ℂ) (c : F)
    (hM : MeasurableSet (box A c)) (y : A.K) :
    fourB μ (A.kerK ψ) ((box A c).indicator u) y = ∫ z in box A c, u z * A.psiK ψ (-((-y) * z)) ∂μ := by
  unfold fourB
  have h : ∀ x, (box A c).indicator u x * A.kerK ψ x y = (box A c).indicator (fun x => u x * A.kerK ψ x y) x :=
    fun x => by by_cases hx : x ∈ box A c <;> simp [hx]
  simp_rw [h]
  rw [integral_indicator hM]
  congr 1; funext z
  rw [Et.kerK, neg_mul, neg_neg, mul_comm z y]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

theorem eq_zero_of_tendsto_fourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd u hu hT hlim
  haveI := hsd.1
  obtain ⟨-, -, -, -, -, -, -, -, hnull, hOo, hOk, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hOc : IsClosed A.OK := by
    have hRo : IsOpen ((R.toAddSubgroup : AddSubgroup A.K) : Set A.K) := by rw [← hR] at hOo; exact hOo
    rw [← hR]; exact R.toAddSubgroup.isClosed_of_isOpen hRo
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one F
  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1
  have hne : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n (norm_pos_iff.1 hϖ0)
  have hpow' : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hpow, Eventually.of_forall hne⟩
  set M : ℕ → Set A.K := fun n => box A (ϖ ^ n) with hMdef
  have hMm : ∀ n, MeasurableSet (M n) := fun n => (isOpen_box A hOo _).measurableSet
  set g : ℕ → A.K → ℂ := fun n => (M n).indicator u with hgdef
  have hg : ∀ n, IsTest (g n) := fun n => isTest_indicator_box A hu hOo hOc hOk (hne n)
  have hTc : ∀ n, Continuous (fourB μK (A.kerK ψ) (g n)) := fun n =>
    (isTest_fourB A ψ hψ μK hsd (hg n)).1.continuous
  have huc : Continuous u := hu.continuous
  have hum : Measurable fun z => ‖u z‖ₑ ^ 2 := (huc.measurable.enorm).pow_const 2
  set b : ℕ → ENNReal := fun n => ∫⁻ z, (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z ∂μK with hbdef
  have hev : ∀ z : A.K, ∀ᶠ n in atTop, z ∈ M n := by
    intro z
    have ht : Tendsto (fun n : ℕ => ϖ ^ n • z) atTop (𝓝 0) := by
      simpa using hpow.smul_const z
    exact ht (hOo.mem_nhds h0)
  have hb : Tendsto b atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μK)
      (F := fun n z => (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z) (f := fun _ => 0) (fun z => ‖u z‖ₑ ^ 2)
      (fun n => hum.indicator (hMm n).compl) (fun n => ae_of_all _ fun z => Set.indicator_le_self _ _ z) hT.ne
      (ae_of_all _ fun z => tendsto_const_nhds.congr'
        ((hev z).mono fun n hn => (Set.indicator_of_notMem (fun h : z ∈ (M n)ᶜ => h hn) _).symm))
    simpa using this
  have hlimF : ∀ y : A.K, IsUnit y → Tendsto (fun n => fourB μK (A.kerK ψ) (g n) y) atTop (𝓝 0) := by
    intro y hy
    exact ((hlim (-y) hy.neg).comp hpow').congr fun n => (fourB_indicator_box A ψ μK u _ (hMm n) y).symm
  have hae : ∀ᵐ y ∂μK, IsUnit y := ae_iff.2 (hnull μK hsd.1)
  have key : ∀ N, ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK ≤ b N := by
    intro N
    rw [← plancherel A ψ hψ μK hsd (hg N)]
    have hFd : ∀ n, ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK
        = ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK := by
      intro n
      have := plancherel A ψ hψ μK hsd (f := g N - g n) ⟨(hg N).1.sub (hg n).1, (hg N).2.sub (hg n).2⟩
      simp only [Pi.sub_apply] at this
      rw [← this]
      congr 1; funext y
      rw [fourB_sub A ψ hψ μK (hg N) (hg n) y]
    have hpt : ∀ n x, ‖g N x - g n x‖ₑ ^ 2 ≤
        (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x := by
      intro n x
      by_cases h1 : x ∈ M N <;> by_cases h2 : x ∈ M n <;> simp [g, h1, h2]
    have hle : ∀ n, ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK ≤ b N + b n := by
      intro n
      calc _ ≤ ∫⁻ x, ((M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK :=
            lintegral_mono (hpt n)
        _ = b N + b n := lintegral_add_left (hum.indicator (hMm N).compl) _
    have hliminf : ∀ᵐ y ∂μK,
        liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop
          = ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 := by
      filter_upwards [hae] with y hy
      have ht := ((ENNReal.continuous_pow 2).tendsto _).comp
        ((continuous_enorm.tendsto _).comp ((tendsto_const_nhds (x := fourB μK (A.kerK ψ) (g N) y)).sub (hlimF y hy)))
      simpa [Function.comp_def] using ht.liminf_eq
    calc ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 ∂μK
        = ∫⁻ y, liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop ∂μK :=
          lintegral_congr_ae (hliminf.mono fun y h => h.symm)
      _ ≤ liminf (fun n => ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK) atTop :=
          lintegral_liminf_le' fun n => ((((hTc N).sub (hTc n)).measurable.enorm).pow_const 2).aemeasurable
      _ = liminf (fun n => ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK) atTop := by simp_rw [hFd]
      _ ≤ liminf (fun n => b N + b n) atTop := liminf_le_liminf (Eventually.of_forall hle)
      _ = b N := by
          have : Tendsto (fun n => b N + b n) atTop (𝓝 (b N + 0)) := tendsto_const_nhds.add hb
          simpa using this.liminf_eq
  have hsplit : ∀ N, ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := by
    intro N
    calc ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK
        = ∫⁻ x, (‖g N x‖ₑ ^ 2 + (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK := by
          congr 1; funext x
          by_cases h : x ∈ M N <;> simp [g, h]
      _ = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := lintegral_add_right _ (hum.indicator (hMm N).compl)
  have hT0 : ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = 0 := by
    refine le_antisymm ?_ (by simp)
    have h2 : Tendsto (fun N => b N + b N) atTop (𝓝 0) := by simpa using hb.add hb
    exact ge_of_tendsto' h2 fun N => (hsplit N).trans_le (add_le_add (key N) le_rfl)
  have hae0 : u =ᵐ[μK] 0 := by
    filter_upwards [(lintegral_eq_zero_iff hum).1 hT0] with z hz
    simpa using hz
  exact (Continuous.ae_eq_iff_eq μK huc continuous_const).1 hae0

end GlobalTheory.PlancherelZero
