import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Definitions.Divisors.KerInfIntegrableOfMemRspan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUniformBound

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Matrix

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def IsLocModerate (F : GA E a → ℂ) : Prop :=
  ∀ g₀ : GA E a, ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ᶠ g in 𝓝 g₀, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

theorem continuous_mapGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] {p : R →+* S} (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) :=
  Continuous.units_map _ (continuous_id.matrix_map hp)

theorem continuous_pInf_ad : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_pFin_ad : Continuous (pFin E) := continuous_snd

theorem continuous_height_inf : Continuous (height : GL (Fin a) (Cinf E) → ℝ) := by
  have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
  show Continuous fun y : GL (Fin a) (Cinf E) => 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
  exact (continuous_const.add (ht.comp Units.continuous_val).norm).add (ht.comp Units.continuous_coe_inv).norm

theorem isAutForm_continuous_locModerate {φ : Sm E a} (hA : IsAutForm φ) : Continuous φ.1 ∧ IsLocModerate φ.1 := by
  have cI : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g := continuous_mapGL continuous_pInf_ad
  have cF : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g := continuous_mapGL continuous_pFin_ad
  have dec : ∀ g₀ g : GA E a, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ → ∀ y,
      φ.1 (g * infGL E a y) = φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)) := by
    intro g₀ g hk y
    have hu : g = g₀ * (infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) := by
      rw [infGL_mul_finGL, mul_inv_cancel_left]
    have e : g * infGL E a y = g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) *
        finGL E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) := by
      conv_lhs => rw [hu]
      rw [map_mul (infGL E a) (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) y]
      simp only [mul_assoc]
      rw [← infGL_comm]
    rw [e]
    exact congrArg (fun ψ : Sm E a => ψ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))) hk
  have nb : ∀ g₀ : GA E a, ∀ᶠ g in 𝓝 g₀, finRep E a (GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g)) φ = φ := by
    intro g₀
    have hc : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) :=
      cF.comp (continuous_const.mul continuous_id)
    refine hc.continuousAt.preimage_mem_nhds (hA.level.mem_nhds ?_)
    simp
  refine ⟨continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · have e : (fun g => φ.1 g) =ᶠ[𝓝 g₀]
        fun g => chart φ.1 g₀ (toL (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
      filter_upwards [nb g₀] with g hg
      rw [chart_val]
      have := dec g₀ g hg 1
      simp only [map_one, mul_one] at this
      exact this
    refine ContinuousAt.congr ?_ e.symm
    refine ContinuousAt.comp_of_eq (contDiffAt_chart (x := oneL E a) φ.2 g₀ isUnit_one).continuousAt ?_
      (by simp [oneL])
    have ht : Continuous fun x : Matrix (Fin a) (Fin a) (Cinf E) => toL x := continuous_id
    exact ((ht.comp Units.continuous_val).comp (cI.comp (continuous_const.mul continuous_id))).continuousAt
  · obtain ⟨C, N, hC⟩ := hA.growth g₀
    have ha : (0 : ℝ) ≤ 1 + 2 * a := by positivity
    have h1' := one_le_height (1 : GL (Fin a) (Cinf E))
    refine ⟨|C| * ((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) ^ N, N,
      mul_nonneg (abs_nonneg C) (pow_nonneg (mul_nonneg ha (by linarith)) N), ?_⟩
    have hh : ∀ᶠ g in 𝓝 g₀, height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) <
        height (1 : GL (Fin a) (Cinf E)) + 1 := by
      have hc : Continuous fun g : GA E a => height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) :=
        continuous_height_inf.comp (cI.comp (continuous_const.mul continuous_id))
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [nb g₀, hh] with g hg hg' y
    rw [dec g₀ g hg y]
    have h1 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g))
    have h2 := one_le_height y
    have h3 := one_le_height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y)
    calc ‖φ.1 (g₀ * infGL E a (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y))‖
        ≤ C * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N := hC _
      _ ≤ |C| * height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g) * y) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)
      _ ≤ |C| * ((1 + 2 * a) * (height (GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)) * height y)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (RapidModel.height_mul_le _ y) N) (abs_nonneg C)
      _ ≤ |C| * (((1 + 2 * a) * (height (1 : GL (Fin a) (Cinf E)) + 1)) * height y) ^ N := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀
            (mul_nonneg ha (mul_nonneg (by linarith) (by linarith))) ?_ N) (abs_nonneg C)
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg'.le ha) (by linarith)
      _ = _ := by rw [mul_pow]; ring

variable (π : CuspSub E a) in

def regSpan : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F}
  add_mem' := fun {F G} hF hG => by
    refine ⟨add_mem hF.1 hG.1, hF.2.1.add hG.2.1, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e1⟩ := hF.2.2 g₀
    obtain ⟨C', N', h0', e2⟩ := hG.2.2 g₀
    refine ⟨C + C', N + N', add_nonneg h0 h0', ?_⟩
    filter_upwards [e1, e2] with g h1 h2 y
    have hy := one_le_height y
    have p1 : height y ^ N ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    have p2 : height y ^ N' ≤ height y ^ (N + N') := pow_le_pow_right₀ hy (by omega)
    refine (norm_add_le _ _).trans ?_
    nlinarith [h1 y, h2 y, mul_le_mul_of_nonneg_left p1 h0, mul_le_mul_of_nonneg_left p2 h0']
  zero_mem' := ⟨zero_mem _, continuous_zero, fun _ => ⟨0, 0, le_rfl, Eventually.of_forall fun _ _ => by simp⟩⟩
  smul_mem' c F hF := by
    refine ⟨Submodule.smul_mem _ c hF.1, hF.2.1.const_smul c, fun g₀ => ?_⟩
    obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨‖c‖ * C, N, mul_nonneg (norm_nonneg _) h0, ?_⟩
    filter_upwards [e] with g h y
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} :
    F ∈ regSpan π ↔ F ∈ rspan π ∧ Continuous F ∧ IsLocModerate F := Iff.rfl

theorem rt_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ regSpan π := by
  refine ⟨rt_mem_rspan hF.1 h, hF.2.1.comp (continuous_mul_right h), fun g₀ => ?_⟩
  obtain ⟨y₀, k, rfl⟩ : ∃ y₀ k, h = infGL E a y₀ * finGL E a k := ⟨_, _, (infGL_mul_finGL h).symm⟩
  obtain ⟨C, N, h0, e⟩ := hF.2.2 (g₀ * finGL E a k)
  have hy₀ := one_le_height y₀
  refine ⟨C * ((1 + 2 * a) * height y₀) ^ N, N, mul_nonneg h0 (pow_nonneg (mul_nonneg (by positivity)
    (by linarith)) N), ?_⟩
  have ht : Tendsto (fun g => g * finGL E a k) (𝓝 g₀) (𝓝 (g₀ * finGL E a k)) := (continuous_mul_right _).tendsto g₀
  filter_upwards [ht.eventually e] with g hg z
  have ex : g * infGL E a z * (infGL E a y₀ * finGL E a k) = g * finGL E a k * infGL E a (z * y₀) := by
    rw [mul_assoc g (finGL E a k), ← infGL_comm, map_mul]; simp only [mul_assoc]
  change ‖F (g * infGL E a z * (infGL E a y₀ * finGL E a k))‖ ≤ _
  rw [ex]
  refine (hg _).trans ?_
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (z * y₀)]) ?_ N) h0
  exact (RapidModel.height_mul_le z y₀).trans_eq (by ring)

theorem kerInf_mem_regSpan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ regSpan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ regSpan π := by
  have hM := RapidModel.rspan_le_modGr π hF.1
  refine ⟨kerInf_mem_rspan hF.1 ν hk, continuous_iff_continuousAt.2 fun g₀ => ?_, fun g₀ => ?_⟩
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    show ContinuousAt (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) g₀
    refine continuousAt_of_dominated (bound := fun x => C * (‖k x‖ * height (γ x) ^ N))
      (Eventually.of_forall fun g => (RapidModel.integrable_of_modGr hM hk g).aestronglyMeasurable) ?_
      ((hk.2.2 N).const_mul C)
      (Eventually.of_forall fun x => (continuous_const.mul (hF.2.1.comp (continuous_mul_right _))).continuousAt)
    filter_upwards [e] with g hg
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul]
    calc ‖k x‖ * ‖F (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hg _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring
  · obtain ⟨C, N, h0, e⟩ := hF.2.2 g₀
    refine ⟨C * (1 + 2 * a) ^ N * ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν, N, ?_, ?_⟩
    · refine mul_nonneg (by positivity) (integral_nonneg fun x => ?_)
      have := one_le_height (γ x)
      positivity
    · filter_upwards [e] with g hC z
      rw [kerInf]
      calc _ ≤ ∫ x, (C * (1 + 2 * a) ^ N * height z ^ N) * (‖k x‖ * height (γ x) ^ N) ∂ν := by
            refine norm_integral_le_of_norm_le ((hk.2.2 N).const_mul _) (Eventually.of_forall fun x => ?_)
            rw [norm_mul, mul_assoc g, ← map_mul]
            have h1 := (hC (z * γ x)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [one_le_height (z * γ x)]) (RapidModel.height_mul_le z (γ x)) N) h0)
            refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_eq ?_
            rw [mul_pow, mul_pow]; ring
        _ = _ := by rw [integral_const_mul]; ring

theorem IsLocModerate.bound_of_isCompact {F : GA E a → ℂ} (hF : IsLocModerate F) {K : Set (GA E a)}
    (hK : IsCompact K) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g ∈ K, ∀ y, ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first
  | exact @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound
  | (apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompactUniformHeightBound.compact_uniform_bound ..)

theorem locSpan_le_regSpan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    locSpan S φ.1 ≤ regSpan π :=
  locSpan_le (mem_regSpan.2 ⟨mem_rspan hφ, isAutForm_continuous_locModerate (π.cusp φ hφ).1⟩)
    (fun _ hF h _ => rt_mem_regSpan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_regSpan hF ν hk

end GlobalTheory.JSW.MirSemi

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory in

theorem GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
      (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, Continuous F ∧
        ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
          ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  intro E _ _ _ a S π φ hφ F hF
  have hG := GlobalTheory.JSW.MirSemi.locSpan_le_regSpan hφ S hF
  refine ⟨hG.2.1, fun K hK => ?_⟩
  obtain ⟨C, N, -, h⟩ := hG.2.2.bound_of_isCompact hK
  exact ⟨C, N, h⟩
