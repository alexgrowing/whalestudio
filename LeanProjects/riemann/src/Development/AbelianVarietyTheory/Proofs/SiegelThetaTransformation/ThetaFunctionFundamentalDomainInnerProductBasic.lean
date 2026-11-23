import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ScalarProduct

open GlobalTheory.HeisOrtho

theorem mul_conj_polar (a b : ℂ) : a * conj b =
    (1 / 4 : ℂ) * (((‖a + (1 : ℂ) * b‖ ^ 2 : ℝ) : ℂ) - ((‖a + (-1 : ℂ) * b‖ ^ 2 : ℝ) : ℂ) +
      I * ((‖a + I * b‖ ^ 2 : ℝ) : ℂ) - I * ((‖a + (-I) * b‖ ^ 2 : ℝ) : ℂ)) := by
  have h : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, h, h, h]
  simp only [map_add, map_mul, map_neg, map_one, Complex.conj_I]
  linear_combination ((a * conj b - b * conj a) / 2) * Complex.I_sq

section Meas

variable {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

def BM (f : X → ℂ) : Prop := Measurable f ∧ ∃ b : ℝ, ∀ w, ‖f w‖ ≤ b

omit [IsFiniteMeasure ν] in
theorem BM.add_smul {f g : X → ℂ} (hf : BM f) (hg : BM g) (c : ℂ) : BM (f + c • g) := by
  obtain ⟨hfm, bf, hbf⟩ := hf
  obtain ⟨hgm, bg, hbg⟩ := hg
  refine ⟨hfm.add (hgm.const_smul c), bf + ‖c‖ * bg, fun w => ?_⟩
  show ‖f w + c * g w‖ ≤ bf + ‖c‖ * bg
  calc ‖f w + c * g w‖ ≤ ‖f w‖ + ‖c * g w‖ := norm_add_le _ _
    _ = ‖f w‖ + ‖c‖ * ‖g w‖ := by rw [norm_mul]
    _ ≤ bf + ‖c‖ * bg := add_le_add (hbf w) (mul_le_mul_of_nonneg_left (hbg w) (norm_nonneg c))

theorem integrable_mul_conj {f g : X → ℂ} (hf : BM f) (hg : BM g) :
    Integrable (fun w => f w * conj (g w)) ν := by
  obtain ⟨hfm, bf, hbf⟩ := hf
  obtain ⟨hgm, bg, hbg⟩ := hg
  refine Integrable.mono' (integrable_const (bf * bg))
    (hfm.mul (Complex.continuous_conj.measurable.comp hgm)).aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hbf w) (hbg w) (norm_nonneg _) ((norm_nonneg _).trans (hbf w))

theorem integrable_normSq {f : X → ℂ} (hf : BM f) : Integrable (fun w => ((‖f w‖ ^ 2 : ℝ) : ℂ)) ν := by
  refine (integrable_mul_conj ν hf hf).congr (ae_of_all _ fun w => ?_)
  show f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem integral_polar {f g : X → ℂ} (hf : BM f) (hg : BM g) :
    ∫ w, f w * conj (g w) ∂ν =
      (1 / 4 : ℂ) * (((∫ w, ‖(f + (1 : ℂ) • g) w‖ ^ 2 ∂ν : ℝ) : ℂ) - ((∫ w, ‖(f + (-1 : ℂ) • g) w‖ ^ 2 ∂ν : ℝ) : ℂ) +
        I * ((∫ w, ‖(f + I • g) w‖ ^ 2 ∂ν : ℝ) : ℂ) - I * ((∫ w, ‖(f + (-I) • g) w‖ ^ 2 ∂ν : ℝ) : ℂ)) := by
  have hInt : ∀ c : ℂ, Integrable (fun w => ((‖(f + c • g) w‖ ^ 2 : ℝ) : ℂ)) ν :=
    fun c => integrable_normSq ν (hf.add_smul hg c)
  have iA := hInt 1
  have iB := hInt (-1)
  have iC := (hInt I).const_mul I
  have iD := (hInt (-I)).const_mul I
  calc ∫ w, f w * conj (g w) ∂ν
      = ∫ w, (1 / 4 : ℂ) * (((‖(f + (1 : ℂ) • g) w‖ ^ 2 : ℝ) : ℂ) - ((‖(f + (-1 : ℂ) • g) w‖ ^ 2 : ℝ) : ℂ) +
          I * ((‖(f + I • g) w‖ ^ 2 : ℝ) : ℂ) - I * ((‖(f + (-I) • g) w‖ ^ 2 : ℝ) : ℂ)) ∂ν :=
        integral_congr_ae (ae_of_all _ fun w => mul_conj_polar (f w) (g w))
    _ = _ := by
        rw [integral_const_mul, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul]
        all_goals first
          | simp only [integral_complex_ofReal]
          | exact iA | exact iB | exact iC | exact iD | exact iA.sub iB | exact (iA.sub iB).add iC

omit [IsFiniteMeasure ν] in
theorem integral_normSq_eq {f : X → ℂ} (hf : Measurable f) :
    ∫ w, ‖f w‖ ^ 2 ∂ν = (∫⁻ w, ‖f w‖ₑ ^ 2 ∂ν).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun w => sq_nonneg _)
    (hf.norm.pow_const 2).aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem norm_add_ratL_eq_of_isTh {D : D7} {S T : HSp D} (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) :
    ∀ γ : WO S T, γ ∈ ratL T S → ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  intro γ hγ w
  obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 hγ
  have hf' : IsThetaFunO C.ψ S T f := hf
  show ‖f (ratW T S y + w)‖ = ‖f w‖
  rw [hf'.quasi y w, norm_mul, C.std.1.2.1, one_mul]

private theorem exists_norm_le_of_isTh {D : D7} {S T : HSp D} (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) :
    ∃ b : ℝ, ∀ w, ‖f w‖ ≤ b := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hf' : IsThetaFunO C.ψ S T f := hf
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hf'.cont.continuousOn
  refine ⟨b, fun w => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hKc w
  rw [← norm_add_ratL_eq_of_isTh C hf γ hγ w]
  exact hb _ hγK

private theorem bm_of_isTh {D : D7} {S T : HSp D} (C : Ctx S T) {f : WO S T → ℂ} (hf : C.IsTh f) : BM f := by
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have hf' : IsThetaFunO C.ψ S T f := hf
  exact ⟨hf'.cont.measurable, exists_norm_le_of_isTh C hf⟩

private theorem mul_conj_add_ratL_eq_of_isTh {D : D7} {S T : HSp D} (C : Ctx S T) {f g : WO S T → ℂ} (hf : C.IsTh f)
    (hg : C.IsTh g) : ∀ γ : WO S T, γ ∈ ratL T S → ∀ w, f (γ + w) * conj (g (γ + w)) = f w * conj (g w) := by
  intro γ hγ w
  obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.1 hγ
  have hf' : IsThetaFunO C.ψ S T f := hf
  have hg' : IsThetaFunO C.ψ S T g := hg
  show f (ratW T S y + w) * conj (g (ratW T S y + w)) = f w * conj (g w)
  rw [hf'.quasi y w, hg'.quasi y w, map_mul]
  have hz : C.ψ (-symplOH S T (ratW T S y) w) * conj (C.ψ (-symplOH S T (ratW T S y) w)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, C.std.1.2.1]
    norm_num
  linear_combination (f w * conj (g w)) * hz

end Meas

theorem ip_basic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f, C.IsTh f → (∃ b : ℝ, ∀ w, ‖f w‖ ≤ b) ∧ (ipO μ 𝓕 f f = 0 → f = 0) ∧ ipO μ 𝓕 f f = nrm2 μ 𝓕 f ∧ ∀ f', C.IsTh f' → IntegrableOn (fun w => f w * conj (f' w)) 𝓕 μ ∧ ipO μ 𝓕 f' f = conj (ipO μ 𝓕 f f') ∧ (∀ a : ℂ, ipO μ 𝓕 (a • f) f' = a * ipO μ 𝓕 f f') ∧ (∀ f'', C.IsTh f'' → ipO μ 𝓕 (f + f') f'' = ipO μ 𝓕 f f'' + ipO μ 𝓕 f' f'') ∧ (∀ w, ipO μ 𝓕 (C.rho w f) (C.rho w f') = ipO μ 𝓕 f f') ∧ ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ p, ipO μ 𝓕 (om p f) (om p f') = ipO μ 𝓕 f f' := by
  intro D S T C
  obtain ⟨hTG, hLC, hSC, hT2, hDisc, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : IsTopologicalAddGroup (WO S T) := hTG
  have : LocallyCompactSpace (WO S T) := hLC
  have : SecondCountableTopology (WO S T) := hSC
  have : SecondCountableTopology (WA T S) := hSC
  have : T2Space (WO S T) := hT2
  have : DiscreteTopology (ratL T S) := hDisc
  have : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  refine ⟨?_, fun μ 𝓕 hμ f hf => ?_⟩
  · obtain ⟨⟨μ, 𝓕, h1, h2, h3⟩, -⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc
      (fun _ => (1 : ℂ)) continuous_const (fun h => one_ne_zero (congrFun h 0)) (fun _ _ _ => rfl)
    refine ⟨μ, 𝓕, ?_⟩
    unfold IsCovolOne
    exact ⟨h1, h2, h3⟩
  unfold IsCovolOne at hμ
  obtain ⟨hH, hFD, h1⟩ := hμ
  have : VAddInvariantMeasure (ratL T S) (WO S T) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hbm : ∀ g, C.IsTh g → BM g := fun g hg => bm_of_isTh C hg
  have hf' : IsThetaFunO C.ψ S T f := hf
  have hnorm : ipO μ 𝓕 f f = nrm2 μ 𝓕 f := by
    unfold ipO nrm2
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show f w * conj (f w) = ((‖f w‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨exists_norm_le_of_isTh C hf, ?_, hnorm, fun f' hf2 => ?_⟩
  · intro h0
    rw [hnorm] at h0
    unfold nrm2 at h0
    have h0' : ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
    have hint : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict 𝓕) := by
      obtain ⟨hm, b, hb⟩ := hbm f hf
      refine Integrable.mono' (integrable_const (b ^ 2)) (hm.norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb w) 2
    have hae := (integral_eq_zero_iff_of_nonneg (by intro w; exact sq_nonneg _) hint).1 h0'
    have hU : IsOpen {w : WO S T | f w ≠ 0} := isOpen_compl_singleton.preimage hf'.cont
    have hae' : ∀ᵐ w ∂(μ.restrict 𝓕), ‖f w‖ ^ 2 = 0 := hae
    have h0r : μ.restrict 𝓕 {w : WO S T | f w ≠ 0} = 0 :=
      measure_mono_null (fun a (ha : f a ≠ 0) (h : ‖f a‖ ^ 2 = 0) => ha (by simpa using h)) (ae_iff.1 hae')
    rw [Measure.restrict_apply hU.measurableSet] at h0r
    open Pointwise in
    have hμU : μ {w : WO S T | f w ≠ 0} = 0 := by
      refine hFD.measure_zero_of_invariant _ (fun γ => ?_) h0r
      ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have hp := norm_add_ratL_eq_of_isTh C hf ((-γ : ratL T S) : WO S T) (-γ).2 x
      change f (((-γ : ratL T S) : WO S T) + x) ≠ 0 ↔ f x ≠ 0
      rw [← norm_ne_zero_iff, hp, norm_ne_zero_iff]
    have hUe := (hU.measure_eq_zero_iff μ).1 hμU
    funext w
    by_contra hw
    have hw' : w ∈ {w : WO S T | f w ≠ 0} := hw
    rw [hUe] at hw'
    exact hw'
  have hI1 : IntegrableOn (fun w => f w * conj (f' w)) 𝓕 μ :=
    integrable_mul_conj (μ.restrict 𝓕) (hbm f hf) (hbm f' hf2)
  refine ⟨hI1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ipO
    rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show f' w * conj (f w) = conj (f w * conj (f' w))
    rw [map_mul, Complex.conj_conj, mul_comm]
  · intro a
    unfold ipO
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show (a • f) w * conj (f' w) = a * (f w * conj (f' w))
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · intro f'' hf3
    unfold ipO
    rw [← integral_add (integrable_mul_conj (μ.restrict 𝓕) (hbm f hf) (hbm f'' hf3))
      (integrable_mul_conj (μ.restrict 𝓕) (hbm f' hf2) (hbm f'' hf3))]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    show (f w + f' w) * conj (f'' w) = f w * conj (f'' w) + f' w * conj (f'' w)
    ring
  · intro u
    have hh : ∀ (g : WO S T → ℂ) x, C.rho u g x = C.ψ (symplOH S T x u) * g (x + u) := fun g x => rfl
    unfold ipO
    calc ∫ x in 𝓕, C.rho u f x * conj (C.rho u f' x) ∂μ
        = ∫ x in 𝓕, (fun y => f y * conj (f' y)) (x + u) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show C.rho u f x * conj (C.rho u f' x) = f (x + u) * conj (f' (x + u))
          rw [hh, hh, map_mul]
          have hz : C.ψ (symplOH S T x u) * conj (C.ψ (symplOH S T x u)) = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, C.std.1.2.1]
            norm_num
          linear_combination (f (x + u) * conj (f' (x + u))) * hz
      _ = ∫ x in 𝓕, f x * conj (f' x) ∂μ :=
          setIntegral_add_right (G := WO S T) (E := ℂ) (ratL T S) μ 𝓕 hFD (fun y => f y * conj (f' y))
            (mul_conj_add_ratL_eq_of_isTh C hf hf2) u
  · intro om hw p
    have hth : ∀ g, C.IsTh g → C.IsTh (om p g) := fun g hg => hw.om_pres p g hg
    have key : ∀ c : ℂ, ∫ x, ‖(om p f + c • om p f') x‖ ^ 2 ∂(μ.restrict 𝓕) =
        ∫ x, ‖(f + c • f') x‖ ^ 2 ∂(μ.restrict 𝓕) := by
      intro c
      have hg : C.IsTh (f + c • f') := GlobalTheory.WeilVacMove.isTheta_add hf (GlobalTheory.WeilVacMove.isTheta_smul c hf2)
      have e : om p f + c • om p f' = om p (f + c • f') := by rw [map_add, map_smul]
      rw [e, integral_normSq_eq _ (hbm _ (hth _ hg)).1, integral_normSq_eq _ (hbm _ hg).1,
        hw.om_unit μ 𝓕 hH hFD p _ hg]
    unfold ipO
    rw [integral_polar _ (hbm _ (hth f hf)) (hbm _ (hth f' hf2)), integral_polar _ (hbm f hf) (hbm f' hf2),
      key 1, key (-1), key I, key (-I)]

end GlobalTheory.Ker.ScalarProduct
