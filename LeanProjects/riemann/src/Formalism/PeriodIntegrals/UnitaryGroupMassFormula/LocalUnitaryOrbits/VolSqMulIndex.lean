import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHI

noncomputable section

namespace PI.OmLocU.Sd

open MeasureTheory PI.VolStabSW.SdUniqW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

theorem vol_mul_vol_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L') :
    μ.real (L : Set V) * μ.real (L' : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hL'o.measurableSet]
    exact integrableOn_const hL'c.measure_lt_top.ne
  have h1 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) =
      (L' : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) := by
    funext y
    rw [hT y, h0, mul_one]
  rw [e1, integral_indicator_const _ hL'o.measurableSet, neg_zero, hΦ,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h1
  have h2 : μ.real (L' : Set V) * c = 1 := by
    rw [Complex.real_smul] at h1
    exact_mod_cast h1
  rw [mul_comm]
  exact h2

theorem vol_sq_mul_index {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L')
    (hle : L ≤ L') (hN : L.relIndex L' ≠ 0) :
    μ.real (L : Set V) ^ 2 * (L.relIndex L' : ℝ) = 1 := by
  have := hμ.1
  have h1 := vol_mul_vol_ann hμ hχ h0 L L' hLc hLo hL'c hL'o hA
  have h2 := PI.VolStabSW.measure_eq_relIndex_mul μ L L' hle hL'o.measurableSet
    hLo.measurableSet hN
  have h3 : μ.real (L' : Set V) = (L.relIndex L' : ℝ) * μ.real (L : Set V) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
    simp
  rw [h3] at h1
  linarith [h1]

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ann_eq_cond {V : Type} (ψ0 : Fv F v → ℂ) (d : Fv F v) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      d * t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) :
    ann (fun x y => ψ0 (B x y)) L = {y | ∀ x ∈ L, d * B x y ∈ v.adicCompletionIntegers F} := by
  ext y
  constructor
  · intro hy x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

end Ann

end PI.OmLocU.Sd
