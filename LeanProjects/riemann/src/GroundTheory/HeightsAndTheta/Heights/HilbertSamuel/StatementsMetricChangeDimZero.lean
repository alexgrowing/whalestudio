import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

def MetricChangeDimZero.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas 0 X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A), W₀.IsSemipositive → W₁.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∫ x, bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ - ε) * (n : ℝ) ^ 0 ≤
          Module.finrank ℂ (V n)) →
      ∀ (e : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n)) (ε : ℝ), 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          |chiGram W₁ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
              chiGram W₀ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
            (n : ℝ) ^ (0 + 1) / 2 * ∫ t in (0 : ℝ)..1,
              ∫ x, Weight.diff W₁ W₀ x * bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ| ≤
            ε * (n : ℝ) ^ (0 + 1)

namespace MetricChangeDimZero

def pointAtlas : FinHolAtlas 0 Unit where
  n := 1
  chart _ := (Homeomorph.homeomorphOfUnique Unit (Fin 0 → ℂ)).toOpenPartialHomeomorph
  cover _ := ⟨0, by simp⟩
  holo _ _ := fun _ _ => (analyticAt_const (v := (0 : Fin 0 → ℂ))).congr
    (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _)

def pointBundle : HolLineBundle pointAtlas where
  g _ _ _ := 1
  holo _ _ _ := fun _ _ => analyticAt_const
  ne_zero _ _ _ _ := one_ne_zero
  cocycle _ _ _ _ _ := (mul_one 1).symm

def pointWeight (c : ℝ) : Weight pointBundle where
  φ _ _ := c
  smooth _ _ := contDiffOn_const
  compat _ _ _ _ := by simp [pointBundle]

def pointVolume : SmoothVolume pointAtlas where
  μ := Measure.dirac ()
  isProb := inferInstance
  dens _ _ := 1
  smooth _ := contDiffOn_const
  pos _ _ _ := one_pos
  chart_lintegral j g hg := by
    have hs : (pointAtlas.chart j).source = univ := rfl
    have ht : (pointAtlas.chart j).target = univ := rfl
    rw [hs, ht, Measure.restrict_univ, Measure.restrict_univ, lintegral_dirac, volume_pi,
      Measure.pi_of_empty (x := (0 : Fin 0 → ℂ)), lintegral_dirac]
    simp

end MetricChangeDimZero

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
