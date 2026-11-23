import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassFiniteness
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRueckertNullstellensatz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteFibreGermIntegral.proof (hWF : WeierstrassFiniteness.Statement)
    (hR : RueckertNullstellensatz.Statement) : FiniteFibreGermIntegral.Statement := by
  intro σ _ X x d A hX hiso g hg
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hfx : ∀ i, AnalyticAt ℂ (f i) x := fun i => hf i x hxN
  have hAj : ∀ j : Fin d, AnalyticAt ℂ (fun z => A z j - A x j) x := fun j =>
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt x).sub
      analyticAt_const

  let F : Fin (k + d) → (σ → ℂ) → ℂ := Fin.append f (fun j z => A z j - A x j)
  have hFx : ∀ i, AnalyticAt ℂ (F i) x := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left] using hfx i
    · simpa only [F, Fin.append_right] using hAj j
  have hcoord : ∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j) := by
    intro l
    have hl : AnalyticAt ℂ (fun z : σ → ℂ => z l - x l) x :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) l).analyticAt x).sub analyticAt_const
    have hvan : ∀ᶠ z in 𝓝 x, (∀ i, F i z = 0) → z l - x l = 0 := by
      filter_upwards [hNo.mem_nhds hxN, hW] with z hzN hzW h0
      have hf0 : ∀ i, f i z = 0 := fun i => by simpa only [F, Fin.append_left] using h0 (Fin.castAdd d i)
      have hA0 : A z = A x := funext fun j =>
        sub_eq_zero.1 (by simpa only [F, Fin.append_right] using h0 (Fin.natAdd k j))
      have hzX : z ∈ X := by
        have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hzN, hf0⟩
        exact this.1
      rw [hWiso z ⟨hzX, hzW⟩ hA0, sub_self]
    obtain ⟨m, h, -, hh, hsum⟩ := hR σ x (k + d) F (fun z => z l - x l) hFx hl hvan
    refine ⟨m, fun i => h (Fin.castAdd d i), fun j => h (Fin.natAdd k j), fun i => hh _, fun j => hh _, ?_⟩
    filter_upwards [hsum] with z hz
    rw [hz, Fin.sum_univ_add]
    simp only [F, Fin.append_left, Fin.append_right]
  obtain ⟨n, a, h, ha, -, hrel⟩ := hWF σ x k f d A hfx hcoord g hg
  refine ⟨n, a, ha, ?_⟩
  filter_upwards [hrel, hNo.mem_nhds hxN] with z hz hzN hzX
  have hz0 : z ∈ X ∩ N := ⟨hzX, hzN⟩
  rw [hXN] at hz0
  rw [hz]
  simp [hz0.2]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
