import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExc
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphFibre

variable {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]

open Classical in

def vertWeight {n : ℕ} (L : Fin n → HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then 0 else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem vertR_eq_finsum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    vertR P L s = ∑ᶠ W, (divCycle P s W : ℝ) * vertWeight L W := by
  classical
  rw [vertR, finsum_mem_def]
  refine finsum_congr fun W => ?_
  simp only [Set.indicator, divCycle, Finsupp.ofSupportFinite_coe, vertWeight]
  by_cases hW : W ∈ divSupp P s
  · rw [if_pos hW, if_pos hW]
  · rw [if_neg hW, if_neg hW, Nat.cast_zero, zero_mul]

theorem finite_support (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    (Function.support fun W => (divCycle P s W : ℝ) * vertWeight L W).Finite :=
  (divCycle P s).support.finite_toSet.subset fun W hW =>
    Finsupp.mem_support_iff.mpr fun h0 => hW (by simp [h0])

theorem vertR_sub (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s₁ s₂ : MRing ι)
    (E : Ideal (MRing ι)) (hhor : ¬ IsHorizontal E)
    (hE : (divCycle P s₂ E : ℤ) = divCycle P s₁ E + 1)
    (hW : ∀ W, ¬ IsHorizontal W → W ≠ E → divCycle P s₂ W = divCycle P s₁ W) :
    vertR P L s₁ - vertR P L s₂ = -((geoNum n E (fun j => (L j).a) : ℝ) * Real.log (charOf E)) := by
  classical
  rw [vertR_eq_finsum, vertR_eq_finsum, ← finsum_sub_distrib (finite_support P L s₁) (finite_support P L s₂)]
  have hpt : ∀ W, (divCycle P s₁ W : ℝ) * vertWeight L W - (divCycle P s₂ W : ℝ) * vertWeight L W =
      if W = E then -vertWeight L E else 0 := by
    intro W
    by_cases hWh : IsHorizontal W
    · have hne : W ≠ E := fun h => hhor (h ▸ hWh)
      simp [vertWeight, hWh, hne]
    · by_cases hWE : W = E
      · subst hWE
        have hR : (divCycle P s₂ W : ℝ) = divCycle P s₁ W + 1 := by exact_mod_cast hE
        rw [if_pos rfl, hR]
        ring
      · rw [if_neg hWE, hW W hWh hWE, sub_self]
  rw [finsum_congr hpt, finsum_eq_single _ E (fun W hW => if_neg hW), if_pos rfl]
  simp [vertWeight, hhor]

end StackedGraphFibre

open StackedGraphFibre in

theorem DualStackedGraphFibre.proof (hCyc : DualStackedExcCycle.Statement)
    (hSec : DualStackedExcGeoSecond.Statement) (hFir : DualStackedExcGeoFirst.Statement) :
    DualStackedGraphFibre.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab t L hL
  obtain ⟨E, hE, hhor, hEt⟩ := hCyc K i F F' T b b' a hi hlt hcov hab
  have key := vertR_sub (stackedGraph b' a) L (graphSecond t) (C (a t) * graphFirst t) E hhor (hEt t).1
    (hEt t).2
  have ha : ∀ s, a s ≠ 0 := fun s hs =>
    b.ne_zero s (Subtype.ext (by rw [hab s, hs, zero_smul]; rfl))
  refine ⟨fun hall => ?_, fun ⟨j, hj⟩ => ?_⟩
  · have hd : (fun j => (L j).a) = fun _ => degSecond := funext hall
    rw [key, hd, hSec K i F F' T b b' a hi hlt hcov hab E hE, ← DualLatticeIndex.proof K i F F' hlt.le,
      DualStackedDegreeAlt.relIndex_stacked hlt.le b b' a hab,
      Real.log_prod (fun s _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha s)))]
  · rw [key, hFir K i F F' T b b' a hi hlt hcov hab E hE (fun j => (L j).a) hL ⟨j, hj⟩]
    simp

end

end GroundTheory.Heights₂.Heights
