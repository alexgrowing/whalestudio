import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

theorem NRCM_of (hS : SqrtKur) (hD : DenseOK) (h2 : HomotheticLatticeIntegralS2) (hN : NRDense) (h4 : Formalism.L2.Th1.CM.CM4) :
    NRCM := by
  intro dK L hsq hd4 hCM l _ hl5 hld hinert ι g2 g3 ε hgood hε hθ
  obtain ⟨c, hc, hg2, hg3, hs2K, hs2n⟩ :=
    h2 h4 dK L hsq hd4 hCM l hl5 hld hinert ι g2 g3 hgood
  refine ⟨⟨_, hs2K⟩, hs2n, ⟨c, hc, hg2, hg3, rfl⟩, ?_⟩
  intro σ hσ α hα hσα
  have hw := (hS dK hsq hd4 l hl5 hinert ι).1
  have hmem : ∀ m n : ℤ, ι ((m : ℂ) + (n : ℂ) * omegaK dK) ∈ MaximalUnramifiedExtension l := by
    intro m n
    rw [map_add, map_mul, map_intCast, map_intCast]
    exact add_mem (intCast_mem _ m) (mul_mem (intCast_mem _ n) hw)
  let S : Set (MaximalUnramifiedExtension l) := {a | ∃ m n : ℤ, ¬ (l : ℤ) ∣ normInt dK m n ∧
    (a : ℂ_[l]) = ι ((m : ℂ) + (n : ℂ) * omegaK dK)}
  refine normUnits (MaximalUnramifiedExtension l) l σ hσ (phFF l g2 g3 ⟨_, hs2K⟩ ε) (FAux.cc_phFF (by omega) _ _ _ _) S ?_ α ?_
  · rintro a ⟨m, n, hmn, ha⟩
    exact hN h4 dK L hsq hd4 hCM l hl5 hld hinert ι g2 g3 ε ⟨_, hs2K⟩ hgood hε hθ c hc hg2 hg3 rfl
      σ hσ m n hmn a ha
  · intro e he
    obtain ⟨m, n, hmn, hclose⟩ := hD dK hsq hd4 l hl5 hinert ι σ hσ α hα hσα e he
    exact ⟨⟨_, hmem m n⟩, ⟨m, n, hmn, rfl⟩, by simpa using hclose⟩

end Formalism.L2.Th1.D
