import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

open Filter Topology
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem convComp_proved : ConvComp := by
  intro E _ _ _ N t s φ h hφ
  induction h with
  | leaf V z z₀ h => exact Conv.leaf V (fun k => z (φ k)) z₀ (h.comp hφ.tendsto_atTop)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
