import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationPrimeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelTorsorOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNormStatement

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginCut

theorem keyOrigin : GlobalTheory.LocAcyc.KeyOrigin := by
  have h₁ := GlobalTheory.T.strict_henselisation_prime_eq
  have h₂ := GlobalTheory.T.exists_noetherian_model_torsor_origin
  have h₃ := GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal
  unfold GlobalTheory.LocAcyc.KeyOrigin GlobalTheory.LocAcyc.KeyLocalWith GlobalTheory.LocAcyc.TorsorsTrivial
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hS q hq hqu D _ _ hfin hproj hff act hbij
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, ψ, hψ, D₁, _, _, act₁, htors₁, hpull₁⟩ :=
    h₁ T O hT P φ hφ hsh hS q hq hqu D act ⟨hfin, hproj, hff, hbij⟩
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, hqA, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, ψA, hψA,
    DA, _, _, actA, htorsA, hpullA⟩ := h₂ T O hT q hq hqu E Q hQ j hj ψ hψ D₁ act₁ htors₁
  obtain ⟨σ, hσ⟩ :=
    h₃ T O hT P φ hφ hsh hS q hq hqu A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htorsA
  obtain ⟨σ₁, hσ₁⟩ := hpullA σ hσ
  exact hpull₁ σ₁ hσ₁

end GlobalTheory.KeyOriginCut
