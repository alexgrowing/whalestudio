import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagSpacesNorm

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem exists_diagSpaces_ofCh : ∀ (P : PreCh) (L : LevCh P), ∃ (sp : @Spaces P.R L.host.F L.host.E _ _ _ _ L.host.cmStar _) (hT : letI := L.host.cmStar; sp.T = L.T P.u₀) (hY : letI := L.host.cmStar; ∀ j, j ≤ P.R.m → ∀ τ : L.host.E →+* ℂ, (sp.Y j).sig τ = sigYD P.R j) (hA : letI := L.host.cmStar; ∀ j, 0 < j → j < P.R.m → HasHyperbolicAuxiliaryFrame sp j) (hV : letI := L.host.cmStar; ∀ j, 1 ≤ j → j ≤ P.R.m → sp.Vneg j = false) (hz : letI := L.host.cmStar; (sp.X P.R.m).hT sp.z sp.z = (sp.T : L.host.E)), (letI := L.host.cmStar; DiagSpaces sp ∧ ∀ j, sp.Vneg j = false) ∧ (Pre.ofCh P L sp hT hY hA hV hz).R = P.R := by
  intro P L
  letI := L.host.cmStar
  have hs : ∀ x : L.host.E, star x = L.host.conj x := bridge_star_holds P.R L.host
  have hpz : star (L.piT P.u₀ : L.host.E) * (L.piT P.u₀ : L.host.E) = (L.T P.u₀ : L.host.E) := by
    rw [hs, mul_comm]
    exact L.piT_norm P.u₀
  obtain ⟨S, hT, hD, hV, hA, hz, hY⟩ := GlobalTheory.Mem.exists_diagSpaces_norm P.R L.host.F L.host.E (host_cmData P.R L.host)
    (L.T P.u₀) (L.T_prime P.u₀) (L.piT P.u₀ : L.host.E) hpz
  exact ⟨S, hT, hY, hA, fun j _ _ => hV j, hz, ⟨hD, hV⟩, rfl⟩

end GlobalTheory.Mem
