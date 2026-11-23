import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagSpacesNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply

noncomputable section

namespace GlobalTheory.StdFrameObj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.FWT GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_piT_mul {P : PreCh} (L : LevCh P) :
    (star (L.piT P.u₀ : L.host.E) : L.host.E) * (L.piT P.u₀ : L.host.E) = (L.T P.u₀ : L.host.E) := by
  have h : (star (L.piT P.u₀ : L.host.E) : L.host.E) = L.host.conj (L.piT P.u₀ : L.host.E) :=
    bridge_star_holds P.R L.host _
  rw [h, mul_comm]
  exact L.piT_norm _

def coordPre (P : PreCh) (L : LevCh P) : Pre :=
  Pre.ofCh P L (DiagSp.spacesNorm P.R (host_cmData P.R L.host) (L.T P.u₀) (L.T_prime _) _ (star_piT_mul L)) rfl
    (fun j _ τ => DiagSp.spacesNorm_Y_sig _ _ _ _ _ _ j τ)
    (fun j _ hj => DiagSp.spacesNorm_hasFrame _ _ _ _ _ _ j hj) (fun _ _ _ => rfl)
    (DiagSp.spacesNorm_z_norm _ _ _ _ _ _)

theorem diagSpaces_coordPre (P : PreCh) (L : LevCh P) : DiagSpaces (coordPre P L).sp :=
  DiagSp.spacesNorm_coord _ _ _ _ _ _

def coordV (D : D7) : D7 :=
  { D with
    sp := { D.sp with
      V := fun _ => Examples₂.posSpace Examples₂.star_isIntegral D.R.nV
      V_sig := fun _ => Examples₂.posSpace_sigOK _ _
      V_rank := fun _ _ _ => rfl
      Vneg := fun _ => false
      V_std := fun _ _ _ => DiagSp.ortho_sign D.R.nV false } }

end GlobalTheory.StdFrameObj

end
