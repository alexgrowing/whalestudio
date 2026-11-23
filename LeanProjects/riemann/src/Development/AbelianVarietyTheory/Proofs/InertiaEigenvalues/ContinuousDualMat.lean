import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsUEqCycLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateDualLocalGaloisRepAtPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTmulOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) (Br.LL D.nbr i w hw) :=
  GlobalTheory.TateDualX.dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)) (Br.loc D.nbr i w hw M)

theorem dualMat_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    dualMat i w hw M g = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) • (Br.loc D.nbr i w hw M g⁻¹).transpose := rfl

theorem continuous_dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (dualMat i w hw M) := by
  haveI := isTopRing i w hw
  exact GlobalTheory.TateDualX.continuous_dualTw _ _ (GlobalTheory.TateDualX.continuous_cyc D i w hw)
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM)

def Udual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (dualMat i w hw M) (continuous_dualMat i w hw M hM)

theorem cyc_mem (g : Br.G D.nbr i w hw) : ∃ c : Br.OLL D.nbr i w hw,
    algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  exact ⟨_, rfl⟩

theorem dualMat_integral {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    ∃ N : Matrix (Fin k) (Fin k) (Br.OLL D.nbr i w hw),
      dualMat i w hw M g = N.map (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  obtain ⟨c, hc⟩ := cyc_mem i w hw g
  refine ⟨c • (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)) g⁻¹).transpose, ?_⟩
  rw [dualMat_apply, ← hc, Matrix.map_smul' _ _ _ (map_mul _), Matrix.transpose_map]
  rfl

def latDual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    Lattice (O := Br.OLL D.nbr i w hw) (Udual i w hw M hM).ρ :=
  GlobalTheory.BKLatticeCochain.stdLattice Subtype.val_injective (Udual i w hw M hM).ρ fun g => by
    obtain ⟨N, hN⟩ := dualMat_integral i w hw M g
    exact ⟨N, fun x => by rw [← hN]; rfl⟩

end GlobalTheory.Pass.LocDirect

end
