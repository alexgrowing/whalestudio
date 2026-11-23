import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRangeMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResEqOneIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiGamPowNeOne

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
namespace GlobalTheory.HWL.Assembly

theorem exists_wach (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (hF : FaithH AI) (hW : WachEx AI) :
    ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  obtain ⟨ht, hπ, -⟩ := GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI hT
  refine exists_of_layers P AI (fun K s LL g => ?_) ht hπ
  obtain ⟨Γ⟩ := GlobalTheory.HWL.GroupLayer.nonempty_gamS l P K s LL g
  obtain ⟨R⟩ := GlobalTheory.HWL.Ser.nonempty_wSer l P K s LL g Γ
  obtain ⟨I, hI⟩ := GlobalTheory.HWL.IoLayer.main l P AI K s LL g Γ R
  obtain ⟨E⟩ := GlobalTheory.HWL.EtMod.nonempty_wEt l P AI K s LL g Γ R I hI (GlobalTheory.EtaleBasis.exists_etBasis l P AI hF K s LL g Γ R I hI)
  obtain ⟨Mo⟩ := hW K s LL g Γ R I hI E
  obtain ⟨Cl⟩ := GlobalTheory.HerrClassMaps.exists_classMaps l P AI K s LL g Γ R I hI E
  obtain ⟨Cm⟩ := GlobalTheory.HWL.Cmp.nonempty_cmpS l P AI hT K s LL g Γ R I hI E Mo
  exact ⟨⟨Γ, R, I, hI, E, Mo, Cl, Cm⟩⟩

end GlobalTheory.HWL.Assembly
