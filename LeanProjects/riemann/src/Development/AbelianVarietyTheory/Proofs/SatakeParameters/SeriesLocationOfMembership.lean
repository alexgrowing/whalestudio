import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CentralOfTameCoupledStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalLanglandsPlaceDatumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.SerFinished

set_option maxHeartbeats 2000000 in

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  intro hP hL
  refine GlobalTheory.HeightCounting.Up.Model.AtMem.imp (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.exists_local_langlands_place_datum hP hL)
    (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.coefficient_duty_in_place hL) (GlobalTheory.T.central_local_stable_integral hL))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hO, hC, -, -⟩
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    (GlobalTheory.CoefDuty.OPinModel.labFixed_iff c.a).2 hO.lab
  have htame : ∀ D', D' = withLoc c.a.nt.L → ∀ k (v : D'.nd.PlG k),
      ∃ κ : IsLocalRing.ResidueField (D'.nd.plOm.1 (D'.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D'.host.g k),
        TameCoupled (D'.nd.plOm.1 (D'.naut.plGw k v)) κ (D'.ntypes.tg k v)
          (@GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩).gen := by
    rintro _ rfl k v
    exact ⟨c.a.nt.A.grp.kv k v, GlobalTheory.CoefDuty.OPinModel.tame_of_pin hO k v⟩
  refine GlobalTheory.T.serLoc_of_tameCoupled_of_cenLoc' hP.what₂ hP.green hP.zel hP.dz hL (w.D Z) P _ hlab (htame _ c.a.nt.eq) ?_
  rw [hPin.M_eq]
  exact hC

end GlobalTheory.SerFinished
