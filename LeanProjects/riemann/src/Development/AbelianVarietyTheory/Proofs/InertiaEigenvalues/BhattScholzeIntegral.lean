import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationIndepAinfModelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticePrismaticFCrystalPerfectPrismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FCrystalHomEqOfEtaleRealisationPerfectPrismStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral := by
  intro l _ K P₀ e H
  obtain ⟨a, ha⟩ := GlobalTheory.T.etaleRealisation_indep_ainfModel l K P₀ e H
  refine ⟨?_, ?_⟩
  · intro P AI hstd V _ _ _ _ _ _ _ ρ L hc hcr
    obtain ⟨M, j₀, hj₀⟩ := GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism l K P AI hstd V ρ L hc hcr
    obtain ⟨j, hj⟩ := ((ha M).2 ↥L.T (fun g => actT L g)).1 j₀ hj₀
    exact ⟨M, j, hj⟩
  · intro T T' _ _ _ _ ρ ρ' E E' j j' hj hj' f hf
    obtain ⟨j₀, hj₀, e₀⟩ := ((ha E).2 T ρ).2 j hj
    obtain ⟨j₀', hj₀', e₀'⟩ := ((ha E').2 T' ρ').2 j' hj'
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_FCrystalHom_of_equivariantEtaleMap_ainf l K T ρ T' ρ' E E' j₀ j₀' hj₀ hj₀' f hf
    refine ⟨u, fun x => ?_, fun u' hu' => ?_⟩
    · exact (e₀' _).symm.trans ((congrArg j₀' (u.u_tr a x).symm).trans
        ((hu _).trans (congrArg (f.lTensor (WCb l)) (e₀ x))))
    · refine GlobalTheory.T.fCrystalHom_eq_of_etale_realisation_perfectPrism l K T' ρ' E E' j₀' hj₀' u' u fun y => ?_
      obtain ⟨x, rfl⟩ := (ha E).1.2 y
      exact (congrArg j₀' (u'.u_tr a x)).trans ((e₀' _).trans ((hu' x).trans
        ((congrArg (f.lTensor (WCb l)) (e₀ x).symm).trans (hu _).symm)))

end GlobalTheory.BSP
