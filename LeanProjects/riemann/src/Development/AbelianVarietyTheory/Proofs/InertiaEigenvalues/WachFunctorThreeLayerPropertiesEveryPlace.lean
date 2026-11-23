import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleMapFrobeniusGaloisEquivariantStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.AllLaws

theorem laws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  intro D HW F l _ K s LL h W E
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact ⟨GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity D HW l K s LL h, GlobalTheory.T.wach_etale_map_frobenius_galois_equivariant D HW F l K s LL h,
    GlobalTheory.TrivCrys.isCrys_lat_of_trivial W.one W.one_triv⟩

end GlobalTheory.NL.AllLaws
