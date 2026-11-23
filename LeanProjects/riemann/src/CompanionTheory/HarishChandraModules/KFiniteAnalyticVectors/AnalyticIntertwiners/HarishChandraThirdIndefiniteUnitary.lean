import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.BoundedOperators
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KFinDensePf
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.PCDense

namespace CompanionTheory.D.gk.HC

theorem clause1_of (hS : KFSm) (hW : IntWts) (hI : UIrr) (hA : UAdm) : Clause1 :=
  harish_chandra_first_clause (fun _ _ _ _ _ _ _ hσ _ => kfinDense_UJC hσ) hS hW hI hA harish_chandra_descent

theorem harishChandraThird_indefiniteUnitary : Clause3 :=
  harish_chandra_third_clause fun _ _ _ πU => kfinDense_coverC (fun _ _ _ _ _ _ _ hσ => kfinDense_UJC hσ) πU

end CompanionTheory.D.gk.HC
