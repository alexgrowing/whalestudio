import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleChernClassEqKummerClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.Inputs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForE

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.E

theorem etMap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : EtMap l K :=
  Main.etale_comparison_map etIn l (CrystallineSemistableComparison.R.forE l) K

theorem firstChern_unique (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O))
    (κ : O →+* OC l) (D : LineData X) (h : Etale D.f) (y y' : ∀ n, MH (PX q κ) n 2) :
    IsFirstChernClassOfLineBundle q κ D y → IsFirstChernClassOfLineBundle q κ D y' → y = y' := Main.firstChern_unique l (CrystallineSemistableComparison.R.forE l) O X q κ D h y y'

end CrystallineSemistableComparison.E
