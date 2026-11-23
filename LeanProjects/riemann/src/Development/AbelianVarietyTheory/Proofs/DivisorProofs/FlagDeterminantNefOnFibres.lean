import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier

namespace GlobalTheory.FlagZ

theorem nefFib_flDet : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1)),
    GlobalTheory.ArInt.NefFib (flDet τ l : GlobalTheory.HermLB (flStr ι N)) := by
  intro ι _ N τ l
  exact GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated (isArithVar_hasHh_unique ι N).1 _
    (GlobalTheory.isGenerated_of_finite _ (iSup_nonzeroLocus_plSec Prod.fst Prod.snd (τ, l)))

end GlobalTheory.FlagZ
