import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicIntegerPointOfFiniteExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Formalism.LocalToGlobal.ProjectiveLattices.LocFld
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidueStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (φ : c.F →+* ℂ_[p]), IntAll Xo c → ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →+* ℂ_[p]), (∀ a, σ (algebraMap c.F L a) = φ a) → ∀ (y : FrPt Xo c L) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ (z : PtC Xo c φ) (u : ℂ_[p]), u ≠ 0 ∧ ∀ f ∈ sec Xo c a n, valC z.1 f = u * σ (evR Xo c f y) := by
  first | exact @GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt | exact GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt | (intros; apply GlobalTheory.GeoTie.NumPt.exists_ptC_of_finExt <;> assumption)
