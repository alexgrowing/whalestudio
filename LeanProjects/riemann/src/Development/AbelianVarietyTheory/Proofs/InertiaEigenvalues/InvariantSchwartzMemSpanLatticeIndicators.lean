import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanIndicatorLowerSetsFinitePoset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGLOfSpanRangeEqLocalRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsSide
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

variable {O : Type} [CommRing O]

noncomputable def red (I : Ideal O) (r : ℕ) : (Fin r → O) →ₗ[O] (Fin r → O ⧸ I) :=
  ((Ideal.Quotient.mkₐ O I).toLinearMap).compLeft (Fin r)

noncomputable def rowSpan {n r : ℕ} (I : Ideal O) (z : Matrix (Fin n) (Fin r) O) :
    Submodule O (Fin r → O ⧸ I) :=
  Submodule.span O (Set.range fun i => red I r (z i))

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix
variable {O : Type} [CommRing O]

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix

end GlobalTheory.GenUnr

namespace GlobalTheory.GenUnr
open Matrix

end GlobalTheory.GenUnr
