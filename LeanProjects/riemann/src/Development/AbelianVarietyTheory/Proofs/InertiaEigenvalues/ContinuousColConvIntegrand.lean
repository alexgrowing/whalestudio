import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.MspanOrth

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {ω : HChar E}

omit [IsTotallyComplex E] in
instance isAddHaarMeasure_volume_col : Measure.IsAddHaarMeasure (volume : Measure (Fin a → Cinf E)) :=
  Measure.pi.isAddHaarMeasure _

section Lemmas

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

end Lemmas

end GlobalTheory.MspanOrth
