import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Monomial
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.SignedPerm

section General

variable {K : Type} [Field K] [NumberField K]

end General

section Host

theorem finite_and_ncard_le : ∀ (D : D7) (n : ℕ),
    {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧
    {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard
      ≤ NumberField.Units.torsionOrder D.host.E ^ n * n.factorial := by
  intro D n
  have hcm := D.host.isCMField_hostE
  exact UpperTheory.Mu.unitary_integral_finite_and_ncard_le
    (fun φ x => IsCMField.complexEmbedding_complexConj D.host.E φ x) n

end Host

end GlobalTheory.LowRow.SignedPerm
