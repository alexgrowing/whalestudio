import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg

open Formalism.BasicNotions Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem vacuum_oriented_exists : ∀ D : D7, VacExistsO D := GlobalTheory.VacuumO.vacExists

end GlobalTheory.Member
