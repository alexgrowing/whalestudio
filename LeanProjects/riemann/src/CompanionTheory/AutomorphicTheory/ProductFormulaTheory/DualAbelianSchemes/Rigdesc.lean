import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RigDescent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AppTopCompApply

set_option autoImplicit false

open CompanionTheory.ObstructionTrivialLocus

namespace CompanionTheory.PfDual

theorem rigdesc_pf : H90 → RigDescent := GlobalTheory.CompanionTheory.RigDesc.rigDescent

theorem rigDescent_holds : RigDescent := rigdesc_pf GlobalTheory.CompanionTheory.FlatHilbert90.h90

end CompanionTheory.PfDual
