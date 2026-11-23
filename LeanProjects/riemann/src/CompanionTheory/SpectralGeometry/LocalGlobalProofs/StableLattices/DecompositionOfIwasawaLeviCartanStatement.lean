import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfIwasawaLeviCartan
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_of_iwasawa_levi_cartan : AdaptExists → IwaQ → LeviQ → CartanQ → Decomp := by
  first | exact @GlobalTheory.CompanionTheory.BmuDecomp.decomp | exact GlobalTheory.CompanionTheory.BmuDecomp.decomp | (intros; apply GlobalTheory.CompanionTheory.BmuDecomp.decomp <;> assumption)
