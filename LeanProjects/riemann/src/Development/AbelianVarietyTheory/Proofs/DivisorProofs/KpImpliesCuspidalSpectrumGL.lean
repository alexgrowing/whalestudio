import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL

namespace GlobalTheory.ThK

theorem cuspidalSpectrumGL_of_KP : GlobalTheory.ThK.KP → GlobalTheory.Published.CuspidalSpectrumGL :=
  fun h => h.cuspidalSpectrumGL

end GlobalTheory.ThK
