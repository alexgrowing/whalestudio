import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturatedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickeningStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.GE

theorem geClosedProj : GEClosedProj := by
  intro R _ _ I hI N P Cs i β hi hβ
  obtain ⟨hbase, hsat, hanti, hcompat⟩ := GlobalTheory.T.thickening_vanishing_ideal_system R I N Cs i β hi hβ
  obtain ⟨n₀, hlift⟩ := GlobalTheory.T.homogeneous_ideal_filtration_saturated R I N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hsat hcompat
  obtain ⟨J, hJ, h⟩ := GlobalTheory.T.homogeneous_lift_adic_filtration R I hI N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hanti n₀ hlift
  exact GlobalTheory.T.homogeneous_ideal_le_thickening R I N Cs i β hi hβ J hJ (fun e => (h e).1) (fun e => (h e).2)

end GlobalTheory.CompanionTheory.GE
