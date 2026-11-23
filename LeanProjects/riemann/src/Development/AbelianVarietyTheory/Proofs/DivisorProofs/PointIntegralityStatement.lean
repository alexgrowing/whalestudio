import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorPointSemiFibrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDegreeHeightBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationLatticeDegreeHeightBoundedStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

theorem GlobalTheory.HeightParts.ptInt : Hypotheses2 → HypothesesH → PtInt := by
  intro hP hH D O hc hN A T H hr
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.lie_lattice_degree_height_bounded hP hH D O hc hN A T H hr
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.T.filtration_lattice_degree_height_bounded hP hH D O hc hN A T H hr
  refine ⟨max C₂ C₃, fun y hy => ?_⟩
  obtain ⟨K, _, _, F, ι, hg, ht⟩ := GlobalTheory.T.interior_point_semi_fibration hP hH D O hc hN A T H hr y hy
  obtain ⟨h, hh⟩ := (GlobalTheory.T.semi_fibration_lie_lattice_full K F).2.1
  refine ⟨K, inferInstance, inferInstance, F, h, hg, hh, (hC₂ y hy K F ι h ht hh).trans (le_max_left _ _), fun τ k hk => ?_⟩
  obtain ⟨e₁, e₂⟩ := hC₃ y hy K F ι h ht hh τ k hk
  exact ⟨stepLat O F τ k, inf_le_left, e₁, e₂.trans (le_max_right _ _)⟩
