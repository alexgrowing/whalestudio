import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsScaledIsometry
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

theorem GlobalTheory.SelfDualIsom.landherrSelfDual : Formalism.L2.Pj.LandherrSelfDual := by
  unfold Formalism.L2.Pj.LandherrSelfDual
  exact GlobalTheory.SelfDualIsom.exists_scaled_isometry GlobalTheory.QNorm.hasseNormSt
