import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  first | exact @GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | exact GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | (intros; apply GlobalTheory.LocalUnitaryGlue.exists_finite_adelic <;> assumption)
