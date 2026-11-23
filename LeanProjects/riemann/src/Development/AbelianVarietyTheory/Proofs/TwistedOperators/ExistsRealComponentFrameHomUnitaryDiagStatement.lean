import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealComponentFrameHomUnitaryDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realComponent_frame_hom_unitaryDiag : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ), ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ := by
  first | exact @GlobalTheory.FibreAtTau.cmp_frame_hom | exact GlobalTheory.FibreAtTau.cmp_frame_hom | (intros; apply GlobalTheory.FibreAtTau.cmp_frame_hom <;> assumption)
