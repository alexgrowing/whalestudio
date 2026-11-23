import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductOverPlacesCompactOpenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QFinMain

theorem qFin_of_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QFin v w := by
  intro D c v t w hc ht hv hW hP j σ h
  obtain ⟨F, hF⟩ := hP
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.twistChainLevelProductOverPlaces_compact_open D c v t w F hF j σ h
  obtain ⟨T₁, hT, hS⟩ := GlobalTheory.T.firstVariable_support_finite_cells_at_twist_places D c v t w F hc ht hv hW hF j σ h
  exact ⟨GlobalTheory.QuotientFiniteLevel.qK F j σ h, T₁, h1, h2, h3, hT, GlobalTheory.T.twistChainLevelProduct_inverse_scalar_laws D c v t w F hc ht hv hW hF j σ h, hS⟩

end GlobalTheory.QFinMain
