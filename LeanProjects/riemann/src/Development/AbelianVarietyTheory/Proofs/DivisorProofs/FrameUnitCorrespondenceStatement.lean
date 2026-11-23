import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameUnitCorrespondence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_unit_correspondence : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → ModelOf V hr X → NegFirst V X.p0 x → (∀ u y, FrIs θ V hr X x u y → IsUnitFr X y) ∧ (∀ y, IsUnitFr X y → ∃ u ∈ GinfC V, FrIs θ V hr X x u y) ∧ (∀ u, ∃ y, FrIs θ V hr X x u y) ∧ (∀ u y y', FrIs θ V hr X x u y → FrIs θ V hr X x u y' → y = y') ∧ ∀ u ∈ GinfC V, ∀ u' ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → FrIs θ V hr X x u' y → u = u' := by
  first | exact @GlobalTheory.UnitFrameReal.unit_frames | exact GlobalTheory.UnitFrameReal.unit_frames | (intros; apply GlobalTheory.UnitFrameReal.unit_frames <;> assumption)
