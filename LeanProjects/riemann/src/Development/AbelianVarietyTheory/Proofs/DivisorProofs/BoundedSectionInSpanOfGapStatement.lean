import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSectionInSpanOfGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_section_in_span_of_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → (∀ (τ : X.Ψ) (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) → P ∈ X.SS la := by
  first | exact @GlobalTheory.SepCusp.mem_SS_of_sep | exact GlobalTheory.SepCusp.mem_SS_of_sep | (intros; apply GlobalTheory.SepCusp.mem_SS_of_sep <;> assumption)
