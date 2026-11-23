import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeight
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∃ B : Finset RM.Ω, ∀ A : Subring RM.Ω, (↑B : Set RM.Ω) ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A) → FinRd.GoodRing Fr A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset <;> assumption)
