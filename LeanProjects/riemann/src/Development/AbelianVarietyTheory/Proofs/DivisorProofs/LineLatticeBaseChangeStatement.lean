import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineLatticeBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_lattice_base_change : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), L.FG → ∀ x : Fin m → K, latBC K' (lineLat L x) = lineLat (latBC K' L) (fun i => algebraMap K K' (x i)) := by
  first | exact @GlobalTheory.LineBC.latBC_lineLat | exact GlobalTheory.LineBC.latBC_lineLat | (intros; apply GlobalTheory.LineBC.latBC_lineLat <;> assumption)
