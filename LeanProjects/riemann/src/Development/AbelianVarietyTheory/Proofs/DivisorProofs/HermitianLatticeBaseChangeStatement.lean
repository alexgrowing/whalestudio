import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_base_change : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ) (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)), L.FG → (∃ h' : HermFam K' (Fin m → K'), IsBC h h') ∧ (Full L → Full (latBC K' L)) ∧ ∀ h' : HermFam K' (Fin m → K'), IsBC h h' → deg h' (latBC K' L) = deg h L ∧ latRank K' (latBC K' L) = latRank K L ∧ ∀ x : Fin m → K, latBC K' (lineLat L x) = lineLat (latBC K' L) (fun i => algebraMap K K' (x i)) := by
  first | exact @GlobalTheory.LatExt.ext_deg_rank_line | exact GlobalTheory.LatExt.ext_deg_rank_line | (intros; apply GlobalTheory.LatExt.ext_deg_rank_line <;> assumption)
