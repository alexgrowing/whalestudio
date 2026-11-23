import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFamilyBaseChangeExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_family_base_change_exists : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (m : ℕ) (h : HermFam K (Fin m → K)), ∃ h' : HermFam K' (Fin m → K'), IsBC h h' := by
  first | exact @GlobalTheory.HermExt.exists_isBC | exact GlobalTheory.HermExt.exists_isBC | (intros; apply GlobalTheory.HermExt.exists_isBC <;> assumption)
