import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFunctionFieldEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_function_field_embedding : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (K : Type) [Field K] [Algebra Y.Fn K] [FiniteDimensional Y.Fn K], ∃ (V : Cover Y) (ρ : V.X ⟶ M.X) (ψ : K →+* V.G.functionField), V.j ≫ ρ = V.π ≫ M.j ∧ ψ.comp (algebraMap Y.Fn K) = V.φ := by
  first | exact @GlobalTheory.Mean4O.NormCover.exists_cover | exact GlobalTheory.Mean4O.NormCover.exists_cover | (intros; apply GlobalTheory.Mean4O.NormCover.exists_cover <;> assumption)
