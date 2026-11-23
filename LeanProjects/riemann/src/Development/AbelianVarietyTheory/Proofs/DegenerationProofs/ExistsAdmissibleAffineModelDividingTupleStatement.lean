import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_affine_model_dividing_tuple' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ ∧ IsAffineOpen U₀ ∧ M.HasDiv t₀ := by
  first | exact @GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple | exact GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple | (intros; apply GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple <;> assumption)
