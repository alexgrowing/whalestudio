import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomExtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusEndomorphismStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem frob_isFrob_unique : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K),
    IsFrob (frob A) ∧ ∀ π : End A, IsFrob π → π = frob A := by
  intro K _ _ A
  have hex : ∃ π : End A, IsFrob π := by
    obtain ⟨π, hπ, -⟩ := GlobalTheory.T.exists_frobenius_endomorphism K A
    exact ⟨π, hπ⟩
  have hf : IsFrob (frob A) := by
    unfold frob
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hf, fun π hπ => ?_⟩
  apply GlobalTheory.AV.AbVar.ext_of_pt_eq
  intro x
  rw [hπ x, hf x]

end GlobalTheory.AV.AbVar
