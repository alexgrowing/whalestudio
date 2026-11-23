import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackIsogenyEqDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackNotSurjectiveEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_eq_deg_mul_inter : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
      inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hd J _ hJ c
  by_cases hi : IsIsogeny f
  · exact GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul K A B f hi J hJ c
  · have hs : ¬ Surjective f.hom.left := by
      intro hs
      exact hi ⟨GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K A B f hd hs, hs⟩
    rw [GlobalTheory.T.intersection_number_pullback_not_surjective_eq_zero K A B f hd hs J hJ c, deg, if_neg hi]
    simp

end GlobalTheory.AV.AbVar
