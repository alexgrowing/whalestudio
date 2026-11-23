import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def IntCoordGeoNum.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ), A * B = 1 → B * A = 1 →
    ∀ (V : Ideal (MRing (dualBlocks T))) (n p : ℕ), IsMultiProjPrime V → p.Prime →
      (C (p : ℤ) : MRing (dualBlocks T)) ∈ V →
      ringKrullDim (MRing (dualBlocks T) ⧸ V) = ((n + Fintype.card Unit : ℕ) : WithBot ℕ∞) →
      ∀ a : Fin n → Unit → ℤ, geoNum n (V.comap (intCoordSubst A)) a = geoNum n V a

example : (-1 : Matrix (Fin 1) (Fin 1) ℤ) * (-1) = 1 ∧
    IsMultiProjPrime (RingHom.ker (Bridge.GeoNum.red (ι := fun _ : Unit => Fin (0 + 1)) 2)) ∧
    Nat.Prime 2 ∧
    (C ((2 : ℕ) : ℤ) : MRing (dualBlocks (Fin 1))) ∈
      RingHom.ker (Bridge.GeoNum.red (ι := fun _ : Unit => Fin (0 + 1)) 2) ∧
    ringKrullDim (MRing (dualBlocks (Fin 1)) ⧸
        RingHom.ker (Bridge.GeoNum.red (ι := fun _ : Unit => Fin (0 + 1)) 2)) =
      ((0 + Fintype.card Unit : ℕ) : WithBot ℕ∞) :=
  ⟨by simp, (Bridge.intNum_map_eq_geoNum_hyps 2 0).1, Nat.prime_two,
    (Bridge.intNum_map_eq_geoNum_hyps 2 0).2.1, (Bridge.intNum_map_eq_geoNum_hyps 2 0).2.2⟩

end

end GroundTheory.Heights₂.Heights
