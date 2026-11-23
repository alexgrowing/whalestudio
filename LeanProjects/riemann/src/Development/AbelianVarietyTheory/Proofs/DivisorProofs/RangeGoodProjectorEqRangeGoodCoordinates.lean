import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalRingCardinality.DataBu
import Formalism.QuotientMetricDivisors.FinalW

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
    {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G)
    (ψ : P →* Kˣ) :
    LinearMap.range (S.lvlOp r P ψ (idemOf X)).mulVecLin =
      LinearMap.range (S.lvlPr r P ψ * S.V0E r X P ψ).mulVecLin := by
  have hE : LinearMap.range (S.lvlE r P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hV : LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (goodAt X P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hm : S.gaMat r (goodAt X P ψ) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ) :=
    (group_action_matrix_hom K S G r).2 _ _
  unfold CSD.lvlOp
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp,
    hE, hV, hm, Matrix.mulVecLin_mul, LinearMap.range_comp, Submodule.map_comp]

theorem range_goodProjector_eq_range_goodCoordinates : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn D.what₂.LL G Pl0 T m) (s : ℕ), A.fam.Ok s → ∀ (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T),
    LinearMap.range (rE D A P ψ t).mulVecLin = LinearMap.range (rV0 D A P ψ t).mulVecLin := by
  intro D G _ _ Pl0 T m A s _ P ψ t
  exact range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E (A.fam.R t).S (A.fam.R t).r A.X P ψ

end GlobalTheory
