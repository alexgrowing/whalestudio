import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace UpperTheory.N.TwistK

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def TBe (PD : PeriodData G Qp K₀ K B BdR) (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O]
    [Algebra O LL] (I : Subgroup G) : Prop :=
  ∀ (e : ℕ) (Ve : LocLat G Qp LL O), Module.finrank LL Ve.V = 1 →
    (∀ g x, Ve.ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) →
    (∀ n : ℕ, Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology Ve.L ⧸ divisibleFiniteCohomology PD Ve.L)
        (((PD.p : ℕ) : O) ^ n)) ≤ (((Module.finrank Qp K + 1) * n : ℕ) : ℕ∞) * lenOl PD (O := O)) ∧
    (0 < e → HfD PD Ve.L = BD Ve.L) ∧
    (e = 0 → ∀ c : G → Ve.V ⧸ Ve.L.T, c ∈ HfD PD Ve.L ↔
      (c ∈ divisibleCocycles Ve.L ∧ ∃ x, ∀ g ∈ I, c g = actD Ve.L g x - x))

end
end UpperTheory.N.TwistK

end
