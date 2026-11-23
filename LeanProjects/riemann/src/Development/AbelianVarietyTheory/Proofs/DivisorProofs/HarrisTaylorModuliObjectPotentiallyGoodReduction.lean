import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulRelDimEqFinrankHarrisTaylorLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingLieMultiplicityZeroCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfOrderLeftActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTPotGood

theorem potGood : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro p _ D R _ b N V K _ _ _ _ _ _ _ _ β o h
  rcases h with h | ⟨hdiv, hn⟩
  · let Ω := AlgebraicClosure K
    have hx : spMap (algebraMap K Ω) ≫ spMap β = spMap ((algebraMap K Ω).comp β) := by
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_embedding_lie_multiplicity_zero_char_zero p D R b N (Sp K) (spMap β) o h Ω (spMap (algebraMap K Ω))
      ((algebraMap K Ω).comp β) hx
    exact GlobalTheory.T.potentialGoodReduction_of_lieMult_zero V K o.A o.ab D.F (o.act.toF D) Ω (algebraMap K Ω) σ hσ
  · obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K o.A o.ab
    have h2g := GlobalTheory.T.two_mul_relDim_eq_finrank_harrisTaylor_lattice p D R b N K β o g hg
    rw [D.rankLa] at h2g
    haveI := D.freeO
    haveI := D.finO
    have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    have hm := D.m_pos
    have hlt : g < Module.finrank ℤ D.O := by
      rw [D.rankO]
      have h1 : D.m * D.n * Module.finrank ℚ D.F < D.m * (2 * D.m) * Module.finrank ℚ D.F := by
        apply Nat.mul_lt_mul_of_pos_right _ hd
        exact Nat.mul_lt_mul_of_pos_left hn hm
      have h2 : D.m * (2 * D.m) * Module.finrank ℚ D.F = 2 * (D.m ^ 2 * Module.finrank ℚ D.F) := by ring
      omega
    exact GlobalTheory.T.potentialGoodReduction_of_order_leftAction V K o.A g o.ab hg D.O o.act.act o.act.hom o.act.one o.act.mul o.act.add hdiv hlt

end GlobalTheory.HTPotGood
