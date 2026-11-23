import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isFinite_etale_surjective_of_isQuasiInv : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left := by
  intro Y A B _ _ k ψ ψ' hA hB hk hq
  obtain ⟨-, -, h1, h2⟩ := hq
  obtain ⟨⟨hAf, hAe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hk
  obtain ⟨⟨-, hBe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hk
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h1, Over.comp_left] at hAf hAe
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h2, Over.comp_left] at hBe
  haveI := hB.proper
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI := IsSeparated.of_comp ψ'.left A.hom
  haveI := FormallyUnramified.of_comp ψ'.left ψ.left
  haveI := locallyOfFiniteType_of_comp ψ'.left ψ.left
  refine ⟨IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨fun b => ?_⟩
    have hu := hk.map (Y.evaluation ⊤ (B.hom.base b) trivial).hom
    rw [map_natCast, Nat.cast_zero] at hu
    exact absurd hu not_isUnit_zero
  · obtain ⟨-, hs, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk0
    rw [← h2, Over.comp_left] at hs
    exact Surjective.of_comp ψ'.left ψ.left

end GlobalTheory.UPel.HT.ES
