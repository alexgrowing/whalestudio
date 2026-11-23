import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCellStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBlocStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitDetAddMulOfFromBlocksLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceHermitianStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti_split_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ H : Subgroup (GlobalTheory.DblVac.UD σ V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PDiag σ V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PAnti σ V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 H hD hA g hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ := GlobalTheory.T.exists_admissible_unipotent_at_split_place GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing σ B V r s hB hV v hv hψ h2 g hg
  obtain ⟨p, hpK, hpD, hp⟩ := GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock σ V v h2 Y hYat hYlat hYadm
  obtain ⟨hpgK, hpg⟩ := hp g hg
  have hbig : GlobalTheory.DblVac.BigCell V v (p * g) := ⟨M, by rw [hpg]; exact hM, hMlat⟩
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ V v h2 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
