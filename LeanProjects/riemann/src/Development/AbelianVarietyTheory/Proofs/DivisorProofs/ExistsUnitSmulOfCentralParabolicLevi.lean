import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalCoordinatesGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviSectionIsotropicFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectHaarMeasureProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

namespace GlobalTheory.CentralLevi

theorem exists_unit_smul_of_central : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ f g hg hc
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ f

  let Dα : GL (Fin (r + 1)) (AF F ⊗[F] E) → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun α =>
    ⟨cT (sigR (AF F) σ) (α⁻¹).1, cT (sigR (AF F) σ) α.1,
      by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one],
      by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]⟩
  have hmem : ∀ α, lv α ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := fun α => by
    refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => ?_
    rw [Finset.mem_singleton] at hk
    subst hk
    exact ⟨⟨α, trivial, hlv.onC α⟩, ⟨Dα α, trivial, hlv.onD α⟩⟩
  obtain ⟨B, -, hB⟩ := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg (Fin.last r)) (Finset.mem_singleton_self _)).1
  change GL (Fin (r + 1)) (AF F ⊗[F] E) at B
  change (matHom _ σ J g).1 * adMat F X = adMat F X * B.1 at hB
  have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, f.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcomm : ∀ α : GL (Fin (r + 1)) (AF F ⊗[F] E), B.1 * α.1 = α.1 * B.1 := fun α => by
    have e := congrArg (fun h => (matHom _ σ J h).1 * adMat F X) (hc (lv α) (hmem α))
    simp only [map_mul, Units.val_mul] at e
    have e1 : (matHom _ σ J g).1 * (matHom _ σ J (lv α)).1 * adMat F X = adMat F X * (B.1 * α.1) := by
      rw [Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have e2 : (matHom _ σ J (lv α)).1 * (matHom _ σ J g).1 * adMat F X = adMat F X * (α.1 * B.1) := by
      rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hlv.onC, Matrix.mul_assoc]
    have := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) (e1.symm.trans (e.trans e2))
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using this
  obtain ⟨c, hcB⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := B.1) fun t =>
    (hcomm ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩).symm
  have hu : IsUnit c := by
    have h1 := congrFun (congrFun (Units.mul_inv B) 0) 0
    rw [← hcB, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h1
    exact ⟨⟨c, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, ?_⟩
  rw [hB, ← hcB, IsUnit.unit_spec]
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

end GlobalTheory.CentralLevi
