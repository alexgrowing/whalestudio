import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceFieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearChoiceEqRealisingPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FrameB.evenFrameBlock_scaling_homogeneous_polynomial : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : FData X D) (c : Kc) (j : ℕ) (La' : X.Lt (j + 1)) (d : D.what₂.Tau → ℤ) (R : XspC (X.Pj (j + 1)) Kc), (∀ m ∈ R.support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 → (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) = (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = d τ) → GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') R = (∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') R := by
  intro p _ X D pos Kc _ _ _ fd c j La' d R hR
  classical
  let blk : Var (X.Pj (j + 1)) → Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v) := fun y => ⟨y.1, y.2.1⟩
  let E : (Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) → Kc := fun b => if IsOddPos b.2 then 1 else c
  have hf : ∀ y, GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') y =
      MvPolynomial.C (E (blk y)) * GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.mk Kc fd j La') y := by
    intro y
    unfold GlobalTheory.FrameB.frF GlobalTheory.FrameB.wV
    simp only [E, blk]
    split_ifs with h1 h2 h2
    · simp only [MvPolynomial.C_1, one_mul]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · simp only [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, Finset.mul_sum, mul_assoc]
  have hm : ∀ m ∈ R.support, (∏ y, E (blk y) ^ m y) = ∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ := by
    intro m hmR
    rw [← Finset.prod_fiberwise Finset.univ blk, ← (posJ X D pos (j + 1)).prod_comp]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hpb : pos.symm (posJ X D pos (j + 1) b) = b := pos.symm_apply_apply b
    have h2 : ∏ y ∈ Finset.univ.filter (fun y => blk y = b), E (blk y) ^ m y =
        E b ^ (∑ y ∈ Finset.univ.filter (fun y => blk y = b), m y) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun y hy => ?_
      rw [(Finset.mem_filter.1 hy).2]
    rw [h2, hpb]
    simp only [E]
    split_ifs with h1 h3 h3
    · exact one_pow _
    · exact absurd h1 h3
    · exact absurd h3 h1
    · have hd := hR m hmR (posJ X D pos (j + 1) b) (by rw [hpb]; exact h1)
      rw [Equiv.symm_apply_apply, ← Finset.sum_filter] at hd
      rw [← hd, ← Nat.cast_sum, zpow_natCast]
  unfold GlobalTheory.FrameB.tau0
  conv_lhs => rw [R.as_sum]
  conv_rhs => rw [R.as_sum]
  simp only [map_sum, Finset.smul_sum, MvPolynomial.aeval_monomial]
  refine Finset.sum_congr rfl fun m hmR => ?_
  rw [← hm m hmR]
  simp only [hf]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring
