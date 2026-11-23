import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionPropsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorPropsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataPeriodsBalancedMatrixActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorPairingFactorInclusionPeriodsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem TensO.idem_binv_alg {r : ℕ} (s : SymUnit r) (i₀ : Fin r)
    (hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀) :
    (∃ b : ℕ, 0 < b ∧ Star.star (TensO.idem s i₀) * TensO.idem s i₀ =
        b • (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀)) ∧
      Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ =
        Star.star (TensO.idem s i₀) * Star.star (TensO.binv s) * TensO.idem s i₀ ∧
      ∃ g : TensO s, g * (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀) = TensO.idem s i₀ := by
  have hf : Star.star (TensO.binv s) = TensO.binv s := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)
    rw [TensO.inv_transpose, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hEE : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 =
      Matrix.single i₀ i₀ 1 := by simp
  have hET : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose = Matrix.single i₀ i₀ 1 := by simp
  have hmain : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) := by
    rw [hET, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc, hEE]
  have hefe : Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ = TensO.binv s * TensO.idem s i₀ := hmain
  refine ⟨⟨((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat, by omega, ?_⟩, by rw [hf], TensO.ofMat s s.1, ?_⟩
  · rw [hefe]
    have h : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
        (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        Matrix.single i₀ i₀ (1 : ℤ) = ((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat •
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) := by
      rw [hET, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single i₀ i₀ (1 : ℤ)),
        Matrix.single_mul_mul_single, ← Matrix.mul_smul]
      congr 1
      rw [Matrix.smul_single, nsmul_eq_mul, Int.toNat_of_nonneg hp.le]
      simp
    exact h
  · rw [hefe]
    have h : (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) =
        Matrix.single i₀ i₀ (1 : ℤ) := by
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    exact h

theorem Tens.nonempty_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ),
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
      ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D D' r W hpos hdet T hr
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := T.mod s
  obtain ⟨hhom, h1, hmul, hadd⟩ := GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties R D.toPre D'.toPre W T
  obtain ⟨hinc, hip, hpi, hcx⟩ := GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props R D.toPre D'.toPre W T i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := GlobalTheory.T.mumfordTensorData_latticeFactor_props R D.toPre D'.toPre W T s i₀
  obtain ⟨w, hw, htau⟩ := GlobalTheory.T.mumfordTensorPairing_factorInclusion_periods R hR D D' W hdet hpos T i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := T.mod s
    o := { onB := { act := fun a => T.act (TensO.mat s a)
                    hom := fun a => hhom _
                    map_one := h1
                    map_mul := fun a b => hmul _ _
                    map_add := fun a b => hadd _ _
                    rosati := GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef R hR D D' W hdet hpos T }
           c_lin := GlobalTheory.T.tensor_action_compatible_with_degeneration R D.toPre D'.toPre W T s
           tau_bal := GlobalTheory.T.tensorDegData_periods_balanced_matrixAction R hR D D' W hdet hpos T }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := T.inc i₀
    pr := T.pr i₀
    xi := T.xi i₀
    xp := T.xp i₀
    w := w
    idem := TensO.idem_mul_idem s i₀
    inc_hom := hinc
    pr_hom := T.pr_hom i₀
    inc_pr := hip
    pr_inc := hpi
    xp_xi := hxx
    xi_xp := hxe
    c_xi := hcx
    inj := hinj
    onto := honto
    w_gen := hw
    tau := htau }, TensO.idem_binv_alg s i₀ hp⟩

end GlobalTheory.Mum
