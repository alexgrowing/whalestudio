import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatCoord

set_option maxHeartbeats 1000000 in

theorem coords_rat {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank)
    (u : GL (Fin ρ) (AE D)) (hQ : d.nC c' * (d.nB b' * d.levi u) ∈ GQ V) :
    c'.1 ∈ ratMx D ρ ρ ∧ b' ∈ ratMx D ρ V₀.rank ∧ u.1 ∈ ratMx D ρ ρ ∧ (u⁻¹).1 ∈ ratMx D ρ ρ := by
  generalize hg : d.nC c' * (d.nB b' * d.levi u) = g at hQ
  have hM : mt V g ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g).1 hQ
  have hM' : mt V g⁻¹ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V g⁻¹).1 (inv_mem hQ)
  have hX : mt V g ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.levi_jX, cancel₂ (d.nB_jX _), cancel₂ (d.nC_jX _)]
  have hX' : mt V g⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
    calc mt V g⁻¹ ⬝ d.jX = mt V g⁻¹ ⬝ (d.jX ⬝ u.1 ⬝ (u⁻¹).1) := by
          rw [Matrix.mul_assoc d.jX, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have h0 : mt V g ⬝ d.j0 = d.j0 + d.jX ⬝ b' := by
    rw [← hg]; simp only [mt_mul, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.nB_j0, Matrix.mul_add, cancel₂ (d.nC_jX _), d.nC_j0]
  have hY : d.pX ⬝ (mt V g ⬝ d.jY) = (c'.1 - half D • (b' ⬝ plus V₀ b')) ⬝ adj (u⁻¹).1 := by
    rw [← hg, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, cancel₂ (d.nB_jY _)]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₂ (d.nC_jY _),
      cancel₂ (d.nC_j0 _), cancel₂ (d.nC_jX _), cancel₂ d.pX_jY, cancel₂ d.pX_jX, cancel₂ d.pX_j0, d.pX_jY, d.pX_jX,
      d.pX_j0, Matrix.one_mul, Matrix.zero_mul, zero_add, zero_sub, sub_zero]
  have hu1 : u.1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g ⬝ d.jX) = u.1 := by rw [hX, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hu2 : (u⁻¹).1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V g⁻¹ ⬝ d.jX) = (u⁻¹).1 := by rw [hX', cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM' (rat_mem _))
  have hb : b' ∈ ratMx D ρ V₀.rank := by
    have e : d.pX ⬝ (mt V g ⬝ d.j0) = b' := by
      rw [h0, Matrix.mul_add, d.pX_j0, zero_add, cancel₂ d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))
  have hc : c'.1 = d.pX ⬝ (mt V g ⬝ d.jY) ⬝ adj u.1 + half D • (b' ⬝ plus V₀ b') := by
    have e : adj (u⁻¹).1 ⬝ adj u.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
    rw [hY, Matrix.mul_assoc, e, Matrix.mul_one, sub_add_cancel]
  refine ⟨?_, hb, hu1, hu2⟩
  rw [hc]
  exact add_mem (ratMx_mul (ratMx_mul (rat_mem _) (ratMx_mul hM (rat_mem _))) (ratMx_adj hu1))
    (ratMx_smul _ (ratMx_mul hb (ratMx_mul (rat_mem _) (ratMx_adj hb))))

theorem rat_coords_of_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ (c : skewA D ρ) (b : Mx D ρ V₀.rank) (u : UX D ρ), γ = d.nC c * (d.nB b * d.levi u.1) ∧ c.1 ∈ ratMx D ρ ρ ∧ b ∈ ratMx D ρ V₀.rank ∧ u ∈ UXQ D ρ := by
  intro D V V₀ ρ d γ hQ hN
  obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.T.flag_unipotent_fourier_jacobi_group_structure D V V₀ ρ d).1 γ).1 hN
  have hγ : d.levi u * (d.nB b * d.nC c) = d.nC (skewConj u.1 c) * (d.nB (u.1 ⬝ b) * d.levi u) := by
    rw [← mul_assoc, d.levi_mul_nB, mul_assoc, d.levi_mul_nC, ← mul_assoc, ← d.nC_mul_nB, mul_assoc]
  rw [hγ] at hQ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := coords_rat d _ _ u hQ
  exact ⟨skewConj u.1 c, u.1 ⬝ b, ⟨u, hu⟩, rfl, h1, h2, h3, h4⟩

end GlobalTheory.RatCoord

end
