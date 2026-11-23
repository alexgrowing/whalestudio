import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.AmpCell

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem one_mem_UW' (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem mem_S_of_N (z : Fin (2 * r + k + 1) → ℂ) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : n ∈ Sset k r z := ⟨1, one_mem_UW' z, n, hn, (one_mul n).symm⟩

def Ds (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem Ds_mul_Ds : Ds r * Ds r = 1 := by
  unfold Ds
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  norm_num

theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ZhatO k r z z' g = Zhat k r z z' g * Ds r := by
  ext a b
  simp only [Ds]
  rw [Matrix.mul_diagonal]
  simp only [ZhatO]
  ring

theorem inCell_of_rep {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') {n n' g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r)
    (hn' : n' ∈ Nset k r) {p : Point ℂ (r + 1)} (hZ : ZhatO k r z z' g₀ = ptMat p) :
    IsInCell (ZhatO k r z z' (n * g₀ * n')) p := by
  have hni : n⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hn
  have hE := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ n⁻¹ (mem_S_of_N z hni) n'
    (mem_S_of_N z' hn') g₀
  have hnn : (n⁻¹)⁻¹ = n := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hn.1)
  rw [hnn] at hE
  have hu := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z ⟨hz, hT⟩).1 n⁻¹ (mem_S_of_N z hni)).2.1
  have hu' := ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' ⟨hz', hT'⟩).1 n' (mem_S_of_N z' hn')).2.1
  refine ⟨(Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ, Ds r * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r, fun i j => ⟨fun hij => ?_, fun hij => ?_⟩,
    fun i j => ⟨fun hij => ?_, fun hij => ?_⟩, ?_⟩
  · rw [Matrix.conjTranspose_apply, hu.1 j i hij, star_zero]
  · subst hij; rw [Matrix.conjTranspose_apply, hu.2 i, star_one]
  · unfold Ds; rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hu'.1 i j hij]; ring
  · subst hij; unfold Ds; rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hu'.2 i, mul_one, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [zhatO_eq, hE, ← hZ, zhatO_eq]
    calc (Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ * Zhat k r z z' g₀ * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r
        = (Formalism.FourierDecayAlt.C2.uMap k r z n⁻¹)ᴴ * (Zhat k r z z' g₀ * (Ds r * Ds r)) * Formalism.FourierDecayAlt.C2.uMap k r z' n' * Ds r := by
          rw [Ds_mul_Ds, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem zhat_monomial {z z' : Fin (2 * r + k + 1) → ℂ} {g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hZ : ZhatO k r z z' g₀ = ptMat p) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Zhat k r z z' g₀) := by
  have hinv : Function.Involutive (Formalism.L2.SG.PtCell.pinv p) := Formalism.L2.SG.PtCell.pinv_pinv p
  refine ⟨hinv.toPerm _, fun a => (-1 : ℂ) ^ (r - a.val) * Formalism.L2.SG.PtCell.pval p.1 (Formalism.L2.SG.PtCell.pinv p a).val,
    fun a => mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Formalism.L2.SG.PtCell.pval_ne p.1 (fun b hb => (p.2.1 b hb).1) _ (by rw [p.2.2]; exact (Formalism.L2.SG.PtCell.pinv p a).isLt)),
    ?_⟩
  have hZ' : Zhat k r z z' g₀ = ptMat p * Ds r := by
    rw [← hZ, zhatO_eq, Matrix.mul_assoc, Ds_mul_Ds, Matrix.mul_one]
  rw [hZ', Formalism.L2.SG.PtCell.ptMat_eq_mono]
  ext i a
  rw [show Ds r = Matrix.diagonal (fun b : Fin (r + 1) => (-1 : ℂ) ^ (r - b.val)) from rfl, Matrix.mul_diagonal]
  simp only [Formalism.L2.SG.PtCell.mono, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, Function.Involutive.coe_toPerm]
  by_cases h : a = Formalism.L2.SG.PtCell.pinv p i
  · have h2 : i = Formalism.L2.SG.PtCell.pinv p a := by rw [h, hinv]
    rw [if_pos h]
    simp only [h2, if_true]
    ring
  · have h2 : ¬ i = Formalism.L2.SG.PtCell.pinv p a := fun e => h (by rw [e, hinv])
    rw [if_neg h]
    simp only [h2, if_false]
    ring

theorem cell_representation : Formalism.MainNotions.S.Pv.LemmaJ.CellRep := by
  intro D W γ p θ' νR hz hz' hT hT' hRel hνR
  obtain ⟨p', μR, ⟨n, hn, n', hn', g₀, hγ, hZ', μ₀, h0, h1, hμR⟩, hq⟩ := hνR
  have hcell := inCell_of_rep hz hz' hT hT' hn hn' hZ'
  rw [← hγ] at hcell
  have hpp : p = p' := Formalism.L2.SG.PtCell.isInCell_uniq hRel.2.1 hcell
  subst hpp
  have hnU : n ∈ UH (Hpk D.R.k D.R.rS) := hn.1
  have hn'U : n' ∈ UH (Hpk D.R.k D.R.rS) := hn'.1
  have hu := WeylGroupFacts.isUnit_of_uh hnU
  have hu' := WeylGroupFacts.isUnit_of_uh hn'U
  have hg₀ : g₀ = n⁻¹ * γ * n'⁻¹ := by
    rw [hγ]
    calc g₀ = (n⁻¹ * n) * g₀ * (n' * n'⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu', Matrix.one_mul, Matrix.mul_one]
      _ = n⁻¹ * (n * g₀ * n') * n'⁻¹ := by simp only [Matrix.mul_assoc]
  have hg₀U : g₀ ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [hg₀]
    exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hnU) hRel.1) (WeylGroupFacts.uh_inv hn'U)
  have hGeq : Gf D.R.k D.R.rS W.z W.z' γ = Gf D.R.k D.R.rS W.z W.z' g₀ := by
    rw [hγ]
    exact Formalism.QuantumDeterminants.gInv _ _ _ _ hz hz' n (mem_S_of_N _ hn) n' (mem_S_of_N _ hn') g₀
  have hG : 0 < Gf D.R.k D.R.rS W.z W.z' g₀ := by
    refine lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg _ _ _ _ hz hz' hT hT' g₀ hg₀U) (fun e => hRel.2.2 ?_)
    rw [hGeq, ← e]
  refine ⟨n, hn, n', hn', g₀, hγ, hg₀U, hZ', hG, zhat_monomial hZ', μ₀, h0, h1, ?_⟩
  rw [← hμR]
  exact hq

end Formalism.L2.S.Pv.AmpCell
