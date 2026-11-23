import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzHeis

section Blocks
variable {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n)

theorem block_mul₂ (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem bl_add (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  unfold bl
  rw [← Matrix.fromBlocks_add]
  rfl

theorem block_sub (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d - bl hn a' b' c' d' = bl hn (a - a') (b - b') (c - c') (d - d') := by
  ext i j
  simp only [bl, Matrix.sub_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  ext i j
  simp only [bl, Matrix.zero_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem det_bl_lower (c : Matrix (Fin p) (Fin ρ) R) : (bl hn 1 0 c 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

end Blocks

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  have e : chz ψ b₀ (a + b) = ψ (GlobalTheory.CompanionTheory.FourierN.pr b₀.1 (a.1 + b.1)) := rfl
  rw [e, GlobalTheory.CompanionTheory.FourierN.pr_add_right, AddChar.map_add_eq_mul]
  rfl

theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    conj (chz ψ b₀ a) = conj (chz ψ b₀ (a + b)) * chz ψ b₀ b := by
  have hb : ‖chz ψ b₀ b‖ = 1 := hψ.2.1 _
  rw [chz_add, map_mul, mul_assoc, Complex.conj_mul', hb]
  simp

variable {hn : ρ + p = n} (M : Maps D hn)

theorem mat_u (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    mat (M.nzx 0 x₀ * M.emb g₁) = blk4 1 (bl hn 0 x₀ (adj x₀) b) 0 1 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  rw [LeftInvSect.mat_mul, M.nzx_mat, h1, submatrix_fromBlocks_mul]
  simp [bl_add]

theorem nzx_comm (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (ζ z₀ : hermA D ρ) :
    M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁) = (M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [LeftInvSect.mat_mul, LeftInvSect.mat_mul, LeftInvSect.mat_mul, mat_u M g₁ b hg, M.nzx_mat, M.nzx_mat, M.nzx_mat, h1]
  simp only [submatrix_fromBlocks_mul, bl_add, adj_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [show (ζ + z₀).1 = z₀.1 + ζ.1 from add_comm _ _]

theorem q_mat (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    ∃ (β δ : Mx D n n), mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹) = blk4 (bl hn 1 0 (adj x₀) 1) β 0 δ := by
  have h := GlobalTheory.CompanionTheory.SwUnf.SmallCell.conj_block M.w (M.nzx 0 x₀ * M.emb g₁) M.w_mat (mat_u M g₁ b hg x₀)
  have hC : adj (bl hn (-1 : Mx D ρ ρ) 0 0 0) = bl hn (-1) 0 0 0 := by
    simp [adj_bl, adj_zero, adj_neg, adj_one]
  rw [hC] at h
  have e1 : (1 : Mx D n n) - bl hn 0 0 0 1 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0 = bl hn 1 0 (adj x₀) 1 := by
    rw [← blockRowSubstitution_one hn]
    simp [block_mul₂, block_sub]
  have e2 : -(bl hn (-1 : Mx D ρ ρ) 0 0 0 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0) = (0 : Mx D n n) := by
    simp [block_mul₂, blockMatrix_zero]
  rw [e1, e2] at h
  exact ⟨_, _, h⟩

theorem law_q (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ) (hf : IsLaw χ z f) (g₁ : G D p) (b : Mx D p p)
    (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (v : G D n) :
    f (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * v) = f v := by
  obtain ⟨β, δ, hq⟩ := q_mat M g₁ b hg x₀
  let a : GL (Fin n) (AE D) := ⟨bl hn 1 0 (adj x₀) 1, bl hn 1 0 (-adj x₀) 1,
    by simp [block_mul₂, blockRowSubstitution_one], by simp [block_mul₂, blockRowSubstitution_one]⟩
  have hdet : Matrix.GeneralLinearGroup.det a = 1 := Units.ext (det_bl_lower hn _)
  have hA : blkA (mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹)) = a.1 := by
    rw [hq]
    simp [blkA, blk4, a]
  rw [hf _ (GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq) a hA v, hdet, map_one, map_one]
  simp [npow]

theorem wz_heis : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₁ : G D p) (b : Mx D p p),
  mat g₁ = blk4 1 b 0 1 → ∀ (z₀ : hermA D ρ) (x₀ : Mx D ρ p) (x : G D n),
    Wz M m ψ b₀ f (M.nzx z₀ x₀ * M.emb g₁ * x) = chz ψ b₀ z₀ * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ hψ b₀ χ z f hf g₁ b hg z₀ x₀ x
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨hlam, -, -⟩ := m.hz
  have step : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) =
      f (M.w * M.nzx (ζ + z₀) 0 * x) := by
    intro ζ
    have e : M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x) =
        M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * (M.w * M.nzx (ζ + z₀) 0 * x) := by
      have h := nzx_comm M g₁ b hg x₀ ζ z₀
      calc M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)
          = M.w * (M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁)) * x := by group
        _ = M.w * ((M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0) * x := by rw [h]
        _ = _ := by group
    rw [e, law_q M χ z f hf g₁ b hg x₀]
  unfold Wz
  calc ∫ ζ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) ∂m.lz
      = ∫ ζ, (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) (ζ + z₀) ∂m.lz := by
        refine integral_congr_ae (.of_forall fun ζ => ?_)
        show f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) =
          chz ψ b₀ z₀ * (f (M.w * M.nzx (ζ + z₀) 0 * x) * conj (chz ψ b₀ (ζ + z₀)))
        rw [step, conj_chz ψ hψ b₀ ζ z₀]
        ring
    _ = ∫ y, chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y)) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz) (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) z₀
    _ = _ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.WzHeis
end
