import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.Sieg

def blkC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b c d, M = StdUnn.blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold StdUnn.blk4
  rw [Matrix.fromBlocks_toBlocks]
  simp

theorem submatrix_sum_equiv_fromBlocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (StdUnn.blk4 a b c d).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks a b c d := by
  simp [StdUnn.blk4]

theorem key {R : Type} [CommRing R] {n : ℕ} (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) (Z Z' : Matrix (Fin n) (Fin n) R)
    (hZ : Z' * Z = 1) (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    (h : M * StdUnn.blk4 1 Z 1 (-Z) = StdUnn.blk4 1 Z 1 (-Z) * N) :
    (KeepsDiag finSumFinEquiv M ↔ blkC N = 0) ∧ (blkC N = 0 → StdUnn.blkA N = leviMat finSumFinEquiv M) := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq N
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq M
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, -, h3, -⟩ := StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul] at h1 h3
  simp only [KeepsDiag, leviMat, blkC, StdUnn.blkA, submatrix_sum_equiv_fromBlocks, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, h1, h3]
  refine ⟨⟨fun h4 => ?_, fun h4 => by simp [h4]⟩, fun h4 => by simp [h4]⟩
  have h5 : Z * c = 0 := h2 _ (neg_eq_iff_add_eq_zero.1 (add_left_cancel h4))
  rw [← Matrix.one_mul c, ← hZ, Matrix.mul_assoc, h5, Matrix.mul_zero]

theorem mulVec_upper {R : Type} [CommRing R] {n : ℕ} {N : Matrix (Fin (n + n)) (Fin (n + n)) R} (hN : blkC N = 0)
    (x : Fin (n + n) → R) (hx : ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0) (i : Fin n) :
    (N *ᵥ x) (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := by
  have h : ∀ j : Fin n, N (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) = 0 :=
    fun j => congrFun (congrFun hN i) j
  simp only [Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [h, hx, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

variable {D : D7} {n : ℕ}

theorem mem_upperHalf {x : Fin (n + n) → AE D} :
    x ∈ StdUnn.upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 :=
  funext_iff

theorem mem_siegelParabolic_of {g : StdUnn.G D n} (h : blkC (StdUnn.mat g) = 0) (h' : blkC (StdUnn.mat g⁻¹) = 0) :
    g ∈ StdUnn.P D n := by
  refine fun x => ⟨fun hx => mem_upperHalf.2 (mulVec_upper h x (mem_upperHalf.1 hx)), fun hx => ?_⟩
  have : (StdUnn.mat g⁻¹).mulVec ((StdUnn.mat g).mulVec x) ∈ StdUnn.upperHalf D n :=
    mem_upperHalf.2 (mulVec_upper h' _ (mem_upperHalf.1 hx))
  rwa [Matrix.mulVec_mulVec, show StdUnn.mat g⁻¹ * StdUnn.mat g = StdUnn.mat (g⁻¹ * g) from rfl, inv_mul_cancel,
    show StdUnn.mat (1 : StdUnn.G D n) = 1 from rfl, Matrix.one_mulVec] at this

theorem blkC_of_mem_P {g : StdUnn.G D n} (h : g ∈ StdUnn.P D n) : blkC (StdUnn.mat g) = 0 := by
  funext i j
  exact StdUnn.Model.lower_eq_zero h i j

theorem siegel_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ κ g ∈ GlobalTheory.StdUnn.P D n) ∧ ∀ p : siegelOf finSumFinEquiv (uinc D J₂), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat (κ p)) = (leviOf finSumFinEquiv (uinc D J₂) p).1 := by
  intro D n J₂ T κ hκ J hT
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul, ← Matrix.smul_mul] at hZ
  have h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1 := by rw [cj_rat, ← rat_mul, hZ, rat_one]
  have h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1 := by
    have := congrArg cj h1
    rwa [cj_mul, cj_cj, cj_one] at this
  have hm : (rat T.1 : Mx D (n + n) (n + n)) = StdUnn.blk4 1 (rat Z) 1 (-rat Z) := by
    rw [hT, blk_eq, rat_fromBlocks_map, rat_one, rat_neg]
  have hk : ∀ g : UD D J₂, (KeepsDiag finSumFinEquiv (umat g) ↔ blkC (StdUnn.mat (κ g)) = 0) ∧
      (blkC (StdUnn.mat (κ g)) = 0 → StdUnn.blkA (StdUnn.mat (κ g)) = leviMat finSumFinEquiv (umat g)) := fun g =>
    key _ _ _ _ h2 (fun _ => eq_zero_of_add_self) (by rw [← hm]; exact hκ.mul_eq g)
  have hs : ∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ blkC (StdUnn.mat (κ g)) = 0 := fun g =>
    mem_siegelOf.trans (hk g).1
  refine ⟨fun g => ⟨fun hg => mem_siegelParabolic_of ((hs g).1 hg) ?_, fun hg => (hs g).2 (blkC_of_mem_P hg)⟩,
    fun p => (hk p).2 ((hs p).1 p.2)⟩
  rw [← map_inv]
  exact (hs _).1 (inv_mem hg)

end GlobalTheory.SWLink.Sieg

end
