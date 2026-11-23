import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EntryTest

theorem exists_left_inv {K : Type} [Field K] {m n : ℕ} (P : Matrix (Fin m) (Fin n) K) (h : P.rank = n) :
    ∃ P' : Matrix (Fin n) (Fin m) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [← Matrix.rank, h, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' P, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' P = P.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

theorem exists_right_inv {K : Type} [Field K] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) K) (h : Q.rank = m) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q * Q' = 1 := by
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Q.mulVecLin hrange
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' Q, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' Q = Q.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

variable {D : D7}

theorem hO_test (V W : HSp D) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (x : WO V W) :
    hO V W x ((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) = ∑ a, ∑ d, incA D (N a d) * x d a := by
  have h1 : V.gram⁻¹ * (V.gram * N * W.gram⁻¹) * W.gram = N := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  have hc : ∀ b c, cA D (((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) c b) = incA D ((V.gram * N * W.gram⁻¹) b c) := by
    intro b c
    rw [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, Matrix.of_apply, star_star]
  unfold hO
  simp only [hc]
  generalize V.gram * N * W.gram⁻¹ = M at h1
  subst h1
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_emb_single (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i : Fin a) (j : Fin b)
    (e : D.host.E) (hN : Q * N * P = Matrix.single j i e) (y : Mx D a b) :
    ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k = incA D e * y i j := by
  have h1 : ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k =
      (N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h2 : N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y =
      N.map (incA D) * (P.map (incA D) * y) * Q.map (incA D) := by
    simp only [GlobalTheory.IsoMean.emb, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hN]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  intro D V W a b P Q hP hQ i j c
  obtain ⟨P', hP'⟩ := exists_left_inv P hP
  obtain ⟨Q', hQ'⟩ := exists_right_inv Q hQ
  set N := Q' * Matrix.single j i (D.host.xi0⁻¹ * c) * P' with hNdef
  have hN : Q * N * P = Matrix.single j i (D.host.xi0⁻¹ * c) := by
    rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul, Matrix.mul_assoc, hP', Matrix.mul_one]
  refine ⟨Matrix.of fun q p => star ((V.gram * N * W.gram⁻¹) p q), fun y r => ?_⟩
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.FinTranslate.symplOH_smul_right, ← mul_add,
    GlobalTheory.SplitScalar.symplOH_add_self]
  congr 1
  rw [symplO, hO_test, sum_emb_single V W P Q N i j _ hN y, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

end GlobalTheory.EntryTest
