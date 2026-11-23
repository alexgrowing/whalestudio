import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem adj_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) (B : Matrix (Fin b) (Fin c) D.host.E) :
    adj D (A * B) = adj D B * adj D A := by
  simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) : adj D (adj D A) = A := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact star_star (A i j)

theorem adj_one {a : ℕ} : adj D (1 : Matrix (Fin a) (Fin a) D.host.E) = 1 := by
  simp [adj, Formalism.UG.cT]

theorem adj_zero {a b : ℕ} : adj D (0 : Matrix (Fin a) (Fin b) D.host.E) = 0 := by
  simp [adj, Formalism.UG.cT]

theorem adj_gram (V : HSp D) : adj D V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  simp only [adj, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact GlobalTheory.LatVac.gram_star V j i

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

variable {D : D7}

theorem exists_decomp_one (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B)
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (hKC : K * C = 1) (hKB : K * B = 0) :
    ∃ N' : Matrix (Fin V.rank) (Fin r) D.host.E,
      C * K + (B * (V'.gram⁻¹ * adj D B * V.gram) + N' * (adj D C * V.gram)) = 1 := by
  set G := V.gram
  set Pi := adj D C * G
  set Pm := V'.gram⁻¹ * adj D B * G
  set N := G⁻¹ * adj D K
  set N' := N - C * (K * N) - B * (Pm * N)
  have hG := GlobalTheory.LatVac.gram_det_isUnit V
  have hG' := GlobalTheory.LatVac.gram_det_isUnit V'
  have hPiC : Pi * C = 0 := hs.frame.2.2
  have hPiB : Pi * B = 0 := hs.orth
  have hBC : adj D B * G * C = 0 := by
    have h := congrArg (adj D) hs.orth
    rw [adj_mul, adj_mul, adj_adj, adj_gram, adj_zero, ← Matrix.mul_assoc] at h
    exact h
  have hPmC : Pm * C = 0 := by
    simp only [Pm, Matrix.mul_assoc] at hBC ⊢
    rw [hBC, Matrix.mul_zero]
  have hPmB : Pm * B = 1 := by
    simp only [Pm, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (adj D B), hs.isom, Matrix.nonsing_inv_mul _ hG']
  have hPiN : Pi * N = 1 := by
    simp only [Pi, N, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, ← adj_mul, hKC, adj_one]
  have hKN' : K * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hKC, hKB, Matrix.one_mul, Matrix.zero_mul, sub_self, sub_zero]
  have hPmN' : Pm * N' = 0 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPmC, hPmB, Matrix.one_mul, Matrix.zero_mul, sub_zero, sub_self]
  have hPiN' : Pi * N' = 1 := by
    simp only [N', Matrix.mul_sub, ← Matrix.mul_assoc, hPiC, hPiB, Matrix.zero_mul, sub_zero]
    simpa only [Pi, N, Matrix.mul_assoc] using hPiN
  let M : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows K (Matrix.fromRows Pm Pi)
  let Q : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E :=
    Matrix.fromCols C (Matrix.fromCols B N')
  have hMQ : M * Q = 1 := by
    simp only [M, Q, Matrix.fromRows_mul, Matrix.mul_fromCols, hKC, hKB, hKN', hPmC, hPmB, hPmN', hPiC, hPiB, hPiN']
    refine Matrix.ext fun a b => ?_
    rcases a with a | a | a <;> rcases b with b | b | b <;> simp [Matrix.one_apply]
  have e : Fin r ⊕ (Fin V'.rank ⊕ Fin r) ≃ Fin V.rank :=
    Fintype.equivOfCardEq (by simp [hs.rank]; ring)
  have hQM : Q * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hMQ
  refine ⟨N', ?_⟩
  simpa only [M, Q, Matrix.fromCols_mul_fromRows] using hQM

end GlobalTheory.HalfDecomp

namespace GlobalTheory.HalfDecomp

theorem half_decomp : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ (a : AE D) (u : WO V W), IsHalf a u → ∃ (y : Mx D W.rank r) (x : WO V' W) (t : Mx D W.rank r), IsHalf a y ∧ IsHalf a x ∧ IsHalf a t ∧ u = isoPart V W C y + midPart V V' W B x + restEmb V W K t := by
  intro D V V' W r C B hs K hKC hKB a u hu
  obtain ⟨N', hN'⟩ := exists_decomp_one V V' C B hs K hKC hKB
  refine ⟨HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (N'.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (B.map (incA D)),
    HMul.hMul (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (C.map (incA D)),
    isHalf_mul hu _, isHalf_mul hu _, isHalf_mul hu _, ?_⟩
  have h1 := congrArg (fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (incA D)) hN'
  simp only [Matrix.map_add, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [isoPart, midPart, restEmb, Matrix.map_mul, Matrix.mul_assoc]
  conv_lhs => rw [← Matrix.mul_one u, ← h1]
  simp only [Matrix.map_add _ (map_add (incA D)), Matrix.map_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

end GlobalTheory.HalfDecomp

end
