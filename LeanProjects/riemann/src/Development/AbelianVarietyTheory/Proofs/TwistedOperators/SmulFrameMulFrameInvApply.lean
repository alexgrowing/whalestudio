import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMeasurePiChangeConstantStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

namespace GlobalTheory.IdealChain

theorem smul_frame_mul_frame_inv_apply {k : Type} [Field k]
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ} (a : k) (b b' : ℕ → kˣ)
    (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (r : n ⊕ Fin c) (s : n' ⊕ Fin c') :
    (a • ((frame n c b).val * y * ((frame n' c' b')⁻¹).val)) r s =
      a * Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k)) r *
        Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹) s * y r s := by
  have h1 : (frame n c b).val =
      Matrix.diagonal (Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k))) := by
    rw [← Matrix.fromBlocks_diagonal]; rfl
  have h2 : ((frame n' c' b')⁻¹).val =
      Matrix.diagonal (Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp only [← Units.val_inv_eq_inv_val]
    rfl
  rw [h1, h2, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  ring

theorem opE_rescale_frame : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (α β₀ : kˣ) (b' : ℕ → kˣ) (ν νs : Measure k), (∀ i, 1 ≤ i → i ≤ c → b' i / b' (i + 1) = β₀) → ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ (ψ : AddChar k Circle) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k), opE ψ ν p Ψ x = C * opE (ψ.mulShift (β₀ : k)) νs p (fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => Ψ ((α : k) • ((frame n c fun i => α⁻¹ * b' i).val * y * ((frame n' (c + 1) b')⁻¹).val))) (((α⁻¹ : kˣ) : k) • x) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p α β₀ b' ν νs hb hν hνs
  let d : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → kˣ := fun rs =>
    α * Sum.elim (fun _ : n => 1) (fun i : Fin c => α⁻¹ * b' (i.val + 1)) rs.1.1 *
      (Sum.elim (fun _ : n' => 1) (fun i : Fin (c + 1) => b' (i.val + 1)) rs.1.2)⁻¹
  obtain ⟨C, hC, hF⟩ := @GlobalTheory.T.haar_measure_pi_change_constant k _ _ _ _ _ _ _ (@Subtype.fintype _ _ (Classical.decPred _) _) ν νs d hν hνs
  refine ⟨C, hC, fun ψ Ψ x => ?_⟩
  unfold opE
  rw [hF]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  dsimp only
  congr 1
  · congr 1
    ext r q
    rw [smul_frame_mul_frame_inv_apply]
    by_cases h : Free p (r, q)
    · rcases r with r | r <;> rcases q with q | q
      · exact absurd h (by simp [Free])
      · simp [affPt, basePt, h, d]
      · simp [affPt, basePt, h, d]
      · have : r.val ≠ q.val := by simp only [Free] at h; omega
        simp [affPt, basePt, h, d, this]
    · rcases r with r | r <;> rcases q with q | q
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · by_cases h' : r.val = q.val <;> simp [affPt, basePt, h, h']
  · rw [AddChar.mulShift_apply, mul_neg]
    congr 3
    unfold ch
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by simp [Free]
    rw [← hb (i.val + 1) (by omega) (by omega)]
    simp [affPt, basePt, h, d, div_eq_mul_inv]

end GlobalTheory.IdealChain
