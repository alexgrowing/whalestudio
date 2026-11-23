import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem frameIdem_inl_mulVec {E : Type} [Field E] {n r : ℕ} (S : E →+* E)
    (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (i : Fin r) (v : Fin n → E) :
    frameIdem S J X Y (some (Sum.inl i)) *ᵥ v = fun a => X a i * ((cT S Y * J) *ᵥ v) i := by
  funext a
  simp only [frameIdem]
  rw [← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, ite_and]

theorem stabilises_flag_span : ∀ (E : Type) [Field E] (S : E →+* E) (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E), cT S Y * J * X = 1 → ∀ (g : Matrix (Fin n) (Fin n) E) (j : Fin r), (∀ α β : FrameIx r, frameLev j α < 2 → frameLev j β = 2 → frameIdem S J X Y α * g * frameIdem S J X Y β = 0) → ∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0 := by
  intro E _ S n r J X Y hXY g j hg l hl
  have hcol : (fun a => X a l) = X *ᵥ Pi.single l 1 := by
    funext a; simp
  have hx : frameIdem S J X Y (some (Sum.inl l)) *ᵥ (fun a => X a l) = fun a => X a l := by
    rw [frameIdem_inl_mulVec, hcol, Matrix.mulVec_mulVec, hXY]
    funext a; simp
  have hβ : frameLev j (some (Sum.inl l) : FrameIx r) = 2 := by simp [frameLev, hl]
  set v : Fin n → E := g *ᵥ (fun a => X a l) with hv
  have hz : ∀ α : FrameIx r, frameLev j α < 2 → frameIdem S J X Y α *ᵥ v = 0 := by
    intro α hα
    have := hg α _ hα hβ
    calc frameIdem S J X Y α *ᵥ v
        = frameIdem S J X Y α *ᵥ (g *ᵥ (frameIdem S J X Y (some (Sum.inl l)) *ᵥ (fun a => X a l))) := by
          rw [hx]
      _ = (frameIdem S J X Y α * g * frameIdem S J X Y (some (Sum.inl l))) *ᵥ (fun a => X a l) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = 0 := by rw [this, Matrix.zero_mulVec]
  have hsum : v = ∑ α, frameIdem S J X Y α *ᵥ v := by
    have h1 : (∑ α, frameIdem S J X Y α) *ᵥ v = ∑ α, frameIdem S J X Y α *ᵥ v :=
      map_sum (Matrix.mulVec.addMonoidHomLeft v) (fun α => frameIdem S J X Y α) Finset.univ
    rwa [sum_frameIdem, Matrix.one_mulVec] at h1
  refine ⟨fun m => if m ≤ j then ((cT S Y * J) *ᵥ v) m else 0, ?_, fun m hm => if_neg (not_le.2 hm)⟩
  refine hsum.trans ?_
  rw [Fintype.sum_option, Fintype.sum_sum_type, hz none (by simp [frameLev]), zero_add]
  have hinr : ∑ i, frameIdem S J X Y (some (Sum.inr i)) *ᵥ v = 0 := by
    refine Finset.sum_eq_zero fun i _ => hz _ ?_
    by_cases h : i ≤ j <;> simp [frameLev, h]
  rw [hinr, add_zero]
  funext a
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ j
  · have := congrFun (frameIdem_inl_mulVec S J X Y i v) a
    simp only [Matrix.mulVec, dotProduct] at this
    simpa [h] using this
  · have h0 := congrFun (hz (some (Sum.inl i)) (by simp [frameLev, h])) a
    simp only [Matrix.mulVec, dotProduct] at h0
    simpa [h] using h0

end GlobalTheory.CompanionTheory.RapidDecay
