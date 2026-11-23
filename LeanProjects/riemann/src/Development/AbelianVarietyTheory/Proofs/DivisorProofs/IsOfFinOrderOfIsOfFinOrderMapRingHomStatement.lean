import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHom

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 → (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B, IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  first | exact @GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom | exact GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom | (intros; apply GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom <;> assumption)
