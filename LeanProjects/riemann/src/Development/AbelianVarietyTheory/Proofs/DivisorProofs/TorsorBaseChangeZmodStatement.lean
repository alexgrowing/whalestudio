import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorBaseChangeZmod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_base_change_zmod : ∀ (U B : Type) [CommRing U] [CommRing B] [Algebra U B] (q : ℕ) (D : Type) [CommRing D]
    [Algebra U D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[U] D)), 0 < q →
    GlobalTheory.LocAcyc.IsZModTorsor U D q act →
    ∃ actB : Multiplicative (ZMod q) →* (TensorProduct U B D ≃ₐ[B] TensorProduct U B D),
      GlobalTheory.LocAcyc.IsZModTorsor B (TensorProduct U B D) q actB := by
  first | exact @GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase | exact GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase | (intros; apply GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase <;> assumption)
