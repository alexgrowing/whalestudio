import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupGradedCommOfIsFlipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_eq_cast_of_isTwPair (q : ℕ) [NeZero q] (E : Spc) {n m i j k w : ℤ} (hk : i + j = k) (hw : n + m = w)
    (ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (hν : IsTwPair ν) (a : Ht q E n i) (b : Ht q E m j) :
    ν.cup E hw a b = (cup q a b).cast hw hk := by
  subst hk
  subst hw
  have h := (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).2 (i + j) rfl ν (twPair q i j) hν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 E (n := n) (m := m) rfl
  rw [h]
  rfl

theorem isTwPair_of_isFlip (q : ℕ) {i j k : ℤ} (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)))
    (ν : Pair (res _ (tw q j)) (res _ (tw q i)) (res _ (tw q k))) (hμ : IsTwPair μ) (h : μ.IsFlip ν) : IsTwPair ν := by
  intro U ζ
  rw [h U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ), hμ U ζ]
  simp

theorem cup_comm (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j) :
    cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring) := by
  obtain ⟨ν, hf, -, -⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) (twPair q i j)
  have hν : IsTwPair ν := isTwPair_of_isFlip q _ ν (GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique q i j).1 hf
  have h1 := GlobalTheory.T.cup_graded_comm_of_isFlip (ZMod q) (twPair q i j) ν hf E (n := n) (m := m) (k := n + m) rfl (by ring) a b
  have h2 := cup_eq_cast_of_isTwPair q E (n := m) (m := n) (i := j) (j := i) (k := i + j) (w := n + m) (by ring) (by ring) ν hν b a
  change (twPair q i j).cup E rfl a b = _
  rw [h1, h2]

end GlobalTheory.EtC
