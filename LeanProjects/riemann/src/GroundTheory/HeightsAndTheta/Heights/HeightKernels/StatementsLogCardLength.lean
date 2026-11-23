import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open Classical in

def locLen {R : Type*} [CommRing R] (m : Ideal R) (N : Type*) [AddCommGroup N] [Module R N] : ℕ :=
  if h : m.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl N)).toNat
  else 0

def LogCardLength.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [Finite N],
    Real.log (Nat.card N) =
      ∑ᶠ (m : Ideal R) (_ : m.IsMaximal), (locLen m N : ℝ) * Real.log (Nat.card (R ⧸ m))

end

end GroundTheory.Heights₂.Heights
