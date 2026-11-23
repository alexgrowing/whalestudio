import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

noncomputable section

namespace UpperTheory.HF.Formalism.HC

open UpperTheory.HF _root_.Formalism _root_.Formalism.HC

namespace Frame

open _root_.Formalism.HC.Frame

variable (φ : Frame)

def oh : ℕ := Nat.card φ.hH.ker

def Thick (T : Finset ℕ) (u : φ.A) (π : φ.GG) : Prop := ∃ s ∈ T, π = φ.tau2 (φ.dig s + u)

def letter {φ : Frame} (g τ : φ.GG) (i : ℤ) : φ.GG := placeOf (g ^ i * τ)

end Frame

namespace HostRaw

open _root_.Formalism.HC.HostRaw

variable {φ : Frame} (H : HostRaw φ)

def frobG (p : ℕ) : φ.GG :=
  if h : Nat.Coprime p H.condN then H.art (ZMod.unitOfCoprime p h) else 1

def Inert (p : ℕ) : Prop := p.Prime ∧ jacobiSym (-(H.d : ℤ)) p = -1

def DRC (B : ℝ) : Set ℕ :=
  {p | H.Inert p ∧ (p : ℝ) ≤ B ∧ φ.cc ∈ Subgroup.zpowers (H.frobG p) ∧ H.frobG p ≠ φ.cc}

def DRh (B : ℝ) : Set ℕ := {p | H.Inert p ∧ (p : ℝ) ≤ B ∧ φ.hH (H.frobG p).2 = 1}

theorem frobG_of_coprime {p : ℕ} (h : Nat.Coprime p H.condN) : H.frobG p = H.art (ZMod.unitOfCoprime p h) := dif_pos h

theorem Inert.ne_two {H : HostRaw φ} {p : ℕ} (h : H.Inert p) : p ≠ 2 := by
  rintro rfl
  have h1 := h.2
  have h8 := H.d_mod_eight
  have h2 : jacobiSym (-(H.d : ℤ)) 2 = jacobiSym 1 2 := by
    apply jacobiSym.mod_left'
    push_cast
    omega
  rw [h2, jacobiSym.one_left] at h1
  exact absurd h1 (by decide)

theorem Inert.not_dvd {H : HostRaw φ} {p : ℕ} (h : H.Inert p) : ¬ p ∣ H.condN :=
  H.not_dvd_condN_of_inert h.1 h.ne_two h.2

theorem Inert.coprime {H : HostRaw φ} {p : ℕ} (h : H.Inert p) : Nat.Coprime p H.condN :=
  h.1.coprime_iff_not_dvd.2 h.not_dvd

end HostRaw

end UpperTheory.HF.Formalism.HC

end
