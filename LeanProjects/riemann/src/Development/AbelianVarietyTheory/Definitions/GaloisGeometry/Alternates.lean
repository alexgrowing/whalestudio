import Mathlib
import Formalism.LocalRingCardinality.DataParams

noncomputable section

namespace GlobalTheory.HTW

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def Alternates {n : ℕ} (up : ZMod n → Bool) : Prop := ∀ i, up (i + 1) = !up i

def NoThree {n : ℕ} (th : ZMod n → Prop) : Prop := ∀ i, ¬ (th i ∧ th (i + 1) ∧ th (i + 2))

def WindowTwo {n : ℕ} (th : ZMod n → Prop) (L : ℕ) : Prop :=
  ∀ (i : ZMod n) (a b c : ℕ), a < b → b < c → c < L → ¬ (th (i + a) ∧ th (i + b) ∧ th (i + c))

def Clusters {n : ℕ} (th : ZMod n → Prop) (j : ℕ) : Prop :=
  ∃ (F : Set (ZMod n)) (sp : ZMod n → ℕ),
    (∀ x ∈ F, th x ∧ sp x ≤ j ∧ sp x < n ∧ th (x + sp x) ∧
      (∀ q : ℕ, 0 < q → q < sp x → ¬ th (x + q)) ∧ (∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ th (x - q))) ∧
    ∀ y, th y → ∃! x, x ∈ F ∧ (y = x ∨ y = x + sp x)

structure WordData (n : ℕ) where
  up : ZMod n → Bool
  sz : ZMod n → ℤ
  b : ℕ
  w : ℕ
  S : ℕ
  η : ℕ
  m : ℕ
  J1 : ZMod n → Set ℤ
  J2 : ZMod n → Multiset ℤ

namespace WordData

variable {n : ℕ} (W : WordData n)

def thick (i : ZMod n) : Prop := (W.b : ℤ) ≤ W.sz i ∧ W.sz i ≤ W.b + W.η

def T1 : Prop := ∀ i, ∀ u ∈ W.J1 i,
  (if W.up i then W.sz i ≤ u ∧ u ≤ W.sz i + W.S else -W.sz i - W.S ≤ u ∧ u ≤ -W.sz i) ∨ |u| ≤ W.η

def T2 : Prop := ∀ i, (∀ u ∈ W.J2 i, u ∈ W.J1 i) ∧ ((W.J2 i).filter fun u : ℤ => |u| ≤ (W.η : ℤ)).card ≤ W.m

def ThickOr : Prop := ∀ i, W.thick i ∨ W.sz i ≤ W.w

def G : ℕ := W.w + W.S + W.η

def Mi (i : ZMod n) : ℕ := if W.up i then W.η else max W.η (W.sz i + W.S).toNat

def hi (i : ZMod n) : ℕ := if W.up i then max W.η (W.sz i + W.S).toNat else W.η

def HypA (j : ℕ) : Prop :=
  (∀ i, 0 ≤ W.sz i) ∧ 1 ≤ j ∧ j + 1 ≤ n ∧ ((∃ i, W.thick i) → 40 * (j + 1) * (W.G + 1) ≤ W.b) ∧
    Clusters W.thick j

def Box : Prop :=
  1 ≤ W.b ∧ 1 ≤ W.w ∧ 20 * W.w ≤ W.b ∧ 20 * W.η ≤ W.b ∧ 20 * W.S ≤ W.b ∧ ∀ i, (W.η : ℤ) < W.sz i

def HypNT : Prop := Alternates W.up ∧ (∃ i, ¬ W.thick i) ∧ NoThree W.thick

def HypAT (l : ℕ) : Prop :=
  Even n ∧ Alternates W.up ∧ ∀ M : ℤ, IsGreatest (Set.range W.sz) M → ∀ i,
    1 ≤ W.sz i ∧ ((M : ℝ) + W.S) / 2 ≤ W.sz i ∧
    2 * (((M : ℝ) + W.S + W.η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 +
      (Real.logb l (2 * ((M : ℝ) + W.S + W.η)) + 1)) + W.η + 1 ≤ W.sz i

end WordData

def plc {fr : Formalism.HC.Frame} (g : fr.GG) : fr.GG := if g.1.2 = 1 then g else fr.cc * g

theorem plc_mem {fr : Formalism.HC.Frame} (g : fr.GG) : plc g ∈ fr.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff]
  unfold plc
  split_ifs with h
  · exact h
  · have h' : g.1.2 = -1 := (Int.units_eq_one_or g.1.2).resolve_left h
    simp [Formalism.HC.Frame.cc, c0, h']

def Thick {R : Ranks} (H : Host R) (g : R.GG) : Prop := plc g ∈ H.thickPlaces

def letter {fr : Formalism.HC.Frame} (τ φ : fr.GG) (i : ZMod (orderOf φ)) : fr.GG := τ * φ ^ i.val

def pos {fr : Formalism.HC.Frame} (ε : ℤˣ) (g : fr.GG) : Bool := decide (g.1.2 = ε)

section Jumps

variable {R : Ranks} (P : HCParam R) (j : Fin R.m)

def cloud : Multiset ℤ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map fun i => ⌊P.e j⌋ + ⌊P.v i⌋ + ((R.t : ℤ) - 1) / 2

def lows : Multiset ℤ :=
  (Finset.univ : Finset (Fin R.m)).val.map fun i => ⌊P.e j⌋ - ⌊P.b i⌋ + ((R.t : ℤ) - 1) / 2

def block (R : Ranks) : Multiset ℤ := (Multiset.range R.t).map fun c : ℕ => (c : ℤ)

def jW (s : Bool) : Multiset ℤ :=
  if s then cloud P j + lows P j else (cloud P j + lows P j).map fun u => (R.t : ℤ) - 1 - u

def jR (s : Bool) : Multiset ℤ := jW P j s + block R

def jT2 (s : Bool) : Multiset ℤ := (jW P j s).map fun u => -u - 1

def jT1 (s : Bool) : Multiset ℤ := (jR P j s).map fun u => -u - 1

def szT (s : Bool) : ℤ := if s then ⌊P.e j⌋ + ((R.t : ℤ) + 1) / 2 else ⌊P.e j⌋ - ((R.t : ℤ) + 1) / 2

end Jumps

section Page

variable {D : D7} (L : SizeData₂ D)

def hcAt (D : D7) (g : D.R.GG) : HCParam D.R := D.hc (D.eTau.symm ⟨plc g, plc_mem g⟩)

def bHat : ℕ := ⌈L.sc.b⌉₊ - (D.R.t + 1) / 2

def etaHat : ℕ := ⌊L.etaSz⌋₊ + D.R.t + 2

def sHat : ℕ := ⌊L.Sc⌋₊

def wMax (D : D7) : ℕ :=
  sSup {s : ℕ | ∃ (g : D.R.GG) (j : Fin D.R.m), ¬ Thick D.host g ∧ s = ⌊(hcAt D g).e j⌋.toNat}

def wHat (D : D7) : ℕ := wMax D + (D.R.t + 1) / 2

def hPage : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t

def depth (l : ℕ) : ℕ := sInf {j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j}

def pageWord (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) : WordData (orderOf φ) where
  up i := !pos ε (letter τ φ i)
  sz i := szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))
  b := bHat L
  w := wHat D
  S := sHat L
  η := etaHat L
  m := D.R.m
  J1 i := {u | u ∈ jT1 (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))}
  J2 i := jT2 (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i))

def Roomy (C : ℝ) : Prop :=
  100 ≤ C ∧ (100 : ℝ) ≤ L.sc.w'' D.R.n ∧
  100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧
  L.sc.w'' D.R.n ≤ L.sc.b' ∧
  (∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b') ∧
  C * ((D.host.Lw : ℝ) + 1) * L.sc.b' ≤ L.sc.b

end Page

end GlobalTheory.HTW
