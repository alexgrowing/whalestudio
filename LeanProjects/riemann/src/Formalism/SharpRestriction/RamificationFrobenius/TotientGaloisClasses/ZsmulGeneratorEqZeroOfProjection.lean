import Mathlib
import Formalism.FrobeniusOrbits.Statement

noncomputable section

namespace Formalism.HC

open Formalism.FrobeniusOrbits

def Idx (n : ℕ) : Type := Fin n

instance (n : ℕ) : Fintype (Idx n) := inferInstanceAs (Fintype (Fin n))
instance (n : ℕ) : DecidableEq (Idx n) := inferInstanceAs (DecidableEq (Fin n))

structure Frame where
  e : ℕ

  ord : ℕ
  grp : AddCommGroup (Idx ord)
  h0 : letI := grp; Idx ord →+ Additive (HGrp e)
  projection_surjective_field : Function.Surjective h0
  gen0 : Idx ord
  zsmul_generator_eq_zero_of_projection : letI := grp; ∀ k : ℤ, h0 (k • gen0) = 0 → k • gen0 = 0

namespace Frame

variable (φ : Frame)

def A : Type := Idx φ.ord

instance : AddCommGroup φ.A := φ.grp
instance : Fintype φ.A := inferInstanceAs (Fintype (Idx φ.ord))
instance : DecidableEq φ.A := inferInstanceAs (DecidableEq (Idx φ.ord))

def A.val {φ : Frame} (t : φ.A) : ℕ := Fin.val (n := φ.ord) t

theorem A.val_lt {φ : Frame} (t : φ.A) : t.val < φ.ord := by
  exact Fin.is_lt (n := φ.ord) t

theorem A.val_injective (φ : Frame) : Function.Injective (A.val : φ.A → ℕ) := by
  exact fun s t h => Fin.ext h

def A.ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : φ.A := (⟨u, hu⟩ : Fin φ.ord)

@[simp] theorem A.val_ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : (A.ofVal u hu : φ.A).val = u := rfl

theorem card_A : Fintype.card φ.A = φ.ord := by
  exact Fintype.card_fin φ.ord

theorem natCard_A : Nat.card φ.A = φ.ord := by
  rw [Nat.card_eq_fintype_card, card_A]

theorem ord_pos : 0 < φ.ord := by
  exact Fin.pos (n := φ.ord) (0 : φ.A)

def h : φ.A →+ Additive (HGrp φ.e) := φ.h0

theorem h_surj : Function.Surjective φ.h := by
  exact φ.projection_surjective_field

def a0 : φ.A := φ.gen0

def A0 : AddSubgroup φ.A := AddSubgroup.zmultiples φ.a0

theorem zsmul_generator_eq_zero_of_image (k : ℤ) (hk : φ.h (k • φ.a0) = 0) : k • φ.a0 = 0 := by
  exact φ.zsmul_generator_eq_zero_of_projection k hk

def n0 : ℕ := addOrderOf φ.a0

def o : ℕ := φ.ord / φ.n0

def dig (s : ℕ) : φ.A := s • φ.a0

theorem dig_def (s : ℕ) : φ.dig s = s • φ.a0 := rfl

def ofNat (u : ℕ) : φ.A := A.ofVal (u % φ.ord) (Nat.mod_lt _ φ.ord_pos)

theorem val_ofNat (u : ℕ) : (φ.ofNat u).val = u % φ.ord := rfl

theorem val_ofNat_of_lt {u : ℕ} (hu : u < φ.ord) : (φ.ofNat u).val = u := by
  rw [φ.val_ofNat u, Nat.mod_eq_of_lt hu]

@[simp] theorem ofNat_val (t : φ.A) : φ.ofNat t.val = t := by
  apply A.val_injective φ
  rw [φ.val_ofNat, Nat.mod_eq_of_lt (A.val_lt t)]

abbrev MA : Type := Multiplicative φ.A

abbrev GG : Type := G0 × φ.MA

def hH : φ.MA →* HGrp φ.e where
  toFun a := (φ.h a.toAdd).toMul
  map_one' := by simp
  map_mul' a b := by simp

def iota (t : φ.A) : φ.MA := Multiplicative.ofAdd t

def iotaInv (a : φ.MA) : φ.A := a.toAdd

def sg : φ.GG := ((-1, 1), 1)

def cc : φ.GG := (c0, 1)

def iod : φ.GG := ((1, -1), 1)

def chD : φ.GG →* ℤˣ := (MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)

def chQ : φ.GG →* ℤˣ := (MonoidHom.fst ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)

def chC : φ.GG →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp φ.chD

def Psi : Subgroup φ.GG := φ.chD.ker

theorem mem_Psi_iff {φ : Frame} (g : φ.GG) : g ∈ φ.Psi ↔ g.1.2 = 1 := by
  rw [Frame.Psi, MonoidHom.mem_ker]
  rfl

def placeOf {φ : Frame} (g : φ.GG) : φ.GG := if g.1.2 = 1 then g else φ.cc * g

def tau1 (t : φ.A) : φ.GG := ((1, 1), φ.iota t)

def tau2 (t : φ.A) : φ.GG := ((-1, 1), φ.iota t)

def TwoGroup : Prop := ∃ j : ℕ, φ.ord = 2 ^ j

theorem iota_add (s t : φ.A) : φ.iota (s + t) = φ.iota s * φ.iota t := rfl

theorem iota_zero : φ.iota 0 = 1 := rfl

@[simp] theorem iotaInv_iota (t : φ.A) : φ.iotaInv (φ.iota t) = t := rfl

@[simp] theorem iota_iotaInv (a : φ.MA) : φ.iota (φ.iotaInv a) = a := rfl

theorem iota_bijective : Function.Bijective φ.iota := by
  exact Multiplicative.ofAdd.bijective

theorem natCard_GG : Nat.card φ.GG = 4 * φ.ord := by
  show Nat.card (G0 × φ.MA) = _
  rw [Nat.card_prod]
  have h0 : Nat.card G0 = 4 := by
    show Nat.card (ℤˣ × ℤˣ) = 4
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h2 : Nat.card φ.MA = φ.ord := φ.natCard_A
  rw [h0, h2]

end Frame

end Formalism.HC

end
