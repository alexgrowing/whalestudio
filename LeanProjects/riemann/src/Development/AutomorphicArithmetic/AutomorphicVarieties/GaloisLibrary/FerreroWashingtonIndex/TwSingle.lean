import Mathlib

noncomputable section

namespace UpperTheory.V.FW

def ee (l : ℕ) : ℕ := if l = 2 then 2 else 1

section Padic

variable (l : ℕ) [Fact l.Prime]

def WW : Subgroup ℤ_[l]ˣ := rootsOfUnity (Nat.totient (l ^ ee l)) ℤ_[l]

def redU (n : ℕ) : ℤ_[l]ˣ →* (ZMod (l ^ n))ˣ := Units.map (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)).toMonoidHom

abbrev QQ (n : ℕ) : Type := (ZMod (l ^ n))ˣ ⧸ (WW l).map (redU l n)

def piQ (n : ℕ) {M : ℕ} (h : l ^ n ∣ M) : (ZMod M)ˣ →* QQ l n := (QuotientGroup.mk' _).comp (ZMod.unitsMap h)

end Padic

def tw {k G Q : Type} [CommRing k] [CommGroup G] [CommGroup Q] (χ : G →* kˣ) (π : G →* Q) :
    MonoidAlgebra k G →ₐ[k] MonoidAlgebra k Q :=
  MonoidAlgebra.lift k (MonoidAlgebra k Q) G
    { toFun g := MonoidAlgebra.single (π g) (χ g : k)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' a b := by simp [MonoidAlgebra.single_mul_single] }

theorem tw_single {k G Q : Type} [CommRing k] [CommGroup G] [CommGroup Q] (χ : G →* kˣ) (π : G →* Q) (g : G) (a : k) :
    tw χ π (MonoidAlgebra.single g a) = MonoidAlgebra.single (π g) (a * χ g) := by
  simp [tw]

def toK (k G : Type) [CommRing k] [Monoid G] : MonoidAlgebra ℤ G →+* MonoidAlgebra k G :=
  MonoidAlgebra.mapRingHom G (Int.castRingHom k)

def sinE {k A ι : Type} [CommRing k] [AddCommGroup A] [Fintype ι] [DecidableEq ι] (η : ι → A) (N : ℕ) (P : ℕ → k) :
    AddMonoidAlgebra k A :=
  ∑ i, (∑ s ∈ Finset.range N, AddMonoidAlgebra.single (s • η i) (P s)) *
    ∏ j ∈ Finset.univ.erase i, (1 - AddMonoidAlgebra.single (N • η j) 1)

def gc (M c : ℕ) (s : ZMod M) : ℤ := ((c * ((c : ZMod M)⁻¹ * s).val / M : ℕ) : ℤ) - (((c - 1) / 2 : ℕ) : ℤ)

def thetaH (M c : ℕ) [NeZero M] : MonoidAlgebra ℤ (ZMod M)ˣ :=
  ∑ s ∈ Finset.univ.filter fun s : (ZMod M)ˣ => 2 * (s : ZMod M).val < M, MonoidAlgebra.single s (gc M c s)

def push {k : Type} [AddCommMonoid k] {M : ℕ} [NeZero M] {m : ℕ} (h : m ∣ M) (g : ZMod M → k) (y : ZMod m) : k :=
  ∑ s : ZMod M with ZMod.castHom h (ZMod m) s = y, g s

section Grp

variable {C : Type} [CommGroup C]

variable (C) in

abbrev powR (n : ℕ) : Subgroup C := (powMonoidHom n : C →* C).range

variable (C) in

abbrev torK (n : ℕ) : Subgroup C := (powMonoidHom n : C →* C).ker

abbrev difR (τ : C →* C) : Subgroup C := (MonoidHom.id C / τ).range

abbrev minK (τ : C →* C) : Subgroup C := (τ * MonoidHom.id C).ker

end Grp

def evenF {G : Type} [Group G] (J : G) : AddSubgroup (G → ZMod 2) where
  carrier := {f | ∀ g, f (J * g) = f g}
  zero_mem' _ := rfl
  add_mem' {a b} ha hb g := by simp [ha g, hb g]
  neg_mem' {a} ha g := by simp [ha g]

example : gc 7 3 1 = 1 := by decide +kernel

end UpperTheory.V.FW

end
