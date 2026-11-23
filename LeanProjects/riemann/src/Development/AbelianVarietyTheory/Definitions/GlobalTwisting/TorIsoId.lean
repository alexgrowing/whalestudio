import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open NumberField

def Stable (K : IntermediateField ℚ ℂ) (L : PeriodPair) : Prop :=
  ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice

def Tor (q : ℕ) (L : PeriodPair) : Set ℂ := {z | ∃ m : ℕ, 0 < m ∧ m.Coprime q ∧ (m : ℂ) * z ∈ L.lattice}

def Maps (μ : ℂ) (L L' : PeriodPair) : Prop := ∀ z ∈ L.lattice, μ * z ∈ L'.lattice

def idx (μ : ℂ) (L L' : PeriodPair) : ℕ :=
  (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft μ)).relIndex L'.lattice.toAddSubgroup

def Incong (L : PeriodPair) (S : Finset ℂ) : Prop := ∀ z ∈ S, ∀ w ∈ S, z - w ∈ L.lattice → z = w

structure TorIso (K : IntermediateField ℚ ℂ) (q : ℕ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop where
  maps : ∀ z ∈ Tor q L, θ z ∈ Tor q L'
  add : ∀ z ∈ Tor q L, ∀ w ∈ Tor q L, θ (z + w) - θ z - θ w ∈ L'.lattice
  ker : ∀ z ∈ Tor q L, θ z ∈ L'.lattice ↔ z ∈ L.lattice
  surj : ∀ w ∈ Tor q L', ∃ z ∈ Tor q L, θ z - w ∈ L'.lattice
  lin : ∀ (a : 𝓞 K), ∀ z ∈ Tor q L, θ (((a : K) : ℂ) * z) - ((a : K) : ℂ) * θ z ∈ L'.lattice

def Cnt (K : IntermediateField ℚ ℂ) (q : ℕ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop :=
  ∀ (μ : ℂ) (β : 𝓞 K), μ ≠ 0 → β ≠ 0 → Maps μ L L' →
    (∀ z ∈ Tor q L, μ * z - θ (((β : K) : ℂ) * z) ∈ L'.lattice) ∨
    (∀ z ∈ Tor q L, μ * z + θ (((β : K) : ℂ) * z) ∈ L'.lattice) ∨
    ∀ S : Finset ℂ, Incong L S → (∀ z ∈ S, z ∈ Tor q L ∧ ((β : K) : ℂ) * z ∉ L.lattice ∧
        (μ * z - θ (((β : K) : ℂ) * z) ∈ L'.lattice ∨ μ * z + θ (((β : K) : ℂ) * z) ∈ L'.lattice)) →
      S.card ≤ 2 * (idx μ L L' + idx ((β : K) : ℂ) L L)

structure Transp (σ : ℂ ≃+* ℂ) (L L' : PeriodPair) (θ : ℂ → ℂ) : Prop where
  g2 : L'.g₂ = σ L.g₂
  g3 : L'.g₃ = σ L.g₃
  add : ∀ z w, θ (z + w) - θ z - θ w ∈ L'.lattice
  ker : ∀ z, θ z ∈ L'.lattice ↔ z ∈ L.lattice
  surj : ∀ w, ∃ z, θ z - w ∈ L'.lattice
  wp : ∀ z, z ∉ L.lattice → L'.weierstrassP (θ z) = σ (L.weierstrassP z)
  wp' : ∀ z, z ∉ L.lattice → L'.derivWeierstrassP (θ z) = σ (L.derivWeierstrassP z)

def Good (W : ValuationSubring ℂ) (L : PeriodPair) : Prop :=
  L.g₂ ∈ W ∧ L.g₃ ∈ W ∧ (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W

def web (L : PeriodPair) (z : ℂ) : ℂ := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP z

def jj (L : PeriodPair) : ℂ := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

def allWeber (K : IntermediateField ℚ ℂ) (n : ℕ) : Set ℂ :=
  {w | ∃ L : PeriodPair, Stable K L ∧ w ∈ GlobalTheory.FieldSize.weberSet L n}

theorem torIso_id (K : IntermediateField ℚ ℂ) (q : ℕ) (L : PeriodPair) : TorIso K q L L id where
  maps := fun _ h => h
  add := fun z _ w _ => by simp
  ker := fun _ _ => Iff.rfl
  surj := fun w h => ⟨w, h, by simp⟩
  lin := fun a z _ => by simp

theorem transp_id (L : PeriodPair) : Transp (RingEquiv.refl ℂ) L L id where
  g2 := rfl
  g3 := rfl
  add := fun z w => by simp
  ker := fun _ => Iff.rfl
  surj := fun w => ⟨w, by simp⟩
  wp := fun _ _ => rfl
  wp' := fun _ _ => rfl

end GlobalTheory.CMRam
