import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr
open scoped Pointwise

namespace UpperTheory.V.Fr

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  [CharP (ResidueField O) l]

variable (Ω O) in

abbrev omO : G ℚ Ω →* (ResidueField O)ˣ := GC.cycF ℚ Ω l (ResidueField O)

structure Gen (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)) : Prop where
  odd : l ≠ 2
  fin : Finite (ResidueField O)
  M_ne : M ≠ 0
  l_dvd : l ∣ M
  two_dvd : 2 ∣ M
  cc : IsCC σ
  over_l : B.valuation (l : Ω) < 1
  quad : ∃ (D : ℕ) (δ : Ω), 0 < D ∧ (∀ q : ℕ, q.Prime → q ∣ D → q ∣ M) ∧ δ ^ 2 = -(D : Ω) ∧ ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ
  cyc : ∃ a : ℕ, Af.KillsMu (M ^ a) η ∧ Af.KillsMu (M ^ a) (barChar O Ψ)
  η_l : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → Ine (F := ℚ) B' ≤ η.ker
  even : barChar O Ψ σ = 1
  Ψ_l : ∃ j : ℕ, ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B', barChar O Ψ s = omO Ω l O s ^ j
  g4 : ¬ (omO Ω l O).ker ⊓ (barChar O Ψ).ker ≤ η.ker
  g5 : ∃ s ∈ Dec (F := ℚ) B, η s = 1 ∧ barChar O Ψ s ^ 2 ≠ 1
  Hb_open : IsOpen (Hb : Set (G ℚ Ω))
  Hb_ab : commutator (G ℚ Ω) ≤ Hb
  Hb_idx : ∃ a : ℕ, Hb.index = l ^ a
  Hb_l : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → Ine (F := ℚ) B' ≤ Hb
  teich : ∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B' ⊓ Hb, barChar O Ψ s = 1 → Ψ s = 1

variable (Ω) in

def Hth (w : ℕ) : Subgroup (G ℚ Ω) where
  carrier := {s | ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l} ∩ {s | ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s⁻¹ ζ = ζ ^ a ^ l}
  one_mem' := ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩
  mul_mem' := by
    rintro s t ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    refine ⟨⟨a * b, fun ζ h => ?_⟩, ⟨b' * a', fun ζ h => ?_⟩⟩
    · rw [AlgEquiv.mul_apply, hb ζ h, map_pow, ha ζ h, ← pow_mul, mul_pow]
    · rw [mul_inv_rev, AlgEquiv.mul_apply, ha' ζ h, map_pow, hb' ζ h, ← pow_mul, mul_pow]
  inv_mem' := by
    rintro s ⟨h1, h2⟩
    exact ⟨h2, by show ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s⁻¹⁻¹ ζ = ζ ^ a ^ l; rw [inv_inv]; exact h1⟩

variable (Ω) in

def Hlay (m : ℕ) : Subgroup (G ℚ Ω) := (cycMod ℚ Ω l (m + 1) ^ (l - 1)).ker

structure FrobeniusSplitPrimeDatum (η : G ℚ Ω →* ℤˣ) (M : ℕ) (H₀ : Subgroup (G ℚ Ω)) : Prop where
  isOpen : IsOpen (H₀ : Set (G ℚ Ω))
  idx : H₀.index = 2
  real : ∀ τ : G ℚ Ω, IsCC τ → τ ∈ H₀
  loc : ∀ B' : ValuationSubring Ω, B'.valuation (M : Ω) < 1 → Dec (F := ℚ) B' ⊓ H₀ = Dec (F := ℚ) B' ⊓ η.ker
  ram : ∃ B' : ValuationSubring Ω, ¬ B'.valuation (M : Ω) < 1 ∧ ¬ Ine (F := ℚ) B' ≤ H₀

structure FrobeniusWitnessPrime (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (M w : ℕ) : Prop where
  prime : w.Prime
  cop : ¬ w ∣ M
  one : w ≡ 1 [MOD l]
  split : ∀ B' : ValuationSubring Ω, B'.valuation (w : Ω) < 1 →
    Dec (F := ℚ) B' ≤ η.ker ⊓ (barChar O Ψ).ker ⊓ (omO Ω l O).ker

def Upl (Hb H₀ : Subgroup (G ℚ Ω)) (w m : ℕ) : Subgroup (G ℚ Ω) := H₀ ⊓ Hth Ω l w ⊓ Hb ⊓ Hlay Ω l m

structure UFacts (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (M m : ℕ) (U : Subgroup (G ℚ Ω)) : Prop where
  isOpen : IsOpen (U : Set (G ℚ Ω))
  ab : commutator (G ℚ Ω) ≤ U
  real : ∀ τ : G ℚ Ω, IsCC τ → τ ∈ U
  unr : ∀ B' : ValuationSubring Ω, Ine (F := ℚ) B' ⊓ U ≤ η.ker
  split : ∀ B' : ValuationSubring Ω, B'.valuation (M : Ω) < 1 → Dec (F := ℚ) B' ⊓ U ≤ η.ker
  teich : ∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B' ⊓ U, barChar O Ψ s = 1 → Ψ s = 1
  mu : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∃ s ∈ Ine (F := ℚ) B' ⊓ U, cycMod ℚ Ω l 1 s ≠ 1
  deg : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → l ^ m ≤ U.relIndex (Dec (F := ℚ) B')
  f2b : ∀ j : ℤ, j = 1 ∨ j = -1 → ∃ s ∈ U ⊓ η.ker, omO Ω l O s * barChar O Ψ s ^ j ≠ 1
  f2c : ∀ j : ℤ, j = 2 ∨ j = -2 → ∃ s ∈ U ⊓ η.ker, omO Ω l O s * barChar O Ψ s ^ j ≠ 1
  f3 : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∃ s ∈ Dec (F := ℚ) B' ⊓ U, barChar O Ψ s ^ 2 ≠ 1
  f5 : ¬ ∃ j : ℤ, ∀ s ∈ U ⊓ η.ker, omO Ω l O s = barChar O Ψ s ^ j

abbrev etaO (O : Type) [CommRing O] [IsLocalRing O] (η : G ℚ Ω →* ℤˣ) : G ℚ Ω →* (ResidueField O)ˣ :=
  (Units.map (Int.castRingHom (ResidueField O)).toMonoidHom).comp η

def StrictCl (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (κ : G ℚ Ω →* (ResidueField O)ˣ) (U : Subgroup (G ℚ Ω)) : Prop :=
  ∃ y : G ℚ Ω → ResidueField O, IsLocallyConstant y ∧ (∀ s t, y (s * t) = y s + κ s * y t) ∧
    (¬ ∃ b, ∀ s ∈ U, y s = κ s * b - b) ∧
    (∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∃ b, ∀ s ∈ Dec (F := ℚ) B', y s = κ s * b - b) ∧
    ∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B' ⊓ U, η s = 1 → barChar O Ψ s = 1 → y s = 0

def Linked (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Frame l (ResidueField O)) : Prop :=
  ∃ (k : GalLink η Ψ σ g₁ B M L Φ), ∃ S π ι pl e c, GC.FLink (F := W.Lp L) (Ω := Ω) l Φ S
      ((η.ker ⊓ (barChar O Ψ).ker).comap (galEmb ℚ (W.Lp L) Ω)) π ι k.pl pl e c ∧
      (∀ (g : G (W.Lp L) Ω) (h : galEmb ℚ (W.Lp L) Ω g ∈ upl Ω L), π g = k.p ⟨_, h⟩) ∧
      ∀ v s, galEmb ℚ (W.Lp L) Ω (ι v s) = k.j v s

def HasFrameW (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M Q : ℕ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω) (g₁ : G ℚ Ω)
    (Φ : Frame l (ResidueField O)) (C₀ w : ℕ), Linked l η Ψ σ g₁ B M L Φ ∧ Φ.Ok C₀ ∧ Φ.Big C₀ ∧
      FrobeniusWitnessPrime l η Ψ M w ∧ w ≡ 1 [MOD Q] ∧ upl Ω L ≤ Hth Ω l w

end UpperTheory.V.Fr

end
