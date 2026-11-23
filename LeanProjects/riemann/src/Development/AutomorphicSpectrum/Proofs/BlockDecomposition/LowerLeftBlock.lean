import Mathlib

noncomputable section

open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

abbrev Ix (n : ℕ) : Type := Fin n ⊕ Fin n

variable {n : ℕ}

section Ring

variable {R : Type} [CommRing R]

def nU (y : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks 1 y 0 1
  inv := fromBlocks 1 (-y) 0 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

def pM (a d : GL (Fin n) R) (b : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks a.1 b 0 d.1
  inv := fromBlocks (a⁻¹).1 (-((a⁻¹).1 * b * (d⁻¹).1)) 0 (d⁻¹).1
  val_inv := by
    simp [fromBlocks_multiply, ← fromBlocks_one, ← Matrix.mul_assoc]
  inv_val := by
    simp [fromBlocks_multiply, ← fromBlocks_one, Matrix.mul_assoc]

def lowerLeftBlock (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₁

def dBlk (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₂

end Ring

def iD {k : Type} [Field k] (g : GL (Ix n) k) : ℕ := n - (dBlk g).rank

section Local

variable {O : Type} [CommRing O] [IsLocalRing O] {L : Type} [Field L] [Algebra O L]

abbrev inL : GL (Ix n) O →* GL (Ix n) L := Matrix.GeneralLinearGroup.map (algebraMap O L)

abbrev resK : GL (Ix n) O →* GL (Ix n) (IsLocalRing.ResidueField O) :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue O)

def scM (w : Lˣ) : GL (Fin n) L := Units.map (Matrix.scalar (Fin n) : L →+* Matrix (Fin n) (Fin n) L).toMonoidHom w

def tauM (w : Lˣ) : GL (Ix n) L := pM 1 (scM w) 0

def IsHgt (nv : Lˣ →* ℝ≥0) (h : GL (Ix n) L → ℝ≥0) : Prop :=
  ∀ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
    h (pM a d b * inL κ) = nv (Matrix.GeneralLinearGroup.det a) / nv (Matrix.GeneralLinearGroup.det d)

def NvOK [Fintype (IsLocalRing.ResidueField O)] (nv : Lˣ →* ℝ≥0) (w : Lˣ) : Prop :=
  (∀ u : Oˣ, nv (Units.map (algebraMap O L).toMonoidHom u) = 1) ∧
    nv w = ((Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0))⁻¹

def IsRed (w : Lˣ) (κ : GL (Ix n) O) (hb : GL (Ix n) (IsLocalRing.ResidueField O)) : Prop :=
  ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ' : GL (Ix n) O),
    inL κ * tauM w = pM a d b * inL κ' ∧ resK κ' = hb

def Gam2 (ϖ : O) : Subgroup (GL (Ix n) O) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))).ker

instance (ϖ : O) : (Gam2 (n := n) ϖ).Normal := by unfold Gam2; infer_instance

def avgK (ϖ : O) (φ : GL (Ix n) O → ℂ) : ℂ :=
  (Nat.card (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) : ℂ)⁻¹ * ∑ᶠ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ, φ (Quotient.out u)

def liftM (ℓ : IsLocalRing.ResidueField O → O) (Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) :
    Matrix (Fin n) (Fin n) L := (Y.map ℓ).map (algebraMap O L)

end Local

def coY {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (β Y : Matrix (Fin n) (Fin n) k) : ℂ :=
  ((Fintype.card k : ℂ) ^ (n * n))⁻¹ * (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β)))

end GlobalTheory.CompanionTheory.Jp

end
