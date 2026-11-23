import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

namespace UpperTheory.V.U3

open Matrix

section Shape

variable {G : Type*} [Group G] {R : Type*} [CommRing R]

def HasMult {m : ℕ} (η : G →* ℤˣ) (r : G →* GG m R) : Prop := ∀ g, (r g).right = η g

def zeta (c g₁ : G) (r : G →* GG 3 R) : R := zmat c g₁ r 0 0

def MatIrr {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ W : Submodule R (Fin m → R), (∀ g ∈ H, ∀ v ∈ W, a g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

def mats {m : ℕ} (r : G →* GG m R) (g : G) : Matrix (Fin m) (Fin m) R := (r g).mat

def TypeI (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := MatIrr η.ker (mats r)

def Upper (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := ∀ g ∈ η.ker, ∀ a b, wt a b < 0 → (r g).mat a b = 0

def Lower (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := ∀ g ∈ η.ker, ∀ a b, 0 < wt a b → (r g).mat a b = 0

def Block (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := ∀ g ∈ η.ker, ∀ a b, Odd (wt a b) → (r g).mat a b = 0

def corner (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 2) R := X.submatrix ![0, 2] ![0, 2]

def TypeII (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop :=
  Block η r ∧ MatIrr η.ker fun g => corner (r g).mat

def Wfun (r : G →* GG 3 R) (g : G) : Matrix (Fin 2) (Fin 2) R :=
  if (r g).right = 1 then corner (r g).mat else corner (r g).mat * Matrix.diagonal ![-1, 1]

def MatIso {m : ℕ} (H : Subgroup G) (a a' : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∃ M : GL (Fin m) R, ∀ g ∈ H, (M : Matrix (Fin m) (Fin m) R) * a g = a' g * M

end Shape

section Deform

variable {G : Type*} [Group G] {C : Type*} [CommRing C] {m : ℕ}

def IsCoc (r : G →* GG m C) (γ : G → Matrix (Fin m) (Fin m) C) : Prop :=
  ∀ g h, γ (g * h) = γ g + adRep r g (γ h)

def EntIn (I : Ideal C) (X : Matrix (Fin m) (Fin m) C) : Prop := ∀ a b, X a b ∈ I

def IsDeform (r : G →* GG m C) (γ : G → Matrix (Fin m) (Fin m) C) (r' : G →* GG m C) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ (r' g).mat = (1 + γ g) * (r g).mat

def zvar (c g₁ : G) (r : G →* GG 3 C) (γ : G → Matrix (Fin 3) (Fin 3) C) : Matrix (Fin 3) (Fin 3) C :=
  γ g₁ * (r g₁).mat - γ (gstar c g₁) * (r (gstar c g₁)).mat

structure NormCoc (c g₁ : G) (r : G →* GG 3 C) (γ : G → Matrix (Fin 3) (Fin 3) C) : Prop where
  atc : γ c = 0
  z12 : zvar c g₁ r γ 0 1 = 0
  z21 : zvar c g₁ r γ 1 0 = 0

def cob (r : G →* GG m C) (X : Matrix (Fin m) (Fin m) C) (g : G) : Matrix (Fin m) (Fin m) C :=
  X - adRep r g X

def CongOne (I : Ideal C) (h : GL (Fin m) C) : Prop := EntIn I ((h : Matrix (Fin m) (Fin m) C) - 1)

end Deform

structure Marks {G : Type*} [Group G] {k : Type*} [CommRing k] (η : G →* ℤˣ) (Ψ : G →* kˣ) (c g₁ : G) : Prop where
  csq : c * c = 1
  ηc : η c = -1
  Ψc : Ψ c = 1
  ηg : η g₁ = 1
  Ψg : IsUnit (((Ψ g₁ : kˣ) : k) ^ 2 - 1)

theorem hasSimilitudeFactor_diagonalRepr {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) :
    HasMult η (r0 η Ψ) := fun _ => rfl

theorem baseRepGL3_normalised_of_psi_eq_one {G : Type*} [Group G] {R : Type*} [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ)
    {c : G} (g₁ : G) (hc : Ψ c = 1) : Normalised c g₁ (r0 η Ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · show Matrix.diagonal (fun i => ((Ψ c ^ wt1 i : Rˣ) : R)) = 1
    rw [hc]
    simp
  · show Matrix.diagonal _ 0 1 - Matrix.diagonal _ 0 1 = (0 : R)
    simp
  · show Matrix.diagonal _ 1 0 - Matrix.diagonal _ 1 0 = (0 : R)
    simp

example : Marks (G := ℤˣ × ℚˣ) (k := ℚ) (MonoidHom.fst _ _) (MonoidHom.snd _ _) (-1, 1)
    (1, Units.mk0 2 two_ne_zero) :=
  ⟨by simp, rfl, rfl, rfl, by norm_num⟩

end UpperTheory.V.U3
