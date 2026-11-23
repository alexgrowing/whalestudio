import Mathlib

open scoped Classical BigOperators
open IsLocalRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeFlatSpecialisation

section Objects

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F]

def IsInt {m n : Type} (x : Matrix m n F) : Prop :=
  ∀ i j, x i j ∈ Set.range (algebraMap O F)

def red {m n : Type} (x : Matrix m n F) : Matrix m n (ResidueField O) :=
  fun i j => Function.extend (algebraMap O F) (residue O) 0 (x i j)

def toF (F : Type) [Field F] [Algebra O F] {m : ℕ} (g : GL (Fin m) O) :
    Matrix (Fin m) (Fin m) F :=
  (g : Matrix (Fin m) (Fin m) O).map (algebraMap O F)

def detBar {m : ℕ} (g : GL (Fin m) O) : (ResidueField O)ˣ :=
  Units.map (residue O).toMonoidHom (Matrix.GeneralLinearGroup.det g)

def rowSpan {r n : ℕ} (x : Matrix (Fin r) (Fin n) F) :
    Submodule (ResidueField O) (Fin n → ResidueField O) :=
  Submodule.span (ResidueField O) (Set.range fun i => red O x i)

def rk {r n : ℕ} (x : Matrix (Fin r) (Fin n) F) : ℕ :=
  Module.finrank (ResidueField O) (rowSpan O x)

def phiLat {r n : ℕ} (x : Matrix (Fin r) (Fin n) F) : ℤ :=
  if IsInt O x then 1 else 0

def phiPrim {r n : ℕ} (x : Matrix (Fin r) (Fin n) F) : ℤ :=
  if IsInt O x ∧ rk O x = r then 1 else 0

def maxCompact (F : Type) [Field F] [Algebra O F] (r : ℕ) : Subgroup (GL (Fin r) F) :=
  (Matrix.GeneralLinearGroup.map (n := Fin r) (algebraMap O F)).range

def heckeDiag (F : Type) [Field F] [Algebra O F] (ϖ : O) (r j : ℕ) :
    Matrix (Fin r) (Fin r) F :=
  Matrix.diagonal fun i => if (i : ℕ) < j then algebraMap O F ϖ else 1

def heckeCosets (F : Type) [Field F] [Algebra O F] (ϖ : O) (r j : ℕ) :
    Set (GL (Fin r) F ⧸ maxCompact O F r) :=
  {c | ∃ g : GL (Fin r) F, (g : GL (Fin r) F ⧸ maxCompact O F r) = c ∧
    ∃ k₁ k₂ : GL (Fin r) O,
      (g : Matrix (Fin r) (Fin r) F) = toF O F k₁ * heckeDiag O F ϖ r j * toF O F k₂}

def heckeT (ϖ : O) {r n : ℕ} (j : ℕ) (φ : Matrix (Fin r) (Fin n) F → ℤ)
    (x : Matrix (Fin r) (Fin n) F) : ℤ :=
  ∑ᶠ c ∈ heckeCosets O F ϖ r j,
    φ ((((Quotient.out c : GL (Fin r) F)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * x)

def resCard : ℕ := Nat.card (ResidueField O)

def Hecke₃ (ϖ : O) {r n : ℕ} (Y : ℤ) (φ : Matrix (Fin r) (Fin n) F → ℤ)
    (x : Matrix (Fin r) (Fin n) F) : ℤ :=
  ∑ j ∈ Finset.range (r + 1),
    (-1) ^ j * (resCard O : ℤ) ^ (j * (j - 1) / 2) * heckeT O ϖ j φ x * Y ^ j

def blockL {A : Type} {r t : ℕ} (u : Matrix (Fin r) (Fin (r + t)) A) : Matrix (Fin r) (Fin r) A :=
  u.submatrix id (Fin.castAdd t)

def blockR {A : Type} {r t : ℕ} (u : Matrix (Fin r) (Fin (r + t)) A) : Matrix (Fin r) (Fin t) A :=
  u.submatrix id (Fin.natAdd r)

def IsFlat {r t : ℕ} (u : Matrix (Fin r) (Fin (r + t)) F) : Prop :=
  (∃ g : GL (Fin r) O, toF O F g = blockL u) ∧ IsInt O (blockR u)

def phiFlat {r t : ℕ} (u : Matrix (Fin r) (Fin (r + t)) F) : ℤ :=
  if IsFlat O u then 1 else 0

def phiFlatChar {R : Type} [CommRing R] (ψ : (ResidueField O)ˣ →* Rˣ) (ε : ℤˣ) {r t : ℕ}
    (u : Matrix (Fin r) (Fin (r + t)) F) : R :=
  if h : IsFlat O u then ((ψ (detBar O h.1.choose) ^ (ε : ℤ) : Rˣ) : R) else 0

def Grass (r t : ℕ) : Type :=
  {U : Submodule (ResidueField O) (Fin (r + t) → ResidueField O) //
    Module.finrank (ResidueField O) U = t}

instance [Finite (ResidueField O)] (r t : ℕ) : Finite (Grass O r t) := by
  haveI : Finite (Submodule (ResidueField O) (Fin (r + t) → ResidueField O)) :=
    Finite.of_injective _ SetLike.coe_injective
  unfold Grass; infer_instance

instance [Finite (ResidueField O)] (r t : ℕ) : Fintype (Grass O r t) := Fintype.ofFinite _

def phiSub {r t : ℕ} (U : Grass O r t) (x : Matrix (Fin r) (Fin (r + t)) F) : ℤ :=
  if IsInt O x ∧ rowSpan O x ⊔ U.1 = ⊤ then 1 else 0

abbrev DetBases (r t : ℕ) : Type :=
  ∀ U : Grass O r t,
    (⋀[ResidueField O]^r ((Fin (r + t) → ResidueField O) ⧸ U.1)) ≃ₗ[ResidueField O] ResidueField O

def detMod {r t : ℕ} (β : DetBases O r t) (U : Grass O r t)
    (x : Matrix (Fin r) (Fin (r + t)) F) : ResidueField O :=
  β U (exteriorPower.ιMulti (ResidueField O) r fun i => U.1.mkQ (red O x i))

def qPhi [Finite (ResidueField O)] {C : Type} [AddCommGroup C]
    (ω : Additive (ResidueField O)ˣ →+ C) (ε : ℤˣ) {r t : ℕ} (β : DetBases O r t)
    (x : Matrix (Fin r) (Fin (r + t)) F) : AddMonoidAlgebra ℤ C :=
  ∑ U : Grass O r t, phiSub O U x •
    (if h : detMod O β U x = 0 then 0
     else AddMonoidAlgebra.single
       ((ε : ℤ) • ω (Additive.ofMul (Units.mk0 (detMod O β U x) h))) (1 : ℤ))

end Objects

def specialise {C R : Type} [AddCommGroup C] [CommRing R] (ψ : Multiplicative C →* Rˣ) :
    AddMonoidAlgebra ℤ C →+* R :=
  AddMonoidAlgebra.liftNCRingHom (Int.castRingHom R) ((Units.coeHom R).comp ψ)
    (fun _ _ => Commute.all _ _)

def augment (C : Type) [AddCommGroup C] : AddMonoidAlgebra ℤ C →+* ℤ :=
  specialise (1 : Multiplicative C →* ℤˣ)

def charComp {G C R : Type} [CommGroup G] [AddCommGroup C] [CommRing R]
    (ω : Additive G →+ C) (ψ : Multiplicative C →* Rˣ) : G →* Rˣ where
  toFun g := ψ (Multiplicative.ofAdd (ω (Additive.ofMul g)))
  map_one' := by simp
  map_mul' a b := by simp [ofMul_mul, ofAdd_add]

section Statements

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (F : Type) [Field F] [Algebra O F] (r t : ℕ)

def HeckeIdentity : Prop :=
  ∀ ϖ : O, Irreducible ϖ →
    (∀ j ≤ r, (heckeCosets O F ϖ r j).Finite) ∧
    (∀ x : Matrix (Fin r) (Fin (r + t)) F, Hecke₃ O ϖ 1 (phiLat O) x = phiPrim O x) ∧
    (∀ (Y : ℤ) (x : Matrix (Fin r) (Fin (r + t)) F), Hecke₃ O ϖ Y (phiLat O) x =
      phiLat O x * ∏ i ∈ Finset.range (r - rk O x), (1 - (resCard O : ℤ) ^ i * Y))

def IsTranslateFamily (h : Grass O r t → GL (Fin (r + t)) O) : Prop :=
  ∀ (U : Grass O r t) (x : Matrix (Fin r) (Fin (r + t)) F),
    phiSub O U x = phiFlat O (x * toF O F (h U))

def ComplementSum : Prop :=
  (∃ h, IsTranslateFamily O F r t h) ∧
  ∀ x : Matrix (Fin r) (Fin (r + t)) F,
    ∑ U : Grass O r t, phiSub O U x = (resCard O : ℤ) ^ (r * t) * phiPrim O x

def GroupRingDatum : Prop :=
  ∀ β : DetBases O r t,
    (∀ (U : Grass O r t) (x : Matrix (Fin r) (Fin (r + t)) F), IsInt O x →
      (detMod O β U x ≠ 0 ↔ phiSub O U x = 1)) ∧
    ∀ (C : Type) [AddCommGroup C] (ω : Additive (ResidueField O)ˣ →+ C) (ε : ℤˣ),
      (∀ x : Matrix (Fin r) (Fin (r + t)) F, ¬ IsInt O x → qPhi O ω ε β x = 0) ∧
      (∀ x y : Matrix (Fin r) (Fin (r + t)) F, IsInt O x → IsInt O y → red O x = red O y →
        qPhi O ω ε β x = qPhi O ω ε β y) ∧
      (∀ x : Matrix (Fin r) (Fin (r + t)) F,
        augment C (qPhi O ω ε β x) = (resCard O : ℤ) ^ (r * t) * phiPrim O x) ∧
      (∀ (κ : GL (Fin r) O) (x : Matrix (Fin r) (Fin (r + t)) F),
        qPhi O ω ε β (toF O F κ⁻¹ * x) =
          AddMonoidAlgebra.single (-((ε : ℤ) • ω (Additive.ofMul (detBar O κ)))) (1 : ℤ) *
            qPhi O ω ε β x)

def Specialisation : Prop :=
  ∃ h : Grass O r t → GL (Fin (r + t)) O, IsTranslateFamily O F r t h ∧
    ∀ β : DetBases O r t, ∃ c : Grass O r t → (ResidueField O)ˣ,
      (∀ (U : Grass O r t) (x : Matrix (Fin r) (Fin (r + t)) F), IsInt O x →
        detMod O β U x = (c U : ResidueField O) * (red O (blockL (x * toF O F (h U)))).det) ∧
      ∀ (C : Type) [AddCommGroup C] (ω : Additive (ResidueField O)ˣ →+ C) (ε : ℤˣ)
        (R : Type) [CommRing R] (ψ : Multiplicative C →* Rˣ)
        (x : Matrix (Fin r) (Fin (r + t)) F),
        specialise ψ (qPhi O ω ε β x) =
          ∑ U : Grass O r t, ((charComp ω ψ (c U) ^ (ε : ℤ) : Rˣ) : R) *
            phiFlatChar O (charComp ω ψ) ε (x * toF O F (h U))

end Statements

def LocalData : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F] (r t : ℕ),
    HeckeIdentity O F r t ∧ ComplementSum O F r t ∧ GroupRingDatum O F r t ∧
      Specialisation O F r t

section Basic₂

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

example (p : ℕ) [Fact p.Prime] : Finite (ResidueField ℤ_[p]) ∧ IsFractionRing ℤ_[p] ℚ_[p] :=
  ⟨Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv, inferInstance⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeFlatSpecialisation
