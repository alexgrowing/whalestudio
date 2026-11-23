import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Fin n × Fin n

abbrev Ix (n : ℕ) : Type := Bool × Pos n

abbrev Cr (n : ℕ) (V : Type) : Type := Finset (Ix n) → V

def keyR (i : Ix n) : ℕ := (if i.1 then n * n else 0) + CompanionTheory.D.LK.key i.2

def sgR (i : Ix n) (A : Finset (Ix n)) : ℂ := (-1) ^ (A.filter fun j => keyR j < keyR i).card

def cp (p q r : Pos n) : ℂ :=
  (if p.1.2 = q.1.1 ∧ r.1 = (p.1.1, q.1.2) then 1 else 0) - (if q.1.2 = p.1.1 ∧ r.1 = (q.1.1, p.1.2) then 1 else 0)

def cst (i j k : Ix n) : ℂ := if k.1 = (i.1 && j.1) then cp i.2 j.2 k.2 else 0

def dl (c : Fin n) (p : Pos n) : ℂ := (if p.1.1 = c then 1 else 0) - (if p.1.2 = c then 1 else 0)

def dA (s : Bool) (c : Fin n) (i k : Ix n) : ℂ :=
  if i.2 = k.2 then
    (if s then (if i.1 then (if k.1 then dl c i.2 else -dl c i.2) else 0)
      else (if k.1 then 0 else dl c i.2))
  else 0

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def annR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then 0 else sgR i A • x (insert i A)
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def creR (i : Ix n) : Module.End ℂ (Cr n V) where
  toFun x := fun A => if i ∈ A then sgR i A • x (A.erase i) else 0
  map_add' x y := by funext A; by_cases h : i ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : i ∈ A <;> simp [h, smul_comm c]

def liftR (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cr n V →ₗ[ℂ] Cr n V' :=
  T.compLeft (Finset (Ix n))

def rl (E1 E2 : Fin n → Fin n → Module.End ℂ V) (i : Ix n) : Module.End ℂ V :=
  if i.1 then E1 i.2.1.1 i.2.1.2 + E2 i.2.1.1 i.2.1.2 else E2 i.2.1.1 i.2.1.2

def bdR (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cr n V) :=
  (∑ i : Ix n, (liftR n (rl E1 E2 i) : Module.End ℂ (Cr n V)) * annR i) +
    (1 / 2 : ℂ) • ∑ i : Ix n, ∑ j : Ix n, ∑ k : Ix n, cst i j k • (creR k * annR j * annR i)

def trR (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (c : Fin n) : Module.End ℂ (Cr n V) :=
  (liftR n (if s then E1 c c else E2 c c) : Module.End ℂ (Cr n V)) +
    ∑ i : Ix n, ∑ k : Ix n, dA s c i k • (creR k * annR i)

def torEv (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Bool × Fin n) →ₐ[ℂ] Module.End ℂ (Cr n V) :=
  FreeAlgebra.lift ℂ fun p => trR E1 E2 p.1 p.2

def torV (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Bool × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2 p.2 else E2 p.2 p.2

def ev2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Lt n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then E1 p.2.1 p.2.2 else E2 p.2.1 p.2.2

structure Pair2 (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b

def rV (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V := ⨆ i : Ix n, LinearMap.range (rl E1 E2 i)

end Chains

def omR (n : ℕ) : Finset (Ix n) := univ.filter fun i => i.1 = true

def Inv2 (a : FreeAlgebra ℂ (Lt n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∀ c d, Commute (E1 c d + E2 c d) (ev2 E1 E2 a)

def cval (lam : Fin n → ℤ) : FreeAlgebra ℂ (Bool × Fin n) →ₐ[ℂ] ℂ :=
  FreeAlgebra.lift ℂ fun p => (((lam p.2 : ℝ) + 2 * rhoV n p.2 : ℝ) : ℂ)

def levB (n : ℕ) : Fin n → ℕ := fun a => (a : ℕ)

def DegR {V : Type} [AddCommGroup V] [Module ℂ V] (j : ℕ) (x : Cr n V) : Prop := ∀ A, x A ≠ 0 → A.card = j

def SuppR {V : Type} [AddCommGroup V] [Module ℂ V] (S : Ix n → Prop) (x : Cr n V) : Prop := ∀ A, x A ≠ 0 → ∀ i ∈ A, S i

def BdSqR : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    bdR E1 E2 * bdR E1 E2 = 0

def TorComm : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∀ s c, Commute (trR E1 E2 s c) (bdR E1 E2) ∧ ∀ s' c', Commute (trR E1 E2 s c) (trR E1 E2 s' c')

def CoverR : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (F1 F2 : Fin n → Fin n → Module.End ℂ Y) (π : Y →ₗ[ℂ] V),
      Pair2 F1 F2 ∧ Function.Surjective π ∧ (∀ a b y, π (F1 a b y) = E1 a b (π y)) ∧
      (∀ a b y, π (F2 a b y) = E2 a b (π y)) ∧
      ∀ (j : ℕ) (x : Cr n Y), DegR (j + 1) x → bdR F1 F2 x = 0 → ∃ t : Cr n Y, DegR (j + 2) t ∧ bdR F1 F2 t = x

def COGen : Prop :=
  ∀ (n : ℕ) (a : FreeAlgebra ℂ (Lt n)) (b : FreeAlgebra ℂ (Bool × Fin n)) (S : Ix n → Prop),
    (∀ i j k, S i → S j → cst i j k ≠ 0 → S k) →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
      (∀ i, S i → Commute (rl E1 E2 i) (ev2 E1 E2 a)) ∧ ∀ x : V, ev2 E1 E2 a x - torV E1 E2 b x ∈ rV E1 E2) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
      ∀ (j : ℕ) (x : Cr n V), DegR j x → SuppR S x → bdR E1 E2 x = 0 →
        ∃ w : Cr n V, DegR (j + 1) w ∧ liftR n (ev2 E1 E2 a) x - torEv E1 E2 b x = bdR E1 E2 w

def HCR : Prop :=
  ∀ (n : ℕ) (a : FreeAlgebra ℂ (Lt n)), Inv2 a → ∃ b : FreeAlgebra ℂ (Bool × Fin n),
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
      ∀ x : V, ev2 E1 E2 a x - torV E1 E2 b x ∈ rV E1 E2

def DiracK : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ (ν : Fin n → ℝ) (x : V), x ≠ 0 → x ∈ hwSp E1 E2 ν →
      ∃ π : Equiv.Perm (Fin n), 4 * Formalism.REAL.nsq (fun a => (lam a : ℝ) + rhoV n a) ≤
        Formalism.REAL.nsq (ν - rhoV n + rhoV n ∘ π)

def NumShort : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), StrictAnti lam → ∀ ν : Fin n → ℝ, IsSecondTypeWeight lam (levB n) ν → ∀ π : Equiv.Perm (Fin n),
    Formalism.REAL.nsq (ν - rhoV n + rhoV n ∘ π) < 4 * Formalism.REAL.nsq (fun a => (lam a : ℝ) + rhoV n a)

def LiftInv : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Pair2 E1 E2 → (∀ a b (x y : V), inner ℂ (kF E1 E2 a b x) y = inner ℂ x (kF E1 E2 b a y)) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S) →
    ∀ (μ : Fin n → ℝ) (v w : V), v ≠ 0 → v ∈ hwSp E1 E2 μ → w ∈ hwSp E1 E2 μ → (∃ x ∈ alg E1 E2, x v = w) →
      ∃ a : FreeAlgebra ℂ (Lt n), Inv2 a ∧ ev2 E1 E2 a v = w

def COTop : Prop :=
  ∀ (n : ℕ) (a : FreeAlgebra ℂ (Lt n)), Inv2 a → ∃ b : FreeAlgebra ℂ (Bool × Fin n),
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
      ∀ v : V, (∀ p : Pos n, (E1 p.1.1 p.1.2 + E2 p.1.1 p.1.2) v = 0) →
        ∃ w : Cr n V, liftR n (ev2 E1 E2 a) (Pi.single (omR n) v) - torEv E1 E2 b (Pi.single (omR n) v) = bdR E1 E2 w

def ScalTop : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), StrictAnti lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), AdmFor lam (levB n) E1 E2 → ∀ v ∈ hwSp E1 E2 (m0 lam),
      ∀ b : FreeAlgebra ℂ (Bool × Fin n), ∃ w : Cr n V,
        torEv E1 E2 b (Pi.single (omR n) v) - cval lam b • (Pi.single (omR n) v : Cr n V) = bdR E1 E2 w

def VanKostant : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), StrictAnti lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), AdmFor lam (levB n) E1 E2 → ∀ (B : Finset (Pos n)) (j : ℕ)
      (z : CompanionTheory.D.LK.Cn n V), B.Nonempty → CompanionTheory.D.LK.Sup (CompanionTheory.D.LK.allT n) ∅ j z →
      CompanionTheory.D.LK.Wt (CompanionTheory.D.LK.allT n) (kF E1 E2) (m0 lam + (2 : ℝ) • rhoV n - CompanionTheory.D.LK.wt B) z →
      CompanionTheory.D.LK.bd (CompanionTheory.D.LK.allT n) (kF E1 E2) z = 0 →
      ∃ t : CompanionTheory.D.LK.Cn n V, CompanionTheory.D.LK.Sup (CompanionTheory.D.LK.allT n) ∅ (j + 1) t ∧
        CompanionTheory.D.LK.Wt (CompanionTheory.D.LK.allT n) (kF E1 E2) (m0 lam + (2 : ℝ) • rhoV n - CompanionTheory.D.LK.wt B) t ∧
        CompanionTheory.D.LK.bd (CompanionTheory.D.LK.allT n) (kF E1 E2) t = z

def InjTop : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), StrictAnti lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), AdmFor lam (levB n) E1 E2 → ∀ u ∈ hwSp E1 E2 (m0 lam),
      ∀ w : Cr n V, (Pi.single (omR n) u : Cr n V) = bdR E1 E2 w → u = 0

end GlobalTheory.CompanionTheory.RealMult
