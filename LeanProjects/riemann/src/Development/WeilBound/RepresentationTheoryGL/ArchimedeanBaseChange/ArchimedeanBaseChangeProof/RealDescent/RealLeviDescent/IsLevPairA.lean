import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.NoSecondTypeWeight
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP

noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open CompanionTheory.D.LK (Pos key)
open Formalism.REAL (GlRel)

variable {n : ℕ}

abbrev Lt (n : ℕ) : Type := Bool × Pos n

abbrev Cq (n : ℕ) (V : Type) : Type := Finset (Lt n) → V

def keyL (l : Lt n) : ℕ := (if l.1 then n * n else 0) + key l.2

def sgL (l : Lt n) (A : Finset (Lt n)) : ℂ := (-1) ^ (A.filter fun m => keyL m < keyL l).card

def wtL (A : Finset (Lt n)) : Fin n → ℝ := fun c =>
  ((A.filter fun l => l.2.1.1 = c).card : ℝ) - ((A.filter fun l => l.2.1.2 = c).card : ℝ)

abbrev inUU (lev : Fin n → ℕ) (l : Lt n) : Prop := lev l.2.1.1 < lev l.2.1.2

abbrev inRR (lev : Fin n → ℕ) (l : Lt n) : Prop := l.1 = false ∨ lev l.2.1.1 < lev l.2.1.2

abbrev isK (l : Lt n) : Prop := l.1 = false

def omN (n : ℕ) : Finset (Lt n) := univ.filter fun l => l.1 = false

def omU (lev : Fin n → ℕ) : Finset (Lt n) := univ.filter fun l => l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def kA (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ V := fun a b => E1 a b + E2 a b

def pA (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ V := fun a b => E1 a b - E2 a b

def annL (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then 0 else sgL l A • x (insert l A)
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def creL (l : Lt n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => if l ∈ A then sgL l A • x (A.erase l) else 0
  map_add' x y := by funext A; by_cases h : l ∈ A <;> simp [h]
  map_smul' c x := by funext A; by_cases h : l ∈ A <;> simp [h, smul_comm c]

def liftL (n : ℕ) {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') : Cq n V →ₗ[ℂ] Cq n V' :=
  T.compLeft (Finset (Lt n))

def xL (E1 E2 : Fin n → Fin n → Module.End ℂ V) (l : Lt n) : Module.End ℂ V :=
  if l.1 then pA E1 E2 l.2.1.1 l.2.1.2 else kA E1 E2 l.2.1.1 l.2.1.2

open Classical in

def bdL (S : Lt n → Prop) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ l : Lt n, if S l then (liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l else 0) +
    ∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n,
      if S l ∧ S m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
        creL k * annL m * annL l else 0

def FtL (E1 E2 : Fin n → Fin n → Module.End ℂ V) (c : Fin n) : Module.End ℂ (Cq n V) where
  toFun x := fun A => kA E1 E2 c c (x A) + (wtL A c : ℂ) • x A
  map_add' x y := by funext A; simp only [Pi.add_apply, map_add, smul_add]; abel
  map_smul' s x := by funext A; simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, smul_comm s]

def WtL (E1 E2 : Fin n → Fin n → Module.End ℂ V) (τ : Fin n → ℝ) (x : Cq n V) : Prop :=
  ∀ c, FtL E1 E2 c x = (τ c : ℂ) • x

def SuppL (P : Lt n → Prop) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → ∀ l ∈ A, P l

def DegL (j : ℕ) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → A.card = j

def PartL (B : Finset (Lt n)) (y : Cq n V) : Prop := ∀ A, y A ≠ 0 → A.filter (fun l => l.1 = true) = B

def evKP (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if p.1 then pA E1 E2 p.2.1 p.2.2 else kA E1 E2 p.2.1 p.2.2

def evLv (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if lev p.2.1 = lev p.2.2 then (if p.1 then pA E1 E2 p.2.1 p.2.2 else kA E1 E2 p.2.1 p.2.2) else 0

def adCL (s : Bool) (p q : Fin n) (l k : Lt n) : ℂ :=
  (if q = l.2.1.1 ∧ k.1 = xor s l.1 ∧ k.2.1 = (p, l.2.1.2) then 1 else 0) -
    (if l.2.1.2 = p ∧ k.1 = xor s l.1 ∧ k.2.1 = (l.2.1.1, q) then 1 else 0)

def adLL (lev : Fin n → ℕ) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  ∑ l : Lt n, ∑ k : Lt n, if inUU lev l then adCL s p q l k • (creL k * annL l) else 0

def evLc (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (Cq n V) :=
  FreeAlgebra.lift ℂ fun p => if lev p.2.1 = lev p.2.2 then
    ((liftL n (if p.1 then pA E1 E2 p.2.1 p.2.2 else kA E1 E2 p.2.1 p.2.2) : Module.End ℂ (Cq n V)) + adLL lev p.1 p.2.1 p.2.2)
    else 0

end Chains

def IsPairA {V : Type} [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop :=
  GlRel E1 ∧ GlRel E2 ∧ ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b

def IsLevPairA {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (F1 F2 : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b c d, lev a = lev b → lev c = lev d →
    F1 a b * F1 c d - F1 c d * F1 a b = (if b = c then F1 a d else 0) - (if d = a then F1 c b else 0) ∧
    F2 a b * F2 c d - F2 c d * F2 a b = (if b = c then F2 a d else 0) - (if d = a then F2 c b else 0) ∧
    F1 a b * F2 c d = F2 c d * F1 a b

end PositivityTheory.RgBcC.RealD
