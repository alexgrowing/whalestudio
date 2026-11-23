import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

def dimL (j : ℤ × ℤ) : ℕ :=
  if j = wAl ∨ j = wBe ∨ j = wPs ∨ j = wTh ∨ j = 0 then 2 else if j ∈ wts then 1 else 0

def dimP (j : ℤ × ℤ) : ℕ := if j = 0 then 2 else if j ∈ wts then 1 else 0

namespace Raw

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

section

variable {R : Type} [CommRing R] [Algebra c.O R]

def eqL (ρ : D.Gp l →* M4 R) : Prop :=
  (∀ g : D.Gp l, IsGSp (algebraMap c.O R (D.th g)) (ρ g)) ∧
    Ord ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O R (D.ps i g)) D.s0 ρ

def eqP (p : ℕ) (ρ : D.Gp p →* M4 R) : Prop :=
  (∀ g : D.Gp p, IsGSp (algebraMap c.O R (D.th g)) (ρ g)) ∧ ∀ g : D.Gp p, (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker → ρ g = 1

structure Near (v : ℕ) [Algebra ℚ_[l] R] (ρ : D.Gp v →* M4 R) : Prop where
  cont : ∀ i j, Loc.QCont l fun g => ρ g i j
  red : ∀ (g : D.Gp v) i j, IsNilpotent (ρ g i j - algebraMap c.O R (D.r0 g i j))

end

abbrev LocEq (v : ℕ) : Type 1 := ∀ (R : Type) [CommRing R] [Algebra c.O R], (D.Gp v →* M4 R) → Prop

def tanSet (v : ℕ) (P : D.LocEq v) (w : ℤ × ℤ) : Set (D.Gp v → M4 c.O) :=
  {z | (∀ g, z g ∈ spW c.O w) ∧ (∀ i j, AdicCont (maximalIdeal c.O) fun g => z g i j) ∧
    ∃ ρ : D.Gp v →* M4 (DualNumber c.O), P _ ρ ∧
      ∀ (g : D.Gp v) i j, (ρ g i j).fst = D.r0 g i j ∧ (ρ g i j).snd = (z g * D.r0 g) i j}

def IsArt (c : Coef l) (B : Type) [CommRing B] [Algebra c.O B] : Prop :=
  Nontrivial B ∧ ∀ b : B, ∃ a a' : c.O, a' ≠ 0 ∧ IsNilpotent (a' • b - algebraMap c.O B a)

def Liftable (v : ℕ) (P : D.LocEq v) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra c.O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] c.O B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra c.O B'] [Algebra ℤ_[l] B']
    [IsScalarTower ℤ_[l] c.O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'], IsArt c B → IsArt c B' →
    ∀ p : B →ₐ[c.O] B', Function.Surjective p → ∀ ρ' : D.Gp v →* M4 B', D.Near v ρ' → P B' ρ' →
      ∃ ρ : D.Gp v →* M4 B, D.Near v ρ ∧ P B ρ ∧ mapRep (p : B →+* B') ρ = ρ'

def TanRank (v : ℕ) (P : D.LocEq v) (n : ℤ × ℤ → ℕ) : Prop :=
  ∀ w, Module.Finite c.O (Submodule.span c.O (D.tanSet v P w)) ∧ Module.finrank c.O (Submodule.span c.O (D.tanSet v P w)) = n w

end Raw

end UpperTheory.V.GradeZeroInterpolatingElement

end
