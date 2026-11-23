import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def Fil (a : ℤ) : Set P.R.BdR := ((P.PD (botExt l)).Fil a : Set P.R.BdR)

def fr (l : ℕ) [Fact l.Prime] (m : ℕ) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l) := ((frobUr l ^ m : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)) : ↥(MaximalUnramifiedExtension l) →+* ↥(MaximalUnramifiedExtension l))

def kd : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (algebraMap (Om l) P.R.BdR).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))

def ks : ↥(MaximalUnramifiedExtension l) →+* Bst P := (Polynomial.C : P.R.B →+* Bst P).comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)

def ev (m : ℕ) (b : P.R.B) : P.R.BdR := P.ιB (P.φB^[m] b)

def tz (a : ℤ) : P.R.BdR := P.ιB (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B)

variable {n : Type} [Fintype n] [DecidableEq n]

def UnitM (U : GL n P.R.BdR) : Prop :=
  (∀ i j, (U : Matrix n n P.R.BdR) i j ∈ Fil P 0) ∧ ∀ i j, ((U⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i j ∈ Fil P 0

variable {K : FinExt l}

structure IsRat (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop where

  pos : 0 < r

  le : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ K.1

  rat : ∀ g i j, fr l r ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j

  cont : ∀ i j, Continuous fun g => (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)

def matD (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) : Matrix n n P.R.BdR :=
  (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map fun c => kd P (fr l m c)

def AdmDR (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∀ m : ℕ, ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K),
    matD P ρ m g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q

def Framed {r : ℕ} (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) : Prop :=
  ∀ m : Fin r, ∃ U : GL n P.R.BdR, UnitM P U ∧ ∀ g : ↥(GK K),
    matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])

def AdmSt (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1) (Q : GL n (Bst P)), ∀ g : ↥(GK K'),
    (ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) *
      (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q

def Splits (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) : Prop :=
  ∃ (s : Finset n) (p : GL n ↥(MaximalUnramifiedExtension l)), s.Nonempty ∧ s ≠ Finset.univ ∧
    (∀ i j, fr l r ((p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = (p : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) ∧
    ∀ g i j, i ∉ s → j ∈ s → ((p⁻¹ * ρ g * p : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = 0

def eps {α : Type} [DecidableEq α] (x y z : α) : ℤ := if z = x then -1 else if z = y then 1 else 0

variable {P} in

def Plus {AI : LocAinf l P} (T : LocTied l P AI) (b : P.R.B) : Prop :=
  ∃ (N : ℕ) (x : Formalism.Per.Acris l), T.eB ((l : P.R.B) ^ N * b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x

end GlobalTheory.PMon

end
