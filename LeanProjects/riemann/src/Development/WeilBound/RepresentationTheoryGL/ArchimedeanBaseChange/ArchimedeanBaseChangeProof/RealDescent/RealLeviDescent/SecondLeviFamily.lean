import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsLevPairA
import Formalism.RealPlaceAnalysis.StatementE

noncomputable section

open Finset

namespace PositivityTheory.RgBcC.RealD

open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

def InvKP (n : ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPairA E1 E2 →
    ∀ c d, Commute (kA E1 E2 c d) (evKP E1 E2 a)

def InvLv (lev : Fin n → ℕ) (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (F1 F2 : Fin n → Fin n → Module.End ℂ H), IsLevPairA lev F1 F2 →
    ∀ c d, lev c = lev d → Commute (kA F1 F2 c d) (evLv lev F1 F2 b)

section Ops

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def blk (lev : Fin n → ℕ) (j : ℕ) : Finset (Fin n) := univ.filter fun a => lev a = j

def blkE (lev : Fin n → ℕ) (j : ℕ) : Fin (blk lev j).card → Fin n := fun i => (blk lev j).orderEmbOfFin rfl i

def capS (F : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (j : ℕ) (u : ℂ) : Module.End ℂ V :=
  Formalism.REAL.qminor F (blkE lev j) (blkE lev j) (u + (((blk lev j).card : ℂ) - 1) / 2)

def levs (lev : Fin n → ℕ) : List ℕ := (univ.image lev).sort (· ≤ ·)

def capProd (F : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (σ : ℕ → ℂ) (u : ℂ) : Module.End ℂ V :=
  ((levs lev).map fun j => capS F lev j (u - σ j)).prod

def evCap (lev : Fin n → ℕ) (F : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (ℕ × ℂ) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => capS F lev p.1 p.2

def chU (lev : Fin n → ℕ) (j : ℕ) : Submodule ℂ (Cq n V) where
  carrier := {y | SuppL (inUU lev) y ∧ DegL j y}
  add_mem' {x y} hx hy := ⟨fun A hA l hl => by
      by_cases h : x A = 0
      · exact hy.1 A (by simpa [h] using hA) l hl
      · exact hx.1 A h l hl,
    fun A hA => by
      by_cases h : x A = 0
      · exact hy.2 A (by simpa [h] using hA)
      · exact hx.2 A h⟩
  zero_mem' := ⟨fun A hA => absurd rfl hA, fun A hA => absurd rfl hA⟩
  smul_mem' c x hx := ⟨fun A hA l hl => hx.1 A (fun h => hA (by simp [h])) l hl,
    fun A hA => hx.2 A (fun h => hA (by simp [h]))⟩

def bdSub (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Cq n V) :=
  (chU lev ((omU lev).card + 1)).map (bdL (inUU lev) E1 E2)

def firstLeviFamily (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) + evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)))

def secondLeviFamily (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) - evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)))

end Ops

def Lr (lam : Fin n → ℤ) : Fin n → ℝ := fun a => (lam a : ℝ) + ((n : ℝ) - 1) / 2 - (a : ℕ)

end PositivityTheory.RgBcC.RealD
