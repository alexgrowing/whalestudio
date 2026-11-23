import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Block31OfBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

namespace MassDataIdxStIm

open Matrix
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.L2.SG.TypedSets

variable {A : Type} [CommRing A] {r k : ℕ}

def parGEquiv {P : Matrix (Fin k) (Fin k) A → Prop} (hP : GP P) :
    parG (r := r) hP ≃ {x : Matrix (Idx r k) (Idx r k) A // Par P x} where
  toFun g := ⟨(g : GL (Idx r k) A), g.2⟩
  invFun x := ⟨Matrix.GeneralLinearGroup.mk'' x.1 (par_det hP x.2), x.2⟩
  left_inv g := by ext; rfl
  right_inv x := rfl

abbrev nuG (A : Type) [CommRing A] (r k : ℕ) : Subgroup (GL (Idx r k) A) := parG (r := r) (gpUni (A := A) (k := k))

abbrev sG (A : Type) [CommRing A] (r k : ℕ) : Subgroup (GL (Idx r k) A) := parG (r := r) (gpUnit (A := A) (k := k))

theorem card_nuG (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card (nuG K r k) = Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} * Nat.card (upUniG K k) := by
  have hdet : ∀ u : Matrix (Fin k) (Fin k) K, IsUpUni u → IsUnit u.det := by
    intro u hu
    rw [Matrix.det_of_upperTriangular hu.1]
    simp [hu.2]
  have hU : Nat.card (upUniG K k) = Nat.card {u : Matrix (Fin k) (Fin k) K // IsUpUni u} :=
    Nat.card_congr
      { toFun := fun g => ⟨(g : GL (Fin k) K), g.2⟩
        invFun := fun u => ⟨Matrix.GeneralLinearGroup.mk'' u.1 (hdet u.1 u.2), u.2⟩
        left_inv := fun g => by ext; rfl
        right_inv := fun u => rfl }
  have hN : ∀ x : Matrix (Idx r k) (Idx r k) K,
      IsN x ↔ Par (fun h : Matrix (Fin k) (Fin k) K => h = 1) x := by
    intro x
    unfold IsN Par
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h4, h5, h6, 1, rfl, by rw [h3, midEmb_one]⟩
    · rintro ⟨h1, h2, h4, h5, h6, h, rfl, h3⟩
      exact ⟨h1, h2, by rw [h3, midEmb_one], h4, h5, h6⟩
  have hcN : Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hN), card_par]
    simp
  calc Nat.card (nuG K r k)
      = Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par IsUpUni x} :=
        Nat.card_congr (parGEquiv (r := r) (gpUni (A := K) (k := k)))
    _ = _ := by rw [card_par, hcN, hU, mul_comm]

theorem card_sG (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card (sG K r k) = Nat.card (GL (Fin k) K) * Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} := by
  have hG : Nat.card (GL (Fin k) K) = Nat.card {h : Matrix (Fin k) (Fin k) K // IsUnit h.det} :=
    Nat.card_congr
      { toFun := fun g => ⟨(g : Matrix (Fin k) (Fin k) K),
          (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit g)⟩
        invFun := fun h => Matrix.GeneralLinearGroup.mk'' h.1 h.2
        left_inv := fun g => by ext; rfl
        right_inv := fun h => rfl }
  have hN : ∀ x : Matrix (Idx r k) (Idx r k) K,
      IsN x ↔ Par (fun h : Matrix (Fin k) (Fin k) K => h = 1) x := by
    intro x
    unfold IsN Par
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h4, h5, h6, 1, rfl, by rw [h3, midEmb_one]⟩
    · rintro ⟨h1, h2, h4, h5, h6, h, rfl, h3⟩
      exact ⟨h1, h2, by rw [h3, midEmb_one], h4, h5, h6⟩
  have hcN : Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hN), card_par]
    simp
  calc Nat.card (sG K r k)
      = Nat.card {x : Matrix (Idx r k) (Idx r k) K // Par (fun h => IsUnit h.det) x} :=
        Nat.card_congr (parGEquiv (r := r) (gpUnit (A := K) (k := k)))
    _ = _ := by rw [card_par, hcN, hG]

theorem card_nuG_zmod (g : ℕ) [Fact g.Prime] (r k : ℕ) :
    Nat.card (nuG (ZMod g) r k) = nnC r k g * ukC k g := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  exact card_nuG (ZMod g) r k

theorem card_sG_zmod (g : ℕ) [Fact g.Prime] (r k : ℕ) :
    Nat.card (sG (ZMod g) r k) = glkC k g * nnC r k g := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  exact card_sG (ZMod g) r k

end MassDataIdxStIm
