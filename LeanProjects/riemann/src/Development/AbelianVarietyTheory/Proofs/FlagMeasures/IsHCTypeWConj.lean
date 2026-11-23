import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def cc (a : V) : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  WithLp.toLp 2 fun i => star ((stdOrthonormalBasis ℂ V).repr a i)

def ccInv (x : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) : V :=
  (stdOrthonormalBasis ℂ V).repr.symm (WithLp.toLp 2 fun i => star (x i))

theorem cc_apply (a : V) (i) : cc a i = star ((stdOrthonormalBasis ℂ V).repr a i) := rfl

theorem ccInv_cc (a : V) : ccInv (cc a) = a := by
  simp [ccInv, cc_apply]

theorem cc_ccInv (x : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) : cc (ccInv x) = x := by
  ext i
  simp [ccInv, cc_apply]

theorem cc_add (a b : V) : cc (a + b) = cc a + cc b := by
  ext i
  simp [cc_apply]

theorem cc_smul (s : ℂ) (a : V) : cc (s • a) = star s • cc a := by
  ext i
  simp [cc_apply]

variable {k : ℕ}

theorem lowK_allPos (lam : Fin k → ℝ) (a : Fin k) :
    Formalism.QuantumDeterminants.lowK (allPos k) lam a = lam a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := by
  have h1 : (Finset.univ.filter fun b : Fin k => a < b) = Finset.Ioi a := by ext b; simp
  have h2 : (Finset.univ.filter fun b : Fin k => b < a) = Finset.Iio a := by ext b; simp
  have h3 : (a : ℕ) + 1 ≤ k := a.2
  simp only [allPos, Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.sub_apply, Pi.add_apply, ne_eq, not_true_eq_false,
    and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [show k - 1 - (a : ℕ) = k - ((a : ℕ) + 1) by omega, Nat.cast_sub h3]
  push_cast; ring

theorem lowK_neg_rev (u : Fin k → ℝ) :
    Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) = fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
  funext a
  rw [lowK_allPos, lowK_allPos, Fin.val_rev, Nat.cast_sub a.2]
  push_cast
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

def revM (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := (1 : Matrix (Fin k) (Fin k) ℂ).submatrix Fin.revPerm id

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem ccInv_add (x y : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
    (ccInv (x + y) : V) = ccInv x + ccInv y := by
  rw [← cc_ccInv x, ← cc_ccInv y, ← cc_add, ccInv_cc, ccInv_cc, ccInv_cc]

theorem ccInv_smul (s : ℂ) (x : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
    (ccInv (s • x) : V) = star s • ccInv x := by
  conv_lhs => rw [← cc_ccInv x, ← star_star s, ← cc_smul, ccInv_cc]

def tr (T : V →L[ℂ] V) : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => cc (T (ccInv x))
      map_add' := fun x y => by simp only [ccInv_add, map_add, cc_add]
      map_smul' := fun s x => by simp only [ccInv_smul, map_smul, cc_smul, star_star, RingHom.id_apply] }

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

end GlobalTheory.ConjTypeW
