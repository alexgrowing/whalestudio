import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import GroundTheory.LocalFields.LocalFourierHaar
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModAbs

theorem ordL_eq_ord {E : Type} [Field E] [NumberField E] (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    ordL x = GroundTheory.LocalField.ord x := by
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord hx
  have hv : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  unfold ordL
  rw [dif_neg hv]
  have : WithZero.unzero hv = Multiplicative.ofAdd (-GroundTheory.LocalField.ord x) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h2]
    rfl
  rw [this, toAdd_ofAdd, neg_neg]

theorem haar_eq_absHalf_sq : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) (hx : x ≠ 0), (((MeasureTheory.distribHaarChar (w.adicCompletion E) (Units.mk0 x hx) : NNReal) : ℝ) : ℂ) = absHalf w x ^ 2 := by
  intro E _ _ w x hx
  have h1 := GroundTheory.LocalField.distribHaarChar_eq_modulus (K := w.adicCompletion E) (Units.mk0 x hx)
  have h3 : (GroundTheory.LocalField.residueCard (w.adicCompletion E)) = Ideal.absNorm w.asIdeal :=
    GroundTheory.Global.residueCard_adicCompletion
  rw [h1, Units.val_mk0, GroundTheory.LocalField.modulus_of_ne_zero hx, h3]
  unfold absHalf
  rw [ordL_eq_ord w hx]
  have hq : (0 : ℝ) ≤ ((qV E w : ℕ) : ℝ) ^ (-GroundTheory.LocalField.ord x) := zpow_nonneg (Nat.cast_nonneg _) _
  rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  simp [qV]

end GlobalTheory.ModAbs
