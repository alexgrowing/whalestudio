import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem toG_one' {F : Type} [Field F] (m : ℕ) :
    toG (1 : Matrix (Fin m) (Fin m) F) = 1 := by
  unfold toG
  rw [dif_pos isUnit_one]
  exact Units.ext (IsUnit.unit_spec _)

private theorem ent_one' {F : Type} [Field F] {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) :
    ent (1 : Matrix (Fin n) (Fin n) F) i j = if i = j then 1 else 0 := by
  unfold ent
  rw [dif_pos ⟨hi, hj⟩, Matrix.one_apply]
  simp only [Fin.mk.injEq]

private theorem tlG_one' {F : Type} [Field F] (a b : ℕ) :
    tlG a (1 : GL (Fin (a + b)) F) = 1 := by
  have h : tl a ((1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    show ent _ (i : ℕ) (j : ℕ) = _
    rw [Units.val_one, ent_one' _ _ (lt_of_lt_of_le i.isLt (Nat.le_add_right a b))
      (lt_of_lt_of_le j.isLt (Nat.le_add_right a b))]
    simp only [Fin.val_inj]
  unfold tlG
  rw [h, toG_one']

private theorem brG_one' {F : Type} [Field F] (a b : ℕ) :
    brG a b (1 : GL (Fin (a + b)) F) = 1 := by
  have h : br a b ((1 : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    show ent _ (a + (i : ℕ)) (a + (j : ℕ)) = _
    rw [Units.val_one, ent_one' _ _ (Nat.add_lt_add_left i.isLt a)
      (Nat.add_lt_add_left j.isLt a)]
    simp only [Nat.add_left_cancel_iff, Fin.val_inj]
  unfold brG
  rw [h, toG_one']

private theorem inPar_one' {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  rw [Units.val_one, Matrix.one_apply_ne]
  intro h
  rw [h] at hi
  omega

private theorem gal_id' {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  rfl

theorem UpperTheory.Gal.InertialTypesAlt.hcOne :
    HcOne := by
  intro F _ _ a b n hn α β hα hβ
  subst hn
  unfold hc hcTw
  simp only [gal_id', mul_one, inv_mul_cancel, inPar_one', ite_true, tlG_one', brG_one']
  haveI : Nonempty { p : GL (Fin (a + b)) F // InPar a p } := ⟨⟨1, inPar_one' a _⟩⟩
  haveI : Fintype (GL (Fin (a + b)) F) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, nsmul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    (mul_ne_zero (Nat.cast_ne_zero.mpr Finset.univ_nonempty.card_pos.ne') (mul_ne_zero hα hβ))
