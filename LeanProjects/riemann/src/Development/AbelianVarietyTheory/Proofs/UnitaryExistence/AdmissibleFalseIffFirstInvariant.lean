import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.LevelIndexFourierCharacter

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortDatumEq

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def cls (l : Level H) {n : ℕ} (x : Fin n → D.La) : Fin n → ConjCl D l := fun b => Submodule.Quotient.mk (x b)

theorem cls_surjective (l : Level H) (n : ℕ) : Function.Surjective (cls (D := D) l (n := n)) := fun a =>
  ⟨fun b => qRep (a b), funext fun b => Classical.choose_spec (Submodule.Quotient.mk_surjective _ (a b))⟩

theorem cls_neg {n : ℕ} (x : Fin n → D.La) : cls l (-x) = -cls l x := by
  funext b; simp [cls]

theorem isSep_cSep (l : Level H) : IsSep l (cSep l) := by
  have h : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := exists_isSep l
  rw [cSep, dif_pos h]
  exact h.choose_spec

theorem mk_levRep (q : LevQ D l) : (Submodule.Quotient.mk (levRep q) : NamedCl D l) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

theorem levPt_levRep (Xo : Moduli D l) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (q : LevQ D l) :
    levPt Xo x0 (levRep q) = levPtCl Xo x0 q := by
  rw [← levPtCl_mk, mk_levRep]

theorem pairL_cast {n : ℕ} (x0 x : Fin n → D.La) :
    ((pairL (l := l) x0 x : ℤ) : ZMod l.M) = pairing D l (cls l x0) (fun b => Submodule.Quotient.mk (x b)) := by
  simp only [pairL, pairing, cls, Int.cast_sum, pairOne_mk D l (isSep_cSep l)]

theorem pairL_levRep {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    ((pairL (l := l) x0 (fun b => levRep (q b)) : ℤ) : ZMod l.M) = pairing D l (cls l x0) q := by
  rw [pairL_cast]; simp only [mk_levRep]

theorem zetaM_eq (c : Coeff l) : Formalism.L2.Pj.zetaM c = GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero hM l.A_pos.ne'
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hM' hk
  have hd : l.M' / l.M = k := by rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hM)]
  apply Subtype.ext
  rw [Formalism.L2.Pj.zetaM, hd, GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM]
  change zeta l.M' ^ k = zeta l.M
  rw [zeta, zeta, ← Complex.exp_nat_mul, hk]
  congr 1
  have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  have : (l.M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hM
  push_cast
  field_simp

theorem zeta_zpow (c : Coeff l) (m : ℤ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ^ m = GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ^ (m : ZMod l.M).val := by
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  have hz := zetaM_prim c
  have hne : GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation.zetaM c ≠ 0 := hz.ne_zero (NeZero.ne _)
  rw [← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv m l.M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hz.pow_eq_one, one_zpow, _root_.mul_one]

theorem datum_eq_character_pairing (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    x0Dat c x0 q = eChar D c (cls l x0) q := by
  rw [x0Dat, eChar, zetaM_eq, zeta_zpow, pairL_levRep]

theorem datum_neg_eq_inv (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    x0Dat c (-x0) q = (x0Dat c x0 q)⁻¹ := by
  simp only [x0Dat, ← zpow_neg]
  congr 1
  simp [pairL]

theorem indCoeff_cls (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    indCoeff c (cls l x0) q = (Nat.card (Fin n → LevQ D l) : c.F)⁻¹ * x0Dat c (-x0) q := by
  rw [indCoeff_eq, datum_neg_eq_inv, datum_eq_character_pairing, eChar]

theorem normalized_datum_eq_induced_coeff (c : Coeff l) {n : ℕ} (x0 : Fin n → D.La) (q : Fin n → LevQ D l) :
    (Nat.card (Fin n → LevQ D l) : c.F)⁻¹ * x0Dat c x0 q = indCoeff c (-cls l x0) q := by
  rw [← cls_neg, indCoeff_cls, neg_neg]

end GlobalTheory.ShortDatumEq
