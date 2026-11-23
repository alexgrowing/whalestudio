import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.Faithful

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]

theorem act_zero (act : OAct O G) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := act.act 0) (by rw [← h, _root_.mul_one])

theorem act_natCast (act : OAct O G) (n : ℕ) : act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

theorem act_mul_eq_one (act : OAct O G) {c : O} (hc : act.act c = 1) (d : O) : act.act (d * c) = 1 := by
  rw [act.mul, hc, MonObj.comp_one]

theorem pow_eq_one_of_act (act : OAct O G) {n : ℕ} (hn : act.act (n : O) = 1) {T : Over S} (x : T ⟶ G) :
    x ^ n = 1 := by
  have h : x ≫ (𝟙 G ^ n) = x ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← h, ← act_natCast act, hn, MonObj.comp_one]

end

theorem act_injective : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), 1 ≤ P.g → Function.Injective act.act := by
  intro hL E _ _ K _ _ P act hg a b hab
  by_contra hne
  have hc0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hc : act.act (a - b) = 1 := by
    have h := act.add (a - b) b
    rw [sub_add_cancel, hab] at h
    exact mul_right_cancel (b := act.act b) (by rw [← h, _root_.one_mul])
  set n : ℕ := Ideal.absNorm (Ideal.span {a - b}) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a - b}))
  have h1 : act.act (n : 𝓞 E) = 1 := by
    rw [hn, ← hd]; exact act_mul_eq_one act hc d
  let k := AlgebraicClosure K
  let t : Spec (CommRingCat.of k) ⟶ Sp (𝓞 K) :=
    Spec.map (CommRingCat.ofHom ((algebraMap K k).comp (algebraMap (𝓞 K) K)))
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap K k).injective
  have key : ∀ m : ℕ, 1 ≤ m → Nat.card (Over.mk t ⟶ P.A) = (n * m) ^ (2 * P.g) := by
    intro m hm
    have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn0 (by omega)
    obtain ⟨-, -, -, -, h⟩ := hL.mulN _ P (n * m) (Nat.one_le_iff_ne_zero.mpr hnm)
    rw [← h k t (Nat.cast_ne_zero.mpr hnm)]
    refine (Nat.card_congr (Equiv.subtypeUnivEquiv fun x => ?_)).symm
    rw [pow_mul, pow_eq_one_of_act act h1, one_pow]
  have e := (key 1 le_rfl).symm.trans (key 2 (by norm_num))
  have := Nat.pow_left_injective (by omega : 2 * P.g ≠ 0) e
  omega

end GlobalTheory.LamF.Faithful
