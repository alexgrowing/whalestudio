import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma UpperTheory.Gal.productCup_of_system.valuation_mul_bis (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v w : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e w b) : Val B e (v * w) (a * b) := by
  obtain ⟨-, ⟨ev, hev⟩, -⟩ := hV L B e
  obtain ⟨h1, ha⟩ := (hev v a).1 h
  obtain ⟨h2, hb⟩ := (hev w b).1 h'
  refine (hev (v * w) (a * b)).2 ⟨Subalgebra.mul_mem _ h1 h2, ?_⟩
  rw [← ha, ← hb, ← map_mul]
  rfl

private lemma UpperTheory.Gal.productCup_of_system.valuation_unique (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e v b) : a = b := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  rfl

private lemma UpperTheory.Gal.productCup_of_system.valuation_mem (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {b : L} (hb : b ∈ B) : Val B e b (e ⟨b, hb⟩) :=
  (hV L B e).2.2.1 ⟨b, hb⟩

theorem UpperTheory.Gal.productCup_of_system.ptT_of :
    LocEq → ValBasic → RYBasic → PtT := by
  intro hLoc hV hRY
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY I J i hi j hj e hv
  have hr : ∀ l, (sysY x j2 d).r n10 (gT x j2) i j l =
      algebraMap F K' (x l.succ) / algebraMap F K' (x i) := by
    intro l
    simp [Sys.r, Sys.u, gT, sysY, n10, div_eq_mul_inv]
  have hw : ∀ a b, (((sysY x j2 d).X a * ((sysY x j2 d).X b)⁻¹ : K'ˣ) : K') =
      algebraMap F K' (x a) / algebraMap F K' (x b) := by
    intro a b
    simp [sysY, div_eq_mul_inv]
  have hxne : ∀ a, algebraMap F K' (x a : F) ≠ 0 := fun a => (map_ne_zero _).2 (x a).ne_zero
  have h1 : Val (RY (xv x) j2 I J) e 1 1 := by
    have h1v := valuation_mem hV (RY (xv x) j2 I J) e (one_mem (RY (xv x) j2 I J))
    have h1' : (⟨1, one_mem _⟩ : RY (xv x) j2 I J) = 1 := rfl
    rw [h1', map_one] at h1v
    exact h1v
  have hv' : ∀ l : Fin d, Val (RY (xv x) j2 I J) e
      (algebraMap F K' (x l.succ) / algebraMap F K' (x i)) 0 := fun l => hr l ▸ hv l
  have hi0 : i = 0 := by
    by_contra h
    have hvi := hv' (i.pred h)
    rw [Fin.succ_pred, div_self (hxne i)] at hvi
    exact zero_ne_one (valuation_unique hV _ e hvi h1)
  subst hi0
  have hI : I = {0} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun i' hi' => ?_⟩
    by_contra h
    have hgood := (hRY F K K' d x j2 hY).2.1 d
    have hm := hgood.memX I J ⟨j, hj⟩ i' hi' 0
    rw [hw] at hm
    have hval := valuation_mem hV (RY (xv x) j2 I J) e hm
    have hprod := valuation_mul_bis hV _ e (hv' (i'.pred h)) hval
    rw [Fin.succ_pred, zero_mul] at hprod
    have hone : algebraMap F K' (x i') / algebraMap F K' (x 0) *
        (algebraMap F K' (x 0) / algebraMap F K' (x i')) = 1 := by
      rw [div_mul_div_comm, mul_comm (algebraMap F K' (x i')),
        div_self (mul_ne_zero (hxne 0) (hxne i'))]
    rw [hone] at hprod
    exact zero_ne_one (valuation_unique hV _ e hprod h1)
  obtain ⟨e0, hloc, hval⟩ := hLoc F K K' d x j2 hY I J 0 hi e
  refine ⟨⟨e0, fun l => ?_⟩, hI, hloc, hval⟩
  have ht := tco_mem ℂ K' (xv x) l
  have h0 := (hval _ _).1 (hv' l)
  rw [← map_div₀] at h0
  have hm := valuation_mem hV _ e0 ht
  exact valuation_unique hV _ e0 hm h0
