import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem ge_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  obtain ⟨p, hpm, hp⟩ := hx
  have hZ : ∀ z : ℤ, V.Ge 0 (algebraMap ℤ C z) := by
    intro z
    rw [eq_intCast]
    refine Int.induction_on z ?_ ?_ ?_
    · rw [Int.cast_zero]; exact VF.Ge.zero 0
    · intro i ih
      rw [Int.cast_add, Int.cast_one]
      exact VF.Ge.add ih VF.Ge.one
    · intro i ih
      rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg]
      exact VF.Ge.add ih (VF.Ge.neg VF.Ge.one)
  by_contra hneg
  have hlt : V.v x < ((0 : ℝ) : WithTop ℝ) := not_le.mp hneg
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hr0 : r < 0 := by
    rw [← hr] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr
    exact WithTop.coe_ne_top hr
  set yv := x⁻¹ with hyv
  have hy0 : yv ≠ 0 := inv_ne_zero hx0
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (fun h => hy0 ((AddValuation.top_iff V.v).mp h))
  have hrs : r + s = 0 := by
    have h1 : V.v (x * yv) = 0 := by rw [hyv, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [AddValuation.map_mul, ← hr, ← hs] at h1
    exact_mod_cast h1
  have hy : V.Ge (-r) yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hy0' : V.Ge 0 yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hpow : ∀ k : ℕ, V.Ge 0 (yv ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact VF.Ge.one
    | succ k ih => rw [pow_succ]; exact VF.Ge.mul_int ih hy0'
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hp
  set n := p.natDegree
  have hsum : 1 + ∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) = 0 := by
    have h2 := congrArg (· * yv ^ n) hp
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [← h2]
    congr 1
    · rw [← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := le_of_lt (Finset.mem_range.mp hi)
      conv_rhs => rw [show n = (n - i) + i from (Nat.sub_add_cancel hi').symm]
      rw [pow_add, mul_assoc, mul_left_comm (x ^ i), ← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow, mul_one]
  have hS : V.Ge (-r) (∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i)) := by
    refine Finset.sum_induction _ (fun z => V.Ge (-r) z) (fun _ _ ha hb => VF.Ge.add ha hb) (VF.Ge.zero _) ?_
    intro i hi
    have hi' : n - i = (n - i - 1) + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [hi', pow_succ, ← mul_assoc]
    exact VF.Ge.mul_int (VF.Ge.mul_int (hZ _) (hpow _)) hy
  have h1 : (1 : C) = -∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) :=
    eq_neg_of_add_eq_zero_left hsum
  have hS' := VF.Ge.neg hS
  rw [← h1] at hS'
  unfold VF.Ge at hS'
  rw [AddValuation.map_one] at hS'
  have : (-r : ℝ) ≤ 0 := by exact_mod_cast hS'
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem embedding_integral (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) : V.Ge 0 (emA3 io ι τ x) := by
  exact ge_of_isIntegral V ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map (emA3 io ι τ).toIntAlgHom)

theorem embK_conj (hstar : ∀ a : 𝓞 E, star a = H.bar a) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (star x) := by
  unfold embK
  apply Subtype.ext
  simp [embF]
  rw [hstar]
  rw [show (algebraMap (𝓞 E) E) (H.bar x) = ((H.bar x : 𝓞 E) : E) from rfl, H.bar_eq x,
    IsCMField.complexEmbedding_complexConj]

theorem embedding_conjugate (hstar : ∀ a : 𝓞 E, star a = H.bar a) (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) :
    emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (star x) := by
  simp only [emA3, RingHom.coe_comp, Function.comp_apply, embK_conj hstar]

theorem a3uvec_int (C3 : IntChart T io y) {ι : T.Fr →+* C} (hι : EmbOK T V ι) (ℓ : Lt1 Dw) (i : Fin (chD C3.ch)) :
    V.Ge 0 (ι (chartUnitVectors C3 ℓ i)) := by
  obtain ⟨⟨-, -, -, -, -, -, hu⟩, -⟩ := C3.gen
  rw [show chartUnitVectors C3 ℓ i = _ from hu ℓ i]
  exact embIntSt_holds T C V ι hι _

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

structure LabGeoCore (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : Lab E Orb d) :
    Prop where
  u_eig : ∀ o g (x : lab.II Dw o g) a, linAct (Y.B.A.act a) (lieBasisVector C3 ι lab o g x) =
    emA3 io ι (lab.tau o g x.1) a • lieBasisVector C3 ι lab o g x
  u_sat : ∀ o g, ∃ w : Fin (chD C3.ch) → lab.II Dw o g → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o g, ∑ x, lieBasisVector C3 ι lab o g q x * w x q' = if q = q' then 1 else 0
  u_full : ∀ o g a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o g a) x • v) →
    ∃ b : lab.II Dw o g → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • lieBasisVector C3 ι lab o g q

end Core

variable (Xo c)

def LabGeoCoreSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → LabGeoCore C3 ι Y lab

end Formalism.L2.FormalSeriesBounds
