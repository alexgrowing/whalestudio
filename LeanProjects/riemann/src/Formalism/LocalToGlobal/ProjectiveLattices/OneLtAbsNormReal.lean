import Mathlib

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero

namespace Formalism.L2.Pj

section Base

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]

def vLa (la : HeightOneSpectrum R) (x : K) : ℤ := -WithZero.log (la.valuation K x)

end Base

section Dvr

variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

def valV : Valuation K' ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal V).valuation K'

def vV (x : K') : ℤ := -WithZero.log (valV V x)

variable {V}

lemma valV_ne_zero {x : K'} (hx : x ≠ 0) : valV V x ≠ 0 := by
  simpa [valV] using hx

lemma vV_mul {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) : vV V (x * y) = vV V x + vV V y := by
  simp only [vV, map_mul, WithZero.log_mul (valV_ne_zero hx) (valV_ne_zero hy)]
  ring

lemma min_le_vV_add {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vV V x) (vV V y) ≤ vV V (x + y) := by
  have h := (valV V).map_add x y
  rcases max_choice (valV V x) (valV V y) with hm | hm <;> rw [hm] at h
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hx)).2 h
    exact (min_le_left _ _).trans (by simp only [vV]; omega)
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hy)).2 h
    exact (min_le_right _ _).trans (by simp only [vV]; omega)

variable (V)

def nval (e : ℕ) (x : K') : EReal :=
  open Classical in if x = 0 then ⊤ else (((vV V x : ℝ) / e : ℝ) : EReal)

variable {V}

lemma nval_zero (e : ℕ) : nval V e (0 : K') = ⊤ := by simp [nval]

lemma nval_of_ne {e : ℕ} {x : K'} (hx : x ≠ 0) :
    nval V e x = (((vV V x : ℝ) / e : ℝ) : EReal) := by
  simp [nval, hx]

lemma nval_ne_bot (e : ℕ) (x : K') : nval V e x ≠ ⊥ := by
  unfold nval; split_ifs <;> simp

lemma nval_add (e : ℕ) (x y : K') : min (nval V e x) (nval V e y) ≤ nval V e (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, nval_zero]; exact le_top
  by_cases hx : x = 0
  · subst hx; simp
  by_cases hy : y = 0
  · subst hy; simp
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne hxy]
  rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
  · exact min_le_iff.2 (Or.inl (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))
  · exact min_le_iff.2 (Or.inr (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))

lemma nval_mul (e : ℕ) (x y : K') : nval V e (x * y) = nval V e x + nval V e y := by
  by_cases hx : x = 0
  · subst hx; rw [zero_mul, nval_zero, EReal.top_add_of_ne_bot (nval_ne_bot e y)]
  by_cases hy : y = 0
  · subst hy; rw [mul_zero, nval_zero, EReal.add_top_of_ne_bot (nval_ne_bot e x)]
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne (mul_ne_zero hx hy), vV_mul hx hy,
    Int.cast_add, add_div, EReal.coe_add]

lemma nval_mul_unit (e : ℕ) {u : K'} (hu : u ≠ 0) (hu0 : vV V u = 0) (x : K') :
    nval V e (u * x) = nval V e x := by
  rw [nval_mul, nval_of_ne hu, hu0]; simp

lemma nval_bc {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (i : K' →+* K'') {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) (e : ℕ) (x : K') :
    nval V' (r * e) (i x) = nval V e x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, nval_zero, nval_zero]
  rw [nval_of_ne ((map_ne_zero i).2 hx), nval_of_ne hx, hi]
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  congr 1; push_cast; exact mul_div_mul_left _ _ hr'

end Dvr

structure CDVR where

  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V]
  [ch0 : CharZero V]

attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0

abbrev CDVR.Fr (T : CDVR) : Type := FractionRing T.V

def CDVR.FinRes (T : CDVR) : Prop := Finite (IsLocalRing.ResidueField T.V)

section Over

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]

def OverLa (la : HeightOneSpectrum R) (V : Type) {K' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K'] (ι : K →+* K')
    (e : ℕ) : Prop :=
  0 < e ∧ ∀ a : K, vV V (ι a) = (e : ℤ) * vLa la a

variable {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']

lemma nval_smul {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a : K} (ha : a ≠ 0) (x : K') :
    nval V e (ι a * x) = (((vLa la a : ℤ) : ℝ) : EReal) + nval V e x := by
  rw [nval_mul, nval_of_ne ((map_ne_zero ι).2 ha), ho.2 a]
  congr 1
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  congr 1; push_cast; field_simp

lemma OverLa.bc {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {V' K'' : Type} [CommRing V']
    [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K''] [IsFractionRing V' K'']
    (i : K' →+* K'') {r : ℕ} (hr : 0 < r) (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) :
    OverLa la V' (i.comp ι) (r * e) :=
  ⟨Nat.mul_pos hr ho.1, fun a => by rw [RingHom.comp_apply, hi, ho.2 a]; push_cast; ring⟩

structure IsEval {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    (wadd : W → W → W) (mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')) {F : Type} [Field F]
    (ι : K →+* F) (ev : ∀ w, Cusp w → F) : Prop where
  add : ∀ w f g, ev w (f + g) = ev w f + ev w g
  smul : ∀ w (a : K) f, ev w (a • f) = ι a * ev w f
  mul : ∀ w w' f g, ev (wadd w w') (mulC w w' f g) = ev w f * ev w' g

lemma IsEval.zero {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    {wadd : W → W → W} {mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')} {F : Type} [Field F]
    {ι : K →+* F} {ev : ∀ w, Cusp w → F} (h : IsEval wadd mulC ι ev) (w : W) : ev w 0 = 0 := by
  have := h.smul w 0 0
  rwa [zero_smul, map_zero, zero_mul] at this

end Over

section Norm

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

lemma finitePlace_eq_zpow {a : K} (ha : a ≠ 0) :
    FinitePlace.mk la a = (Ideal.absNorm la.asIdeal : ℝ) ^ (-(vLa la a)) := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ ((la.valuation K).ne_zero_iff.2 ha)]
  simp [vLa, WithZero.toAdd_unzero_eq_log]

def nrmOf (v : EReal) : ℝ :=
  open Classical in if v = ⊤ then 0 else (Ideal.absNorm la.asIdeal : ℝ) ^ (-v.toReal)

lemma one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm la

lemma nrmOf_le_one_iff {v : EReal} (hv : v ≠ ⊥) : nrmOf la v ≤ 1 ↔ 0 ≤ v := by
  by_cases ht : v = ⊤
  · subst ht; simp [nrmOf]
  lift v to ℝ using ⟨ht, hv⟩
  simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe, EReal.coe_nonneg]
  rw [← Real.rpow_zero (Ideal.absNorm la.asIdeal : ℝ),
    Real.rpow_le_rpow_left_iff (one_lt_absNorm_real la)]
  constructor <;> intro h <;> linarith

lemma nrmOf_smul {a : K} (ha : a ≠ 0) {v : EReal} (hv : v ≠ ⊥) :
    nrmOf la ((((vLa la a : ℤ) : ℝ) : EReal) + v) = FinitePlace.mk la a * nrmOf la v := by
  rw [finitePlace_eq_zpow la ha]
  by_cases ht : v = ⊤
  · subst ht; simp [nrmOf]
  lift v to ℝ using ⟨ht, hv⟩
  simp only [nrmOf, ← EReal.coe_add, EReal.coe_ne_top, if_false, EReal.toReal_coe]
  rw [neg_add, Real.rpow_add (by linarith [one_lt_absNorm_real la]), ← Real.rpow_intCast]
  push_cast; ring_nf

end Norm

end Formalism.L2.Pj
