import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysEval

section Abstract

variable {B P R : Type} [CommRing B] [CommRing P] [CommRing R] (l : ℕ) (ι : B →+* P) (f : B →+* R)

def Approx (F : P) (r : ℕ) (y : R) : Prop :=
  ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h ∧ (n : R) * y = f b

variable {l ι f}

theorem approx_add {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F + G) r (y + z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, (m : B) * b + (n : B) * c, p + q, h + k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz]; push_cast; ring

theorem approx_mul {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F * G) r (y * z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, b * c, p * q, p * k + h * q + (l : P) ^ r * h * k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_mul, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_mul, ← hy, ← hz]; push_cast; ring

theorem approx_ι (b : B) (r : ℕ) : Approx l ι f (ι b) r (f b) :=
  ⟨1, b, ι b, 0, one_ne_zero, by simp, by simp, by simp⟩

theorem approx_one (r : ℕ) : Approx l ι f 1 r 1 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 1 r

theorem approx_zero (r : ℕ) : Approx l ι f 0 r 0 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 0 r

variable (htf : ∀ (n : ℕ) (x : R), n ≠ 0 → (n : R) * x = 0 → x = 0)
  (hK : ∀ (n : ℕ) (b : B) (p : P), n ≠ 0 → (n : P) * p = ι b → ∃ y : R, (n : R) * y = f b) (hl0 : l ≠ 0)
include htf hK hl0

theorem approx_dvd {F : P} {r s : ℕ} (hrs : r ≤ s) {y z : R} (hy : Approx l ι f F r y)
    (hz : Approx l ι f F s z) : (l : R) ^ r ∣ y - z := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hy
  obtain ⟨m, c, q, k, hm, hq, hF', hz⟩ := hz
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  have h0 : p - q = (l : P) ^ r * ((l : P) ^ d * k - h) := by linear_combination hF' - hF
  have h1 : ((n * m * l ^ r : ℕ) : P) * ((l : P) ^ d * k - h) = ι ((m : B) * b - (n : B) * c) := by
    rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]
    push_cast
    linear_combination ((n : P) * m) * h0.symm
  obtain ⟨w, hw⟩ := hK _ _ _ (mul_ne_zero (mul_ne_zero hn hm) (pow_ne_zero _ hl0)) h1
  refine ⟨w, (sub_eq_zero.1 (htf (n * m) _ (mul_ne_zero hn hm) ?_)).symm⟩
  rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz] at hw
  push_cast at hw ⊢
  linear_combination hw

variable [IsAdicComplete (Ideal.span {(l : R)}) R]
  (hD : ∀ (F : P) (r : ℕ), ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h)

omit htf hl0 in
include hD in
theorem exists_approx (F : P) (r : ℕ) : ∃ y, Approx l ι f F r y := by
  obtain ⟨n, b, p, h, hn, hp, hF⟩ := hD F r
  obtain ⟨y, hy⟩ := hK n b p hn hp
  exact ⟨y, n, b, p, h, hn, hp, hF, hy⟩

omit htf hK hl0 in
variable (l) in

theorem sep_l (x : R) (h : ∀ r : ℕ, (l : R) ^ r ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(l : R)}) x fun n => by
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n

include hD in
theorem exists_lim (F : P) : ∃ L : R, ∀ r y, Approx l ι f F r y → (l : R) ^ r ∣ L - y := by
  choose y hy using exists_approx hK hD F
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : R)}) y (fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact approx_dvd htf hK hl0 hmn (hy m) (hy n))
  refine ⟨L, fun r z hz => ?_⟩
  have h1 := hL r
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  have h2 := approx_dvd htf hK hl0 le_rfl (hy r) hz
  have e : L - z = (y r - z) - (y r - L) := by ring
  rw [e]
  exact dvd_sub h2 h1

include hD in

theorem exists_ringHom : ∃ E : P →+* R, ∀ F r y, Approx l ι f F r y → (l : R) ^ r ∣ E F - y := by
  choose L hL using exists_lim htf hK hl0 hD
  have key : ∀ F z, (∀ r, ∃ y, Approx l ι f F r y ∧ (l : R) ^ r ∣ z - y) → L F = z := fun F z hz =>
    sub_eq_zero.1 (sep_l l _ fun r => by
      obtain ⟨y, hy, hzy⟩ := hz r
      have e : L F - z = (L F - y) - (z - y) := by ring
      rw [e]
      exact dvd_sub (hL F r y hy) hzy)
  have h1 : L 1 = 1 := key 1 1 fun r => ⟨1, approx_one r, by simp⟩
  have h0 : L 0 = 0 := key 0 0 fun r => ⟨0, approx_zero r, by simp⟩
  have hm : ∀ F G, L (F * G) = L F * L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y * z, approx_mul hy hz, c * z + y * d + (l : R) ^ r * c * d, by
      linear_combination (L G) * hc + (y + (l : R) ^ r * c) * hd⟩
  have ha : ∀ F G, L (F + G) = L F + L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y + z, approx_add hy hz, c + d, by linear_combination hc + hd⟩
  exact ⟨{ toFun := L, map_one' := h1, map_zero' := h0, map_mul' := hm, map_add' := ha }, hL⟩

omit hK in
include hD in

theorem ringHom_ext_dense (G₁ G₂ : P →+* R) (h : ∀ b, G₁ (ι b) = G₂ (ι b)) : G₁ = G₂ := by
  ext F
  refine sub_eq_zero.1 (sep_l l _ fun r => ?_)
  obtain ⟨n, b, p, k, hn, hp, hF⟩ := hD F r
  have e1 : (n : R) * (G₁ p - G₂ p) = G₁ ((n : P) * p) - G₂ ((n : P) * p) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]; ring
  have h1 : G₁ p = G₂ p := sub_eq_zero.1 (htf n _ hn (by rw [e1, hp, h, sub_self]))
  exact ⟨G₁ k - G₂ k, by rw [hF, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, h1]; ring⟩

end Abstract

section Concrete

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] (t : Wq l a →ₐ[ℤ_[l]] O)

variable (K) in

def embK (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom

variable (l a) in

abbrev Bp : Type := Polynomial (Polynomial (Wq l a))

variable (K) in

def rhoK (τ : ZMod a) : Polynomial (Wq l a) →+* K⟦X⟧ :=
  (PowerSeries.map (embK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

variable (K) in

def iotaP : Bp l a →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (PowerSeries.map (rhoK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

theorem coeff_iotaP (b : Bp l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (iotaP K t b τ)) = embK K t τ ((b.coeff i).coeff n) := by
  rw [show iotaP K t b τ = PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧) from rfl, coeff_map,
    Polynomial.coeff_coe, rhoK, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, coeff_map,
    Polynomial.coeff_coe]

theorem rhoK_eq_toAc [IsUltrametricDist K] [IsUnitBall O K] (q : Polynomial (Wq l a)) (τ : ZMod a) :
    rhoK K t τ q = (toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧) := by
  ext n
  rw [coeff_toAc]
  simp [rhoK, embK, coeff_map, Polynomial.coeff_coe]

theorem charZero_K [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem embK_injective [NormedAlgebra ℚ_[l] K] (τ : ZMod a) : Function.Injective (embK K t τ) := by
  have := charZero_K (l := l) (K := K)
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  by_contra h0
  obtain ⟨m, v, hv, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit v := WittVector.isUnit_of_coeff_zero_ne_zero v hv
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)) (hu.map _).ne_zero hw

include t in

theorem wq_nat_cancel [NormedAlgebra ℚ_[l] K] {n : ℕ} (hn : n ≠ 0) {x : Wq l a}
    (h : (n : Wq l a) * x = 0) : x = 0 := by
  have := charZero_K (l := l) (K := K)
  refine embK_injective (K := K) t 0 ?_
  have h1 := congrArg (embK K t 0) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hn)

variable {e : ℕ} (ϖ : PiSys l e)

theorem ev_coe (q : Polynomial (Wq l a)) :
    ϖ.ev a (q : (Wq l a)⟦X⟧) = q.eval₂ (wA l a).toRingHom ϖ.teich := by
  have h := Polynomial.ringHom_ext (f := (ϖ.ev a).comp Polynomial.coeToPowerSeries.ringHom)
    (g := Polynomial.eval₂RingHom (wA l a).toRingHom ϖ.teich) (fun w => by simp) (by simp)
  exact RingHom.congr_fun h q

variable (a) in

def evC : Polynomial (Wq l a) →+* Per.Acris l :=
  ((ainfToAcris l).toRingHom.comp (ϖ.ev a)).comp Polynomial.coeToPowerSeries.ringHom

variable (a) in

def fP (g : GQ l) : Bp l a →+* Per.Acris l :=
  Polynomial.eval₂RingHom (evC a ϖ) (ainfToAcris l (ϖ.mu g * ϖ.teich))

end Concrete

end GlobalTheory.CrysEval
