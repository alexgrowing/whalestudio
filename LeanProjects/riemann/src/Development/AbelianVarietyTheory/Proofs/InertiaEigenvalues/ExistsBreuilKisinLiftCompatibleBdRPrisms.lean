import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdealStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsApproxRootEisensteinAwayPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinApproxRootImageIndepStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxRootSubUniformizerMemFilPStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RingHomLiftCongruence

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem exists_poly (bk : BK K) (y : bk.S ⧸ Ideal.span {bk.E}) :
    ∃ P : Polynomial (Wq l bk.a), Ideal.Quotient.mk _ (P : bk.S) = y := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have H : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  exact ⟨_, H.isWeierstrassDivisorAt'.mk_mod'_eq_self⟩

theorem exists_dvd_pow_mul_ringHom_sub_mul {S A : Type} [CommRing S] [CommRing A] (f g : S →+* A) (e p : A) (s t : S)
    (hs : ∃ k : ℕ, e ∣ p ^ k * (f s - g s)) (ht : ∃ k : ℕ, e ∣ p ^ k * (f t - g t)) :
    ∃ k : ℕ, e ∣ p ^ k * (f (s * t) - g (s * t)) := by
  obtain ⟨a, x, hx⟩ := hs
  obtain ⟨b, y, hy⟩ := ht
  refine ⟨a + b, p ^ b * f t * x + p ^ a * g s * y, ?_⟩
  rw [map_mul, map_mul]
  linear_combination (p ^ b * f t) * hx + (p ^ a * g s) * hy

theorem exists_dvd_pow_mul_ringHom_sub_natPowComb {S A : Type} [CommRing S] [CommRing A] (f g : S →+* A) (e p : A) (m i j : ℕ) (s t : S)
    (hs : ∃ k : ℕ, e ∣ p ^ k * (f s - g s)) (ht : ∃ k : ℕ, e ∣ p ^ k * (f t - g t)) :
    ∃ k : ℕ, e ∣ p ^ k * (f ((m : S) ^ i * s + (m : S) ^ j * t) - g ((m : S) ^ i * s + (m : S) ^ j * t)) := by
  obtain ⟨a, x, hx⟩ := hs
  obtain ⟨b, y, hy⟩ := ht
  refine ⟨a + b, p ^ b * (m : A) ^ i * x + p ^ a * (m : A) ^ j * y, ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast]
  linear_combination (p ^ b * (m : A) ^ i) * hx + (p ^ a * (m : A) ^ j) * hy

theorem ringHom_lift_sub_mem_mul {S R A : Type} [CommRing S] [CommRing R] [CommRing A] (ψ : S →+* A) (φ : R →+* A) (I : Ideal A)
    (p : A) (i j : ℕ) (s t : S) (x y : R) (hs : ψ s - p ^ i * φ x ∈ I) (ht : ψ t - p ^ j * φ y ∈ I) :
    ψ (s * t) - p ^ (i + j) * φ (x * y) ∈ I := by
  have h := I.add_mem (I.mul_mem_left (ψ t) hs) (I.mul_mem_left (p ^ i * φ x) ht)
  convert h using 1
  rw [map_mul, map_mul]
  ring

theorem ringHom_lift_sub_mem_natPowComb {S R A : Type} [CommRing S] [CommRing R] [CommRing A] (ψ : S →+* A) (φ : R →+* A) (I : Ideal A)
    (m i j : ℕ) (s t : S) (x y : R) (hs : ψ s - (m : A) ^ i * φ x ∈ I) (ht : ψ t - (m : A) ^ j * φ y ∈ I) :
    ψ ((m : S) ^ j * s + (m : S) ^ i * t) - (m : A) ^ (i + j) * φ (x + y) ∈ I := by
  have h := I.add_mem (I.mul_mem_left ((m : A) ^ j) hs) (I.mul_mem_left ((m : A) ^ i) ht)
  convert h using 1
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

noncomputable def oK (K : FinExt l) (C : Core l) : ↥(OL K) →+* Per.BdRp l :=
  C.o.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)

def Good (bk : BK K) (C : Core l) (n : ℕ) (x : ↥(OL K)) : Prop :=
  ∃ (k : ℕ) (s : bk.S), ((aDp l).comp bk.ev) s - (l : Per.BdRp l) ^ k * oK K C x ∈ Per.FilP l n ∧
    ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f s - BK.hf g s)

variable {bk : BK K} {C : Core l} {n : ℕ}

theorem Good.mul {x y : ↥(OL K)} (hx : Good bk C n x) (hy : Good bk C n y) : Good bk C n (x * y) := by
  obtain ⟨i, s, hs, hs'⟩ := hx
  obtain ⟨j, t, ht, ht'⟩ := hy
  exact ⟨i + j, s * t, ringHom_lift_sub_mem_mul _ _ _ _ i j s t x y hs ht,
    fun B f g => exists_dvd_pow_mul_ringHom_sub_mul _ _ _ _ s t (hs' B f g) (ht' B f g)⟩

theorem Good.add {x y : ↥(OL K)} (hx : Good bk C n x) (hy : Good bk C n y) : Good bk C n (x + y) := by
  obtain ⟨i, s, hs, hs'⟩ := hx
  obtain ⟨j, t, ht, ht'⟩ := hy
  exact ⟨i + j, (l : bk.S) ^ j * s + (l : bk.S) ^ i * t, ringHom_lift_sub_mem_natPowComb _ _ _ l i j s t x y hs ht,
    fun B f g => exists_dvd_pow_mul_ringHom_sub_natPowComb _ _ _ _ l j i s t (hs' B f g) (ht' B f g)⟩

theorem good_C (w : Wq l bk.a) :
    Good bk C n (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) := by
  refine ⟨0, PowerSeries.C w, ?_, fun B f g => ⟨0, ?_⟩⟩
  · have h := bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) (PowerSeries.C w)
      (bk.str.apply_symm_apply _).symm
    rw [bk.ev_C] at h
    have h2 := GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w
      (((bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w)) : ↥(OL K)) : ↥K.1) : Om l)
      (by rw [h]; exact coe_intToOC K _)
    have h3 : oK K C (bk.str.symm (Ideal.Quotient.mk _ (PowerSeries.C w))) = aDp l (wA l bk.a w) := h2
    rw [h3, RingHom.comp_apply, bk.ev_C, pow_zero, one_mul, sub_self]
    exact Ideal.zero_mem _
  · rw [(GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B f g).1 w, sub_self, mul_zero]
    exact dvd_zero _

theorem good_X : Good bk C n (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  obtain ⟨m, q, h1, h2⟩ := GlobalTheory.T.exists_approx_root_eisenstein_away_prime l K bk n
  exact ⟨m, q, GlobalTheory.T.approxRoot_sub_uniformizer_mem_filP l K bk C n m q h1 h2, GlobalTheory.T.breuilKisin_approxRoot_image_indep l K bk n m q h1 h2⟩

theorem good_poly (P : Polynomial (Wq l bk.a)) :
    Good bk C n (bk.str.symm (Ideal.Quotient.mk _ (P : bk.S))) := by
  induction P using Polynomial.induction_on with
  | C a => rw [Polynomial.coe_C]; exact good_C a
  | add p q hp hq => rw [Polynomial.coe_add, map_add, map_add]; exact hp.add hq
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, Polynomial.coe_mul, Polynomial.coe_X, map_mul, map_mul]
    exact h.mul good_X

theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n : ℕ) (x : ↥(OL K)), ∃ (k : ℕ) (s : bk.S), aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * C.o ((x : ↥K.1) : Om l) ∈ Per.FilP l n ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f s - BK.hf g s)) := by
  intro l _ K bk C n x
  obtain ⟨P, hP⟩ := exists_poly bk (bk.str x)
  have h := good_poly (bk := bk) (C := C) (n := n) P
  rw [hP, bk.str.symm_apply_apply] at h
  exact h

end GlobalTheory.BSP.RingHomLiftCongruence
