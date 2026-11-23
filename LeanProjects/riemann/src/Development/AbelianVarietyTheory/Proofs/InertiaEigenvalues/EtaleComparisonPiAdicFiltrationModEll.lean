import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPiPowEllOfNearPiStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

section Abstract

variable {O : Type} [CommRing O] {n : ℕ} {EE RA R : Type} [CommRing EE] [CommRing RA] [CommRing R]

theorem letA_dvd_of_forall_pow (p : ℕ) (a : LetA O n)
    (h : ∀ m : ℕ, ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    ∃ b : LetA O n, a = (p : LetA O n) * b := by
  have h1 : ∀ (i : ZMod n) (k : ℕ), ∃ c : O, PowerSeries.coeff k (a i) = (p : O) * c := by
    intro i k
    obtain ⟨a1, a2, h2⟩ := h (k + 1)
    refine ⟨PowerSeries.coeff k (a2 i), ?_⟩
    have h3 : a i = PowerSeries.X ^ (k + 1) * a1 i + PowerSeries.C (p : O) * a2 i := by
      rw [h2, map_natCast]; rfl
    rw [h3, map_add, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_C_mul]
  choose c hc using h1
  refine ⟨fun i => PowerSeries.mk (c i), funext fun i => PowerSeries.ext fun k => ?_⟩
  have h3 : ((p : LetA O n) * fun i => PowerSeries.mk (c i)) i =
      PowerSeries.C (p : O) * PowerSeries.mk (c i) := by
    rw [map_natCast]; rfl
  rw [h3, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem near_abstract (p : ℕ) (f : LetA O n →+* EE) (io : EE →+* R) (ι : RA →+* R) (t : R)
    (τ : RA) (hτ : ι τ = t) (ht : io (f letπ) = t) (hu : IsUnit (f letπ))
    (hd : ∀ x : EE, ∃ (a : LetA O n) (m : ℕ), x * f (letπ ^ m) - f a ∈ Ideal.span {(p : EE) ^ 1})
    (hs : ∀ a : LetA O n, f a ∈ Ideal.span {(p : EE) ^ 1} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ 1 * b)
    (key : ∀ (m : ℕ) (a : LetA O n), Near ι p t m (io (f a)) →
      ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    (∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e') ∧
    ∀ (e : EE) (r : R), io e = (p : R) * r → ∃ e' : EE, e = (p : EE) * e' := by
  have H1 : ∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e' := by
    intro m e he
    obtain ⟨a, N, h1⟩ := hd e
    rw [pow_one, Ideal.mem_span_singleton] at h1
    obtain ⟨e1, h1⟩ := h1
    have h2 : f a = f letπ ^ N * e - p * e1 := by
      rw [map_pow] at h1; linear_combination -h1
    have h3 : Near ι p t (N + m) (io (f a)) := by
      rw [h2, map_sub, map_mul, map_mul, map_pow, ht, map_natCast]
      refine Near.sub (Near.mul ?_ he) (Near.of_mul _ _)
      simpa using Near.pow_mul (ι := ι) (p := p) (t := t) N 1
    obtain ⟨a1, a2, h4⟩ := key _ _ h3
    obtain ⟨u, hu'⟩ := hu.exists_right_inv
    have h5 : f letπ ^ N * u ^ N = 1 := by rw [← mul_pow, hu', one_pow]
    refine ⟨a1, u ^ N * (e1 + f a2), ?_⟩
    rw [h4, map_add, map_mul, map_mul, map_pow, map_natCast, pow_add] at h2
    rw [map_mul, map_pow]
    linear_combination (-u ^ N) * h2 - (e - f letπ ^ m * f a1) * h5
  refine ⟨H1, fun e r he => ?_⟩
  have h1 := fun m => H1 m e (he ▸ Near.of_mul m r)
  choose a e' h2 using h1
  obtain ⟨b, hb⟩ := letA_dvd_of_forall_pow p (a 0) fun m => by
    obtain ⟨b, hb⟩ := hs (a 0 - letπ ^ m * a m) (by
      rw [pow_one, Ideal.mem_span_singleton]
      refine ⟨e' m - e' 0, ?_⟩
      have h3 := h2 0
      rw [pow_zero, one_mul] at h3
      rw [map_sub]
      linear_combination h2 m - h3)
    exact ⟨a m, b, by linear_combination hb⟩
  refine ⟨f b + e' 0, ?_⟩
  have h3 := h2 0
  rw [pow_zero, one_mul, hb, map_mul, map_natCast] at h3
  linear_combination h3

end Abstract

set_option maxHeartbeats 1000000 in

theorem near_ioE : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (m : ℕ) (e : W.EE), NearPi AI LL s m (E.tie.ioE e) → ∃ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (e' : W.EE), e = algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE (letπ ^ m * a) + (l : W.EE) * e') ∧ ∀ (e : W.EE) (r : RW LL), E.tie.ioE e = (l : RW LL) * r → ∃ e' : W.EE, e = (l : W.EE) * e' := by
  intro l _ P AI K s LL h W E
  have hd := W.EE_dense
  have hs := W.EE_sat
  rw [P.PD_p K] at hd hs
  exact near_abstract l (algebraMap _ W.EE) (E.tie.ioE : W.EE →+* RW LL)
    (inclR LL : RA LL →+* RW LL) (piR AI LL s) _ rfl (GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E).2.2.1
    W.EE_π (fun x => hd x 1) (fun a => hs a 1)
    (fun m a ha => GlobalTheory.T.mem_pi_pow_ell_of_nearPi l P AI K s LL h W E m a (E.tie.ioE_ext a ▸ ha))

end GlobalTheory.Decompl
