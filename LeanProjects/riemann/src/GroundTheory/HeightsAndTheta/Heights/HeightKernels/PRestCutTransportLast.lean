import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutTransportLast

theorem transport_X (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by
  simp [restTransport, restRename]

theorem transport_C (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by
  simp [restTransport, restRename]

theorem lastEquiv_top (j k : ℕ) (i : Fin j) (h : (i : ℕ) < k + j) :
    restLastEquiv j k ⟨i, h⟩ = Sum.inl i := by
  have : (finCongr (Nat.add_comm k j)) ⟨i, h⟩ = Fin.castAdd k i := Fin.ext rfl
  simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]

theorem lastEquiv_bottom (j k : ℕ) (i : Fin k) (h : j + (i : ℕ) < k + j) :
    restLastEquiv j k ⟨j + i, h⟩ = Sum.inr i := by
  have : (finCongr (Nat.add_comm k j)) ⟨j + i, h⟩ = Fin.natAdd j i := Fin.ext rfl
  simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]

theorem transport_yRoot (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.yRoot f k j .last τ i) =
      X (τ, Sum.inr i) := by
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, map_mul, transport_C,
    transport_X, lastEquiv_bottom]
  simp

theorem transport_zRoot (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.zRoot f k j .last τ i) =
      X (τ, Sum.inl i) := by
  simp only [RestTerms.zRoot, RestTerms.zIndex, transport_X, lastEquiv_top]

theorem map_vandermondeOf {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) {m : ℕ}
    (v : Fin m → R) : g (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf fun i => g (v i) := by
  simp only [RestTerms.vandermondeOf, map_prod, map_sub]

theorem transport_mu (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallBlockMu f k j .last) =
      smallMu f j k := by
  simp only [RestTerms.smallBlockMu, map_sum, transport_yRoot, smallMu, if_pos hk]

theorem transport_fib (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.fibreClass f k j .last) =
      fibre f j k := by
  simp only [RestTerms.fibreClass, fibre, if_pos hk, map_prod, map_mul, map_vandermondeOf,
    transport_yRoot, transport_zRoot, vandermonde, KRest.det_rev_pow_eq_vandermondeOf]

end RestCutTransportLast

open RestCutTransportLast in

theorem RestCutTransportLast.proof : RestCutTransportLast.Statement := by
  intro f j k hk
  have hn : f * (k * j) = f * j * k := by ring
  refine ⟨?_, ?_⟩
  · rw [RestTerms.restPolynomial, map_mul, map_pow, transport_mu f j k hk, transport_fib f j k hk,
      hn]
    rfl
  · rw [map_mul, map_pow, transport_mu f j k hk, transport_fib f j k hk, hn]
    rfl

end

end GroundTheory.Heights₂.Heights
