import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutTransportFirst

theorem map_vandermondeOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf (fun i => φ (v i)) := by
  simp [RestTerms.vandermondeOf, map_prod, map_sub]

theorem transport_X (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by
  simp [restTransport, restRename]

theorem transport_C (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by
  simp [restTransport, restRename]

theorem transport_yRoot (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.yRoot f j k .first τ i) =
      -X (τ, Sum.inl i) := by
  have h : (⟨i.val, by have := i.isLt; omega⟩ : Fin (j + k)) = Fin.castAdd k i := Fin.ext rfl
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, map_mul, transport_C,
    transport_X, h, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]
  simp

theorem transport_zRoot (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.zRoot f j k .first τ i) =
      X (τ, Sum.inr i) := by
  have h : (⟨j + i.val, by have := i.isLt; omega⟩ : Fin (j + k)) = Fin.natAdd j i := Fin.ext rfl
  simp only [RestTerms.zRoot, RestTerms.zIndex, transport_X, h, restFirstEquiv,
    finSumFinEquiv_symm_apply_natAdd]

theorem transport_mu (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallBlockMu f j k .first) =
      smallMu f j k := by
  have hkj : ¬ k ≤ j := by omega
  simp only [RestTerms.smallBlockMu, map_sum, transport_yRoot, smallMu, if_neg hkj]

theorem transport_fib (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.fibreClass f j k .first) =
      fibre f j k := by
  have hkj : ¬ k ≤ j := by omega
  simp only [RestTerms.fibreClass, map_prod, map_mul, map_vandermondeOf, transport_yRoot,
    transport_zRoot, fibre, if_neg hkj, vandermonde, KRest.det_rev_pow_eq_vandermondeOf]

end RestCutTransportFirst

theorem RestCutTransportFirst.proof : RestCutTransportFirst.Statement := by
  intro f j k hjk
  have hn : f * (j * k) = f * j * k := (Nat.mul_assoc f j k).symm
  refine ⟨?_, ?_⟩
  · rw [RestTerms.restPolynomial, map_mul, map_pow, RestCutTransportFirst.transport_mu f j k hjk,
      RestCutTransportFirst.transport_fib f j k hjk, restInput, hn]
  · rw [map_mul, map_pow, RestCutTransportFirst.transport_mu f j k hjk,
      RestCutTransportFirst.transport_fib f j k hjk, degreeInput, hn]

end

end GroundTheory.Heights₂.Heights
