import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.ChartGram

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_halfR (σ : E →ₐ[F] E) : sigR R σ (halfR (F := F) (E := E) R) = halfR (F := F) (E := E) R := by
  unfold halfR
  rw [sigR_inclR, AlgHom.commutes]

theorem halfR_add_halfR (h2 : (2 : F) ≠ 0) :
    halfR (F := F) (E := E) R + halfR (F := F) (E := E) R = 1 := by
  have h : (1 / 2 : F) + 1 / 2 = 1 := by field_simp; norm_num
  unfold halfR
  rw [← map_add, ← map_add, h, map_one, map_one]

theorem vH_zero {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 0 = a := rfl
theorem vH_one {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : vH a s Y 1 = s := rfl
theorem tailH_vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : tailH (vH a s Y) = Y := rfl

theorem hR_hypOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin (M + 2) → R ⊗[F] E) :
    hR R σ (hypOne J) x y =
      sigR R σ (x 0) * y 1 + sigR R σ (x 1) * y 0 + hR R σ J (tailH x) (tailH y) := by
  unfold hR hform JR tailH
  simp only [Fin.sum_univ_succ, Matrix.map_apply, Fin.succ_zero_eq_one, hypOne_zero_zero, hypOne_zero_one,
    hypOne_one_zero, hypOne_one_one, hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one,
    hypOne_rest_rest, map_zero, map_one, mul_zero, zero_mul, mul_one, Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem sigR_hR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  unfold hR hform JR
  simp only [map_sum, map_mul, sigR_sigR R σ hσ, Matrix.map_apply, sigR_inclR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]
  ring

theorem hR_comb_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (x u w : Fin M → R ⊗[F] E) :
    hR R σ J x (fun i => c * u i + w i) = c * hR R σ J x u + hR R σ J x w := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_comb_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : R ⊗[F] E)
    (u w y : Fin M → R ⊗[F] E) :
    hR R σ J (fun i => c * u i + w i) y = sigR R σ c * hR R σ J u y + hR R σ J w y := by
  unfold hR hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, map_add, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_tHalf (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin (M + 2) → R ⊗[F] E) :
    sigR R σ (tHalf R σ J x) = tHalf R σ J x := by
  unfold tHalf
  rw [map_mul, sigR_halfR, hR_hypOne, map_add, map_add, map_mul, map_mul, sigR_sigR R σ hσ, sigR_sigR R σ hσ,
    sigR_hR R σ hσ J hJ]
  ring

theorem hR_cvec_right (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x v : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) x (cvec R σ J x v) = v 1 + tHalf R σ J x * v 0 := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have ht : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  rw [hR_hypOne, ht, hR_comb_right]
  simp only [cvec, vH_zero, vH_one]
  linear_combination (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)) * e1 - v 0 * e3 - v 0 * e4

theorem hR_cvec_cvec (h2 : (2 : F) ≠ 0) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (x v w : Fin (M + 2) → R ⊗[F] E) (hu : IsUnit (x 0)) :
    hR R σ (hypOne J) (cvec R σ J x v) (cvec R σ J x w) = hR R σ (hypOne J) v w := by
  have e1 : Ring.inverse (sigR R σ (x 0)) * sigR R σ (x 0) = 1 :=
    Ring.inverse_mul_cancel _ (hu.map (sigR R σ))
  have e2 : sigR R σ (Ring.inverse (sigR R σ (x 0))) * x 0 = 1 := by
    have := congrArg (sigR R σ) e1
    rwa [map_mul, sigR_sigR R σ hσ, map_one] at this
  have e3 : tHalf R σ J x + tHalf R σ J x = hR R σ (hypOne J) x x := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  have e4 := hR_hypOne R σ J x x
  have htv : tailH (cvec R σ J x v) = fun i => v 0 * tailH x i + tailH v i := rfl
  have htw : tailH (cvec R σ J x w) = fun i => w 0 * tailH x i + tailH w i := rfl
  rw [hR_hypOne, hR_hypOne R σ J v w, htv, htw, hR_comb_left, hR_comb_right, hR_comb_right]
  simp only [cvec, vH_zero, vH_one, map_add, map_sub, map_mul, sigR_tHalf R σ hσ J hJ,
    sigR_hR R σ hσ J hJ]
  linear_combination
    (sigR R σ (v 0) * (w 1 - tHalf R σ J x * w 0 - hR R σ J (tailH x) (tailH w))) * e1 +
    (w 0 * (sigR R σ (v 1) - tHalf R σ J x * sigR R σ (v 0) - hR R σ J (tailH v) (tailH x))) * e2 -
    sigR R σ (v 0) * w 0 * e3 - sigR R σ (v 0) * w 0 * e4

end Alg

theorem gramR_chartS : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 0 = hR R σ (hypOne J) (x 0) (x 0) ∧ (∀ j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 j.succ = s 0 j) ∧ ∀ i j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) i.succ j.succ = gramR R σ J Y i j + (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j - hR R σ (hypOne J) (x 0) (x 0) * (sigR R σ (a 0 i) * a 0 j)) := by
  intro F E _ _ _ _ _ σ hc M J hJ R _ _ n x a s Y hu
  have hσ := sig_invol σ hc
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have e3 : tHalf R σ J (x 0) + tHalf R σ J (x 0) = hR R σ (hypOne J) (x 0) (x 0) := by
    unfold tHalf
    rw [← add_mul, halfR_add_halfR R h2, one_mul]
  refine ⟨rfl, fun j => ?_, fun i j => ?_⟩
  · change hR R σ (hypOne J) (x 0) (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = s 0 j
    rw [hR_cvec_right R h2 σ J _ _ hu, vH_zero, vH_one]
    ring
  · change hR R σ (hypOne J) (cvec R σ J (x 0) (vH (a 0 i) (s 0 i - tHalf R σ J (x 0) * a 0 i) (Y i)))
      (cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))) = hR R σ J (Y i) (Y j) + _
    rw [hR_cvec_cvec R h2 σ hσ J hJ.1 _ _ _ hu, hR_hypOne]
    simp only [vH_zero, vH_one, tailH_vH, map_sub, map_mul, sigR_tHalf R σ hσ J hJ.1]
    linear_combination (-(sigR R σ (a 0 i) * a 0 j)) * e3

end GlobalTheory.CompanionTheory.WeilSiegel.ChartGram
