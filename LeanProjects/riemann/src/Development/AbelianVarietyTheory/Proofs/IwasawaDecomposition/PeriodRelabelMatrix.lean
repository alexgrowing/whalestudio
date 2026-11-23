import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RelabBijective
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.ShFam.PerDet

def revIdx {m n r : ℕ} (hr : m + n = r) : Fin m ⊕ Fin n ≃ Fin r :=
  (Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans (finSumFinEquiv.trans (finCongr hr))

theorem revIdx_inl {m n r : ℕ} (hr : m + n = r) (i : Fin m) : ((revIdx hr (Sum.inl i) : Fin r) : ℕ) = m - 1 - i := by
  simp [revIdx]; omega

theorem revIdx_inr {m n r : ℕ} (hr : m + n = r) (i : Fin n) : ((revIdx hr (Sum.inr i) : Fin r) : ℕ) = m + i := by
  simp [revIdx]

theorem horVal_frame {m n r : ℕ} (hr : m + n = r) (y : Matrix (Fin r) (Fin r) ℂ) (hy : y.det ≠ 0)
    (B : Matrix (Fin r) (Fin m ⊕ Fin n) ℂ) (B' : Matrix (Fin m ⊕ Fin n) (Fin r) ℂ) (hB : B * B' = 1)
    (t : ℂ) (ht : t ≠ 0) (K : Matrix (Fin m ⊕ Fin n) (Fin m) ℂ)
    (hK : ∀ a i, (B * K) a i = -t⁻¹ * y a (revIdx hr (Sum.inl i)))
    (C : Matrix (Fin n) (Fin m ⊕ Fin n) ℂ) (hC : ∀ i k, C i k = (y⁻¹ * B) (revIdx hr (Sum.inr i)) k) :
    horVal K C = (-t) ^ m * (B.submatrix (revIdx hr) id).det * y.det⁻¹ := by
  set e := revIdx hr
  have hu : IsUnit y.det := hy.isUnit
  have hyy : y⁻¹ * y = 1 := Matrix.nonsing_inv_mul _ hu
  set Y := y⁻¹ * B with hY
  have hYK : ∀ a i, (Y * K) a i = -t⁻¹ * (1 : Matrix (Fin r) (Fin r) ℂ) a (e (Sum.inl i)) := by
    intro a i
    rw [hY, Matrix.mul_assoc, Matrix.mul_apply]
    simp only [hK, ← hyy, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by ring
  have hYB : Y * (B' * y) = 1 := by
    rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB, Matrix.one_mul, hyy]
  let R : Matrix (Fin m) (Fin m ⊕ Fin n) ℂ := Matrix.of fun i k => -t * Y (e (Sum.inl i)) k
  let S : Matrix (Fin m ⊕ Fin n) (Fin n) ℂ := Matrix.of fun k i => (B' * y) k (e (Sum.inr i))
  have h0 : C * K = 0 := by
    ext i j
    have : (C * K) i j = (Y * K) (e (Sum.inr i)) j := by
      simp only [Matrix.mul_apply, hC]
    rw [this, hYK, Matrix.one_apply_ne (fun h => by simpa using e.injective h)]
    simp
  have hR : R * K = 1 := by
    ext i j
    have : (R * K) i j = -t * (Y * K) (e (Sum.inl i)) j := by
      simp only [R, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]
    rw [this, hYK]
    by_cases hij : i = j
    · subst hij; simp [ht]
    · rw [Matrix.one_apply_ne (fun h => hij (by simpa using e.injective h)), Matrix.one_apply_ne hij]; simp
  have hS : C * S = 1 := by
    ext i j
    have : (C * S) i j = (Y * (B' * y)) (e (Sum.inr i)) (e (Sum.inr j)) := by
      simp only [S, Matrix.mul_apply, Matrix.of_apply, hC]
    rw [this, hYB]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne (fun h => hij (by simpa using e.injective h)), Matrix.one_apply_ne hij]
  rw [horVal_eq h0 hR hS]
  have hF : Matrix.fromRows R C =
      Matrix.diagonal (Sum.elim (fun _ => -t) (fun _ => 1)) * (y⁻¹.submatrix e e * B.submatrix e id) := by
    rw [Matrix.submatrix_mul_equiv, ← hY]
    ext s k
    rcases s with i | i <;> simp [R, hC, Matrix.diagonal_mul]
  rw [hF, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_submatrix_equiv_self, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', Fintype.prod_sum_type]
  simp
  ring

theorem det_submatrix_ne_zero {m n r : ℕ} (hr : m + n = r) (B : Matrix (Fin r) (Fin m ⊕ Fin n) ℂ)
    (B' : Matrix (Fin m ⊕ Fin n) (Fin r) ℂ) (hB : B * B' = 1) : (B.submatrix (revIdx hr) id).det ≠ 0 := by
  have : B.submatrix (revIdx hr) id * B'.submatrix id (revIdx hr) = 1 := by
    have h := Matrix.submatrix_mul_equiv B B' (revIdx hr) (Equiv.refl (Fin m ⊕ Fin n)) (revIdx hr)
    rw [hB, Matrix.submatrix_one_equiv] at h
    exact h
  exact left_ne_zero_of_mul_eq_one (by rw [← Matrix.det_mul, this, Matrix.det_one])

end GlobalTheory.ShFam.PerDet

namespace GlobalTheory.ShFam.PerDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem mult_of (Dw : Datum H) (τ : E →+* ℂ) (hτr : τ (H.rt : E) = H.rt0) :
    Dw.mult τ = Dw.p ∧ Dw.mult (conjEmb τ) = Dw.q ∧ conjEmb τ (H.rt : E) ≠ H.rt0 := by
  have hne : conjEmb τ (H.rt : E) ≠ H.rt0 := by
    intro h
    have h' : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h
    rw [hτr] at h'
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h'
    have hsq := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (2:ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    simp [pow_two, Complex.mul_re, him] at hsq
    nlinarith [sq_nonneg H.rt0.re]
  refine ⟨?_, ?_, hne⟩
  · rw [Datum.mult, if_pos hτr]
  · rw [Datum.mult, if_neg hne]

theorem hm_eq {r : ℕ} (X : Data E r) (Di : Datum H) (φ : Di.La ≃ₗ[𝓞 E] X.Λ) {J : Type} [Fintype J] [DecidableEq J]
    (x : J → Di.La) (hm : Matrix J J E)
    (hEF : ∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (hx : IsPerBasis Di x hm) (k k' : J) :
    hm k k' = -X.ξ0 * herm X.Gm (φ (x k) : Fin r → E) (φ (x k')) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.ShFam.HorIso.eq_zero_of_trace _ fun a => ?_
  have h1 := hx.2.2.1 a k k'
  rw [hEF, map_smul] at h1
  have h2 : herm X.Gm ((a • φ (x k) : X.Λ) : Fin r → E) (φ (x k')) =
      (a : E) * herm X.Gm (φ (x k) : Fin r → E) (φ (x k')) := by
    simp only [herm, Submodule.coe_smul, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    rw [Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap]; ring
  rw [h2] at h1
  rw [mul_sub, map_sub, ← h1, show -X.ξ0 * ((a : E) * herm X.Gm (φ (x k) : Fin r → E) (φ (x k'))) =
    (a : E) * (-X.ξ0 * herm X.Gm (φ (x k) : Fin r → E) (φ (x k'))) by ring, sub_self]

theorem perFr_conj {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) (v : Fin r → E) (T : E →+* ℂ) (hT : T ∈ X.Ψ)
    (hT' : conjEmb T ∉ X.Ψ) (i : ℕ) (hi : X.p0 - 1 - i < r) :
    Formalism.L2.PjFree.perFr X y v (conjEmb T) i =
      hermC T X.Gm (col (mat y ⟨T, hT⟩) ⟨X.p0 - 1 - i, hi⟩) (Data.emb T v) := by
  have hcc : conjEmb (conjEmb T) = T := by ext a; simp [conjEmb]
  have key : ∀ (ρ₁ ρ₂ : E →+* ℂ) (_ : ρ₁ = ρ₂) (h1 : ρ₁ ∈ X.Ψ) (h2 : ρ₂ ∈ X.Ψ),
      hermC ρ₁ X.Gm (col (mat y ⟨ρ₁, h1⟩) ⟨X.p0 - 1 - i, hi⟩) (Data.emb ρ₁ v) =
        hermC ρ₂ X.Gm (col (mat y ⟨ρ₂, h2⟩) ⟨X.p0 - 1 - i, hi⟩) (Data.emb ρ₂ v) := by
    rintro _ _ rfl _ _; rfl
  rw [Formalism.L2.PjFree.perFr, dif_neg hT', dif_pos (by rw [hcc]; exact hT : conjEmb (conjEmb T) ∈ X.Ψ), dif_pos hi]
  exact key _ _ hcc _ _

theorem perFr_self {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) (v : Fin r → E) (T : E →+* ℂ) (hT : T ∈ X.Ψ)
    (i : ℕ) (hi : X.p0 + i < r) :
    Formalism.L2.PjFree.perFr X y v T i = ((mat y ⟨T, hT⟩)⁻¹.mulVec (Data.emb T v)) ⟨X.p0 + i, hi⟩ := by
  rw [Formalism.L2.PjFree.perFr, dif_pos hT, dif_pos hi]

end GlobalTheory.ShFam.PerDet

namespace GlobalTheory.ShFam.PerDet

theorem perVal_eq_horizGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (X : Data E r) (Di : Datum H) (τ : E →+* ℂ) (hτ : Formalism.L2.PjFree.relab c σ τ ∈ X.Ψ) (φ : Di.La ≃ₗ[𝓞 E] X.Λ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), r = Dw.p + Dw.q → X.p0 = Dw.q → τ (H.rt : E) = H.rt0 → (∀ ρ : E →+* ℂ, Formalism.L2.PjFree.relab c σ ρ ∈ X.Ψ ↔ ρ (H.rt : E) = H.rt0) → (∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → IsPerBasis Di x hm → ∃ b : ℂ, b ≠ 0 ∧ ∀ y ∈ X.dom, ∀ Q : Di.La →+ (Letter Dw → ℂ), (∀ v (z : Letter Dw), Q v z = Formalism.L2.PjFree.perFr X y (φ v : Fin r → E) (Formalism.L2.PjFree.relab c σ z.1) z.2) → perVal c σ τ x hm Q = b * GlobalTheory.FlatLine.horizGen ⟨_, hτ⟩ y := by
  intro E _ _ _ H Dw l c σ r X Di τ hτ φ x hm hr hp0 hτr hΨ hEF hx
  obtain ⟨h1, h2, hne⟩ := mult_of Dw τ hτr
  have hmn : Dw.mult (conjEmb τ) + Dw.mult τ = r := by rw [h1, h2, hr]; omega
  have hm0 : Dw.mult (conjEmb τ) = X.p0 := by rw [h2, hp0]
  set T := Formalism.L2.PjFree.relab c σ τ with hT
  have hT' : conjEmb T ∉ X.Ψ := by
    rw [hT, ← GlobalTheory.UnifDataTest.relab_conj, hΨ]; exact hne
  set t := T X.ξ0 with ht_def
  have ht : t ≠ 0 := (map_ne_zero T).2 X.ξ0_ne
  set B : Matrix (Fin r) (Idx Dw τ) ℂ := Matrix.of fun a k => T ((φ (x k) : Fin r → E) a) with hB_def
  set N : Matrix (Idx Dw τ) (Fin r) ℂ := Matrix.of fun k a => ∑ b, starRingEnd ℂ (B b k) * T (X.Gm a b) with hN_def
  have hTm : (hm.map T)ᵀ = -t • (N * B) := by
    ext k' k
    simp only [Matrix.transpose_apply, Matrix.map_apply, hm_eq X Di φ x hm hEF hx, herm, cc, map_mul, map_neg,
      map_sum, IsCMField.complexEmbedding_complexConj, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, hN_def,
      hB_def, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [← ht_def]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  set L := ((hm.map T)ᵀ)⁻¹ with hL
  have hdet : IsUnit ((hm.map T)ᵀ).det := by
    rw [Matrix.det_transpose, show (hm.map T).det = T hm.det from (RingHom.map_det T hm).symm]; exact ((map_ne_zero T).2 hx.2.2.2).isUnit
  have hLN : (-t • (L * N)) * B = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.mul_smul, ← hTm, hL, Matrix.nonsing_inv_mul _ hdet]
  have hB : B * (-t • (L * N)) = 1 := (Matrix.mul_eq_one_comm_of_equiv (revIdx hmn)).1 hLN
  refine ⟨(-t) ^ Dw.mult (conjEmb τ) * (B.submatrix (revIdx hmn) id).det,
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 ht)) (det_submatrix_ne_zero hmn B _ hB), ?_⟩
  intro y hy Q hQ
  have hydet : (mat y ⟨T, hτ⟩).det ≠ 0 := (hy ⟨T, hτ⟩).1
  rw [GlobalTheory.FlatLine.horizGen, perVal]
  rw [horVal_frame hmn (mat y ⟨T, hτ⟩) hydet B _ hB t ht]
  · have hP : (perMat x Q (conjEmb τ))ᵀ = N * Matrix.of (fun a (i : Fin (Dw.mult (conjEmb τ))) =>
        mat y ⟨T, hτ⟩ a (revIdx hmn (Sum.inl i))) := by
      ext k i
      have hi : X.p0 - 1 - (i : ℕ) < r := by omega
      have he : revIdx hmn (Sum.inl i) = ⟨X.p0 - 1 - i, hi⟩ := Fin.ext (by rw [revIdx_inl]; simp only; omega)
      have hc := perFr_conj X y (φ (x k) : Fin r → E) T hτ hT' i hi
      rw [← GlobalTheory.UnifDataTest.relab_conj] at hc
      simp only [Matrix.transpose_apply, perMat, Matrix.of_apply, hQ]
      rw [hc, ← he]
      simp only [hermC, col, Data.emb, Matrix.mul_apply, hN_def, hB_def, Matrix.of_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hBLN : B * (L * N) = (-t)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      have h := congrArg ((-t)⁻¹ • ·) hB
      simp only [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 ht), one_smul] at h
      exact h
    intro a i
    rw [kerMat, ← hL, hP, ← Matrix.mul_assoc L N, ← Matrix.mul_assoc B, hBLN, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, neg_inv]
  · intro i k
    have hi : X.p0 + (i : ℕ) < r := by omega
    have he : revIdx hmn (Sum.inr i) = ⟨X.p0 + i, hi⟩ := Fin.ext (by rw [revIdx_inr]; simp only; omega)
    have hs := perFr_self X y (φ (x k) : Fin r → E) T hτ i hi
    simp only [perMat, Matrix.of_apply, hQ]
    rw [hs, he]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, hB_def, Data.emb, Matrix.of_apply]

end GlobalTheory.ShFam.PerDet
