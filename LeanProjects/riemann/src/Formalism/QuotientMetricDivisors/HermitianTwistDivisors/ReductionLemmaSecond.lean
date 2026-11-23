import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjTransposeEqOfPosDef
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SpecDet
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DeterminantCauchySchwarz
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LcvBasis
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace Rb

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def tw (σ : K →+* ℂ) : K →+* ℂ := (starRingEnd ℂ).comp (σ.comp (starRingEnd K))

theorem tw_apply (σ : K →+* ℂ) (a : K) : tw σ a = starRingEnd ℂ (σ (star a)) := rfl

theorem tw_tw (σ : K →+* ℂ) : tw (tw σ) = σ := by
  ext a
  rw [tw_apply, tw_apply, star_star, starRingEnd_self_apply]

theorem tw_conjugate (σ : K →+* ℂ) :
    tw (ComplexEmbedding.conjugate σ) = ComplexEmbedding.conjugate (tw σ) := by
  ext a
  rw [tw_apply, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, tw_apply]

def plc (v : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (tw v.embedding)

theorem plc_plc (v : InfinitePlace K) : plc (plc v) = v := by
  unfold plc
  rcases InfinitePlace.embedding_mk_eq (tw v.embedding) with h | h
  · rw [h, tw_tw, InfinitePlace.mk_embedding]
  · rw [h, tw_conjugate, tw_tw, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

def Qd {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) (φ : K →+* ℂ) : ℂ :=
  ((P.map φ) * (H.map φ)⁻¹ * (P.map φ)ᴴ).det

theorem conjT_map_conj {m k : Type} (X : Matrix m k ℂ) :
    (X.map (starRingEnd ℂ))ᴴ = Xᴴ.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem Qd_conjugate {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (φ : K →+* ℂ) : Qd P H (ComplexEmbedding.conjugate φ) = starRingEnd ℂ (Qd P H φ) := by
  have hP : P.map (ComplexEmbedding.conjugate φ) = (P.map φ).map (starRingEnd ℂ) := by
    ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
  have hH : H.map (ComplexEmbedding.conjugate φ) = (H.map φ).map (starRingEnd ℂ) := by
    ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
  unfold Qd
  rw [hP, hH, ← R0.map_inv_field, conjT_map_conj, ← Matrix.map_mul, ← Matrix.map_mul,
    RingHom.map_det, RingHom.mapMatrix_apply]

theorem Qd_re_mk {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (φ : K →+* ℂ) : (Qd P H (InfinitePlace.mk φ).embedding).re = (Qd P H φ).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, Qd_conjugate, Complex.conj_re]

theorem Cmap {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (φ : K →+* ℂ) :
    (P * H⁻¹ * Pᴴ).map φ = (P.map φ) * (H.map φ)⁻¹ * (P.map (tw φ))ᴴ := by
  rw [Matrix.map_mul, Matrix.map_mul, R0.map_inv_field]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, tw_apply]

theorem Hmap_tw (K0 : Subfield K) (hK0 : IsCMSub K0) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (hH : ∀ i j, H i j ∈ K0) (φ : K →+* ℂ) : H.map (tw φ) = H.map φ := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, tw_apply, hK0 φ _ (hH i j), starRingEnd_self_apply]

theorem gramStd {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) :
    gram X v (fun i => (Pi.single i 1 : Fin d → K)) = metMat X v := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
  rw [majAt_eq, cv_single, cv_single, single_dot_single]

theorem gramR_std {D : ℕ} (Γ : Matrix (Fin D) (Fin D) K) :
    gramR Γ (fun i => (Pi.single i 1 : Fin D → K)) = Γ.det := by
  unfold gramR
  congr 1
  ext a b
  have hs : star (Pi.single a (1 : K) : Fin D → K) = Pi.single a 1 := by
    funext i
    by_cases h : i = a
    · subst h; simp
    · simp [h]
  rw [Matrix.of_apply, hs]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem metMat_posDef {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (hX : IsUnit (X v).det) : (metMat X v).PosDef := by
  unfold metMat
  apply Matrix.PosDef.conjTranspose_mul_self
  exact Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hX))

theorem pos_real {z : ℂ} (h : 0 < z) : z = ((z.re : ℝ) : ℂ) ∧ 0 < z.re := by
  rw [Complex.lt_def] at h
  have h1 : 0 < z.re := by simpa using h.1
  have h2 : z.im = 0 := by
    have := h.2
    simp only [Complex.zero_im] at this
    exact this.symm
  exact ⟨Complex.ext (by simp) (by simp [h2]), h1⟩

theorem Qd_place {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ : IsQuotMetric P H XQ)
    (u : InfinitePlace K) : Qd P H u.embedding = ((metMat XQ u).det)⁻¹ := by
  have hm : metMat XQ u =
      ((P.map u.embedding) * (H.map u.embedding)⁻¹ * (P.map u.embedding)ᴴ)⁻¹ := (hXQ u).2
  rw [hm, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv]
  rfl

theorem Qd_place_re {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (hXQ : IsQuotMetric P H XQ)
    (u : InfinitePlace K) :
    (Qd P H u.embedding).re = ((metMat XQ u).det.re)⁻¹ ∧ 0 < (metMat XQ u).det.re := by
  obtain ⟨hz, hr⟩ := pos_real (metMat_posDef XQ u (hXQ u).1).det_pos
  refine ⟨?_, hr⟩
  have e : ((metMat XQ u).det)⁻¹ = ((((metMat XQ u).det.re)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, ← hz]
  rw [Qd_place P H XQ hXQ u, e, Complex.ofReal_re]

theorem place_ineq (hCS : DetCS) (K0 : Subfield K) (hK0 : IsCMSub K0) {n D : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : ∀ i j, H i j ∈ K0)
    (hHpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef)
    (P : Matrix (Fin D) (Fin n) K) (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXQ : IsQuotMetric P H XQ) (hc : (P * H⁻¹ * Pᴴ).det ≠ 0) (v : InfinitePlace K) :
    (metMat XQ v).det.re * (metMat XQ (plc v)).det.re ≤
      (‖v.embedding (P * H⁻¹ * Pᴴ).det‖ ^ 2)⁻¹ := by
  have hS : ((H.map v.embedding)⁻¹).PosDef := (hHpos v).inv
  have h := hCS n D _ hS (P.map v.embedding) (P.map (tw v.embedding))
  have e1 : v.embedding (P * H⁻¹ * Pᴴ).det =
      (P.map v.embedding * (H.map v.embedding)⁻¹ * (P.map (tw v.embedding))ᴴ).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Cmap]
  have e2 : (P.map v.embedding * (H.map v.embedding)⁻¹ * (P.map v.embedding)ᴴ).det.re =
      ((metMat XQ v).det.re)⁻¹ := (Qd_place_re P H XQ hXQ v).1
  have e3 : (P.map (tw v.embedding) * (H.map v.embedding)⁻¹ * (P.map (tw v.embedding))ᴴ).det.re =
      ((metMat XQ (plc v)).det.re)⁻¹ := by
    rw [← Hmap_tw K0 hK0 H hH v.embedding, ← (Qd_place_re P H XQ hXQ (plc v)).1]
    exact (Qd_re_mk P H (tw v.embedding)).symm
  rw [← e1, e2, e3, ← mul_inv] at h
  have hr := (Qd_place_re P H XQ hXQ v).2
  have hr' := (Qd_place_re P H XQ hXQ (plc v)).2
  have ha : 0 < ‖v.embedding (P * H⁻¹ * Pᴴ).det‖ ^ 2 := by
    have : v.embedding (P * H⁻¹ * Pᴴ).det ≠ 0 := (map_ne_zero _).mpr hc
    positivity
  exact (le_inv_comm₀ ha (mul_pos hr hr')).mp h

end Rb

open Rb in

theorem lemmaRb_of (hPF : ProdFormula) (hCS : DetCS) (hLB : LcvBasis) (hIC : IdxChange)
    (hVB : ValBasic) (hGC : GramChange) (hFC : FinsumConj) : LemmaRb := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n D H hH hHpos P hP XQ hXQ M hM e he
  classical

  have hΛ : Submodule.IsLattice K (matLat P M) := by
    refine ⟨(Submodule.IsLattice.fg (self := hM)).map _, ?_⟩
    have : ((matLat P M : Submodule (𝓞 K) (Fin D → K)) : Set (Fin D → K)) =
        (Matrix.mulVecLin P) '' (M : Set (Fin n → K)) := by
      rw [matLat, Submodule.map_coe]
      rfl
    rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top (self := hM), Submodule.map_top,
      LinearMap.range_eq_top]
    exact hP

  have hli : LinearIndependent K (fun i => (Pi.single i 1 : Fin D → K)) := by
    have : (fun i => (Pi.single i 1 : Fin D → K)) = ⇑(Pi.basisFun K (Fin D)) := by
      funext i; simp [Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun K (Fin D)).linearIndependent
  obtain ⟨hfin, hlcv⟩ := hLB K D XQ (fun v => (hXQ v).1) (matLat P M) hΛ _ hli

  have hG : gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)) = (P * H⁻¹ * Pᴴ).det⁻¹ := by
    rw [gramR_std, quotGram, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hc : (P * H⁻¹ * Pᴴ).det ≠ 0 := by
    have htw0 : tw v0.embedding = v0.embedding := by
      ext a
      rw [tw_apply, hv0, starRingEnd_self_apply]
    have h0 : v0.embedding (P * H⁻¹ * Pᴴ).det = Qd P H v0.embedding := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Cmap, htw0]
      rfl
    rw [Qd_place P H XQ hXQ v0] at h0
    have hne : ((metMat XQ v0).det)⁻¹ ≠ 0 :=
      inv_ne_zero (metMat_posDef XQ v0 (hXQ v0).1).det_pos.ne'
    intro hz
    rw [hz, map_zero] at h0
    exact hne h0.symm
  have hG0 : gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)) ≠ 0 := by
    rw [hG]; exact inv_ne_zero hc
  obtain ⟨hGfin, hGpf⟩ := hPF K _ hG0

  have hpt : ∀ v : InfinitePlace K,
      Real.log (metMat XQ v).det.re + Real.log (metMat XQ (plc v)).det.re ≤
        2 * Real.log ‖v.embedding (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)))‖ := by
    intro v
    have hr := (Qd_place_re P H XQ hXQ v).2
    have hr' := (Qd_place_re P H XQ hXQ (plc v)).2
    have hi := place_ineq hCS K0 hK0 H hH hHpos P XQ hXQ hc v
    have e2 : 2 * Real.log ‖v.embedding (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)))‖ =
        Real.log ((‖v.embedding (P * H⁻¹ * Pᴴ).det‖ ^ 2)⁻¹) := by
      rw [hG, map_inv₀, norm_inv, Real.log_inv, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [e2, ← Real.log_mul hr.ne' hr'.ne']
    exact Real.log_le_log (mul_pos hr hr') hi
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hpt v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hperm : ∑ v : InfinitePlace K, Real.log (metMat XQ (plc v)).det.re =
      ∑ v : InfinitePlace K, Real.log (metMat XQ v).det.re :=
    Equiv.sum_comp (Function.Involutive.toPerm _ plc_plc) (fun v => Real.log (metMat XQ v).det.re)
  rw [hperm] at hsum
  have hmean : ∑ v, Real.log (gram XQ v (fun i => (Pi.single i 1 : Fin D → K))).det.re ≤
      ∑ v : InfinitePlace K,
        Real.log ‖v.embedding (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)))‖ := by
    simp only [gramStd]
    linarith
  have hinf : (2 / (finrank ℚ K : ℝ)) *
      ∑ v, Real.log (gram XQ v (fun i => (Pi.single i 1 : Fin D → K))).det.re ≤
      ∑ᶠ w, lw w * (vw w (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K))) : ℝ) := by
    rw [← hGpf]
    exact mul_le_mul_of_nonneg_left hmean (by positivity)

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      lw w * (vw w (gramR (quotGram P H) (e w)) : ℝ) =
        lw w * (vw w (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K))) : ℝ) +
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) +
        lw (conjPl w) * (idx (conjPl w)
          (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) := by
    intro w
    obtain ⟨hmul, hstar, hlw, -, -, -, -⟩ := hVB K w
    let γ : Matrix (Fin D) (Fin D) K := Matrix.of fun k i => e w i k
    have hew : (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin D → K)) = e w := by
      funext i j
      simp [γ, Finset.sum_apply, Pi.single_apply]
    have hdet : γ.det ≠ 0 := by
      have hu : IsUnit (Matrix.of (e w)) :=
        Matrix.linearIndependent_rows_iff_isUnit.mp (he w).1
      have : γ = (Matrix.of (e w))ᵀ := by ext k i; rfl
      rw [this, Matrix.det_transpose]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hlb : IsLocBasis (matLat P M) w (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin D → K)) := by
      rw [hew]; exact he w
    obtain ⟨hi1, hi2⟩ := hIC K D (matLat P M) hΛ _ hli w γ hlb
    have hgc : gramR (quotGram P H) (e w) =
        star γ.det * γ.det * gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K)) := by
      rw [← hew]
      exact hGC K D D _ _ γ
    rw [hgc, hmul _ _ (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hG0,
      hmul _ _ (star_ne_zero.mpr hdet) hdet, hstar, hi1, hi2, hlw]
    push_cast
    ring
  have hinj : Function.Injective (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K)) :=
    fun a b h => by rw [← (hVB K a).2.2.2.1, h, (hVB K b).2.2.2.1]
  have hfc : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw (conjPl w) * (idx (conjPl w)
      (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K)))) (matLat P M) : ℝ)).Finite :=
    hfin.preimage hinj.injOn
  have hfun : (fun w => lw w * (vw w (gramR (quotGram P H) (e w)) : ℝ)) = fun w =>
      lw w * (vw w (gramR (quotGram P H) (fun i => (Pi.single i 1 : Fin D → K))) : ℝ) +
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) +
        lw (conjPl w) * (idx (conjPl w)
          (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K))))
          (matLat P M) : ℝ) := funext hloc
  have hfin2 := (hGfin.union hfin).subset (Function.support_add _ _)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hfin2.union hfc).subset (Function.support_add _ _)
  · rw [hfun, finsum_add_distrib hfin2 hfc, finsum_add_distrib hGfin hfin,
      hFC K (fun w => lw w * (idx w
        (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin D → K)))) (matLat P M) : ℝ)),
      hlcv]
    linarith [hinf]

theorem reduction_lemma_second : LemmaRb :=
  lemmaRb_of prod_formula' determinant_cauchy_schwarz covolume_via_basis index_change_formula valuation_basic_properties
    gram_matrix_change finite_sum_conjugation

end Formalism.DivisionValues
