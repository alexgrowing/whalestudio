import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

open Formalism.BasicNotions IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.HermAdelicNorm

theorem congr_of_hasSignature {c p q : ℕ} {J J' : Matrix (Fin c) (Fin c) ℂ}
    (h : Formalism.UG.HasSignature J p q) (h' : Formalism.UG.HasSignature J' p q) :
    ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧ J' = Qᵀ * J * Q.map conj := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  set R : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P * P'⁻¹).val with hR
  have hRP : R * P'.val = P.val := by
    rw [hR, ← Units.val_mul, inv_mul_cancel_right]
  have h1 : Formalism.UG.cT (starRingEnd ℂ) R * J.reindex e e * R = J'.reindex e' e' := by
    have hu : IsUnit (Formalism.UG.cT (starRingEnd ℂ) (P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Formalism.UG.cT, Matrix.det_transpose,
        show ((P' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ)).det = _ from
          (RingHom.map_det (starRingEnd ℂ) _).symm]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 P'.isUnit).map _
    refine hu.mul_left_cancel (P'.isUnit.mul_right_cancel ?_)
    rw [hP', ← hP, ← hRP, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  let S : Matrix (Fin c) (Fin c) ℂ := R.submatrix e e'
  have hS : S.det ≠ 0 := by
    have : S * (P * P'⁻¹)⁻¹.val.submatrix e' e = 1 := by
      rw [Matrix.submatrix_mul_equiv, hR, Units.mul_inv, Matrix.submatrix_one_equiv]
    exact (Matrix.isUnit_det_of_right_inverse this).ne_zero
  refine ⟨S.map conj, ?_, ?_⟩
  · rw [show (S.map conj).det = _ from (RingHom.map_det (starRingEnd ℂ) _).symm]
    exact (map_ne_zero _).2 hS
  · have h2 : (S.map conj).map conj = S := by
      ext a b
      simp
    have h3 : J' = (J'.reindex e' e').submatrix e' e' := by simp
    have h4 : J = (J.reindex e e).submatrix e e := by simp
    rw [h2, h3, ← h1]
    conv_rhs => rw [h4]
    rw [← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e]
    rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_coord (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  have h2 : star (2 : E) = 2 := star_ofNat 2
  obtain ⟨a, ha⟩ := (cm.fixed ((x + star x) / 2)).1 (by
    rw [star_div₀, star_add, star_star, h2, add_comm])
  obtain ⟨b, hb⟩ := (cm.fixed ((x - star x) / (2 * θ))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', h2, hθ]
    field_simp
    ring)
  refine ⟨a, b, ?_⟩
  rw [ha, hb]
  field_simp
  ring

theorem exists_sq_sub (cm : CMData F E) {θ : E} (h0 : θ ≠ 0) (hθ : star θ = -θ) {d a : F}
    (hd : algebraMap F E d = θ * θ) (R : Type) [CommRing R] [Algebra F R] (y : E ⊗[F] R)
    (hy : Formalism.UG.sigR cm.sig R y * y = Formalism.UG.inclE R (algebraMap F E a)) :
    ∃ u w : R, algebraMap F R a = u ^ 2 - algebraMap F R d * w ^ 2 := by
  obtain ⟨u, w, rfl⟩ : ∃ u w : R, y = (1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w := by
    clear hy
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul x r =>
      obtain ⟨s, t, rfl⟩ := exists_coord cm h0 hθ x
      refine ⟨s • r, t • r, ?_⟩
      rw [TensorProduct.add_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        Algebra.smul_def, Algebra.smul_def, mul_one]
    | add x y hx hy =>
      obtain ⟨u, w, rfl⟩ := hx
      obtain ⟨u', w', rfl⟩ := hy
      exact ⟨u + u', w + w', by simp only [TensorProduct.tmul_add]; ring⟩
  refine ⟨u, w, Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := R)
    (algebraMap F E).injective ?_⟩
  have h1 : Formalism.UG.sigR cm.sig R ((1 : E) ⊗ₜ[F] u + θ ⊗ₜ[F] w) =
      (1 : E) ⊗ₜ[F] u - θ ⊗ₜ[F] w := by
    rw [map_add]
    change (star (1 : E)) ⊗ₜ[F] u + (star θ) ⊗ₜ[F] w = _
    rw [star_one, hθ, TensorProduct.neg_tmul, sub_eq_add_neg]
  have h2 : ∀ s : F, ∀ r : R, (algebraMap F E s) ⊗ₜ[F] r = (1 : E) ⊗ₜ[F] (algebraMap F R s * r) := by
    intro s r
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have h3 : Formalism.UG.inclE (F := F) R (algebraMap F E a) = (1 : E) ⊗ₜ[F] (algebraMap F R a) := by
    rw [← mul_one (algebraMap F R a), ← h2]
    rfl
  rw [h1, h3] at hy
  simp only [Algebra.TensorProduct.includeRight_apply]
  rw [← hy, TensorProduct.tmul_sub, ← h2, hd, pow_two, pow_two,
    ← Algebra.TensorProduct.tmul_mul_tmul]
  rw [show ((1 : E) ⊗ₜ[F] (u * u) : E ⊗[F] R) = (1 : E) ⊗ₜ[F] u * (1 : E) ⊗ₜ[F] u by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
  ring

theorem congr_of_signature_of_adelic_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (c : ℕ) (G G' : Matrix (Fin c) (Fin c) E), Gᴴ = G → G'ᴴ = G' → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) → (∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = Formalism.UG.inclE (FiniteAdeleRing (𝓞 F) F) (G.det / G'.det)) → ∃ P : Matrix (Fin c) (Fin c) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  intro F E _ _ _ _ _ _ cm c G G' hG hG' hd hd' hs ⟨y, hy⟩
  haveI := cm.totReal
  haveI := cm.cmUnram.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (cm.cmUnram.2.1 τ x).symm)
  have hH : ∀ {M : Matrix (Fin c) (Fin c) E}, Mᴴ = M →
      ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (M a b) = M b a := fun h a b => by
    rw [hcc]
    exact congrFun (congrFun h b) a
  have hs' : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin c) (Fin c) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj := fun τ => by
    obtain ⟨p, q, h, h'⟩ := hs τ
    exact congr_of_hasSignature h h'
  obtain ⟨a, ha⟩ := (cm.fixed (G.det / G'.det)).1 (by
    rw [star_div₀, ← Matrix.det_conjTranspose, ← Matrix.det_conjTranspose, hG, hG'])
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  rw [hcc] at hθ
  obtain ⟨d, hdθ⟩ := (cm.fixed (θ * θ)).1 (by rw [star_mul', hθ]; ring)
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hdθ, h, map_zero])
  have ha0 : a ≠ 0 := fun h => div_ne_zero hd hd' (by rw [← ha, h, map_zero])
  obtain ⟨u, w, huw⟩ := exists_sq_sub cm h0 hθ hdθ _ y (hy.trans (by rw [ha]))
  obtain ⟨s, t, hst⟩ := GlobalTheory.QNorm.hasseNormSt F d a hd0 ha0
    (fun ρ => by
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
      have h1 : τ (algebraMap F E a) = (Complex.ofRealHom.comp ρ) a :=
        ComplexEmbedding.lift_algebraMap_apply E _ a
      have h2 : 0 < (τ (G.det / G'.det)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd τ (hs' τ)
      rw [← ha, h1] at h2
      exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
    (fun v => by
      let ev : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
        RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) v
      have h1 := congrArg ev huw
      rw [map_sub, map_mul, map_pow, map_pow] at h1
      exact ⟨ev u, ev w, h1⟩)
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E c G G'
    (hH hG) (hH hG') hd hd' hs' ⟨algebraMap F E s + algebraMap F E t * θ, by
      have hf : ∀ z : F, star (algebraMap F E z) = algebraMap F E z :=
        fun z => (cm.fixed _).2 ⟨z, rfl⟩
      rw [hcc, star_add, star_mul', hf, hf, hθ, ← ha, hst, map_sub, map_mul, map_pow, map_pow, hdθ]
      ring⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [hPG]
    congr 2
    ext a b
    simp [hcc]

end GlobalTheory.HermAdelicNorm
