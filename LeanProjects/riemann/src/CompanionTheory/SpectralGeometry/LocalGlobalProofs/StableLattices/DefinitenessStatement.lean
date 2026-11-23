import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometry
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter Matrix
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DefiniteForm

open CompanionTheory.Rg.Fl

theorem cT_congr {R : Type} [CommRing R] (s : R →+* R) {n : ℕ}
    (Q Qi D J J' Δ : Matrix (Fin n) (Fin n) R) (hQ : Q * Qi = 1)
    (h1 : Formalism.UG.cT s Q * J * Q = Δ) (h2 : Formalism.UG.cT s D * J' * D = Δ) :
    Formalism.UG.cT s (D * Qi) * J' * (D * Qi) = J := by
  calc Formalism.UG.cT s (D * Qi) * J' * (D * Qi)
      = Formalism.UG.cT s Qi * (Formalism.UG.cT s D * J' * D) * Qi := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT s Qi * (Formalism.UG.cT s Q * J * Q) * Qi := by rw [h1, h2]
    _ = Formalism.UG.cT s (Q * Qi) * J * (Q * Qi) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_large_sq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (a : Fin n → F) (ha : ∀ i, a i ≠ 0) (B : ℝ) :
    ∃ N : ℕ, B < N ∧ ∀ i, ∃ c : v.adicCompletion F,
      c * c * algebraMap F (v.adicCompletion F) (a i) = algebraMap F (v.adicCompletion F) (a i + N) := by
  set M : ℕ := Ideal.absNorm v.asIdeal with hM
  have hM0 : M ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hM1 : M ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hM2 : 1 < M := by omega
  have hmem : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  have hval : Valued.v ((M : ℕ) : v.adicCompletion F) < 1 := by
    have e : ((M : ℕ) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F ((M : ℕ) : 𝓞 F)) := by simp
    have e2 : ∀ y : F, Valued.v (algebraMap F (v.adicCompletion F) y) = v.valuation F y :=
      fun y => v.valuedAdicCompletion_eq_valuation' y
    rw [e, e2]
    exact (v.valuation_lt_one_iff_mem _).2 hmem
  have h4 : Valued.v (4 : v.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 (by
    have h : algebraMap F (v.adicCompletion F) 4 ≠ 0 := (map_ne_zero _).2 (by norm_num)
    rwa [map_ofNat] at h)
  have hA : ∀ i, algebraMap F (v.adicCompletion F) (a i) ≠ 0 := fun i =>
    (map_ne_zero _).2 (ha i)
  have hev : ∀ i, ∀ᶠ k : ℕ in atTop, Valued.v ((M : ℕ) : v.adicCompletion F) ^ k <
      Valued.v (4 : v.adicCompletion F) * Valued.v (algebraMap F (v.adicCompletion F) (a i)) := by
    intro i
    have hne : Valued.v (4 : v.adicCompletion F) * Valued.v (algebraMap F (v.adicCompletion F) (a i)) ≠ 0 :=
      mul_ne_zero h4 ((Valuation.ne_zero_iff _).2 (hA i))
    obtain ⟨K, hK⟩ := exists_pow_lt₀ hval (Units.mk0 _ hne)
    exact eventually_atTop.2 ⟨K, fun k hk => lt_of_le_of_lt (pow_le_pow_right_of_le_one' hval.le hk) hK⟩
  have hbig : ∀ᶠ k : ℕ in atTop, B < ((M ^ k : ℕ) : ℝ) := by
    have : Tendsto (fun k : ℕ => ((M : ℝ)) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hM2)
    filter_upwards [this.eventually_gt_atTop B] with k hk
    push_cast
    exact hk
  obtain ⟨k, hk1, hk2⟩ := (hbig.and (eventually_all.2 hev)).exists
  refine ⟨M ^ k, hk1, fun i => ?_⟩
  obtain ⟨c, hc⟩ := GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v
    (1 + ((M : ℕ) : v.adicCompletion F) ^ k / algebraMap F (v.adicCompletion F) (a i)) (by
      rw [add_sub_cancel_left, map_div₀, map_pow]
      exact (div_lt_iff₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hA i)))).2 (hk2 i))
  refine ⟨c, ?_⟩
  rw [← hc, map_add, map_natCast]
  have := hA i
  push_cast
  field_simp

section Forms

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}

theorem isHermND_diagonal (e : Fin n → F) (he : ∀ i, e i ≠ 0) :
    IsHermND σ (diagonal fun i => algebraMap F E (e i)) := by
  refine ⟨fun i j => ?_, ?_⟩
  · by_cases h : i = j
    · subst h
      simp
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h), map_zero]
  · rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (map_ne_zero _).2 (he i)

theorem isPosDef_diagonal (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : Fin n → F)
    (he : ∀ (τ : E →+* ℂ) i, 0 < (τ (algebraMap F E (e i))).re) :
    IsPosDef σ (diagonal fun i => algebraMap F E (e i)) := by
  intro x hx τ
  have hre : ∀ i, (τ (σ (x i) * (algebraMap F E (e i) * x i))).re =
      Complex.normSq (τ (x i)) * (τ (algebraMap F E (e i))).re := by
    intro i
    rw [map_mul, map_mul, hσ τ]
    have : star (τ (x i)) * (τ (algebraMap F E (e i)) * τ (x i)) =
        ((Complex.normSq (τ (x i)) : ℝ) : ℂ) * τ (algebraMap F E (e i)) := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
      ring
    rw [this, Complex.re_ofReal_mul]
  simp only [dotProduct, mulVec_diagonal, map_sum, Complex.re_sum, hre]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun j _ => mul_nonneg (Complex.normSq_nonneg _) (he τ j).le)
    ⟨i, Finset.mem_univ _, mul_pos (Complex.normSq_pos.2 ?_) (he τ i)⟩
  simpa using hi

end Forms

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]

theorem sigR_includeLeft (x : R) :
    sigR R σ (Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) x) =
      Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) x := by
  simp [sigR]

theorem sigR_inclR (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem inclR_algebraMap (f : F) :
    inclR R (algebraMap F E f) =
      Algebra.TensorProduct.includeLeft (S := F) (R := F) (A := R) (B := E) (algebraMap F R f) := by
  change Algebra.TensorProduct.includeRight (algebraMap F E f) = _
  rw [AlgHom.commutes, AlgHom.commutes]

end Tensor

theorem locIso {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hinv : ∀ x, σ (σ x) = x) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (hP : P.det ≠ 0) (a e : Fin n → F)
    (hPd : Pᵀ * J * P.map σ = diagonal fun i => algebraMap F E (a i)) (v : HeightOneSpectrum (𝓞 F))
    (c : Fin n → Fv F v) (hc0 : ∀ i, c i ≠ 0)
    (hc : ∀ i, c i * c i * algebraMap F (Fv F v) (a i) = algebraMap F (Fv F v) (e i)) :
    Nonempty (GlobalTheory.AdelicU.GLoc σ J v ≃ₜ* GlobalTheory.AdelicU.GLoc σ (diagonal fun i => algebraMap F E (e i)) v) := by
  set φ : E →+* Fv F v ⊗[F] E := inclR (Fv F v) with hφ
  set s : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E := sigR (Fv F v) σ with hs
  let ι : Fv F v →ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.includeLeft
  have hsι : ∀ x, s (ι x) = ι x := sigR_includeLeft σ (Fv F v)
  have hsφ : ∀ x, s (φ x) = φ (σ x) := sigR_inclR σ (Fv F v)
  have hφι : ∀ f : F, φ (algebraMap F E f) = ι (algebraMap F (Fv F v) f) := inclR_algebraMap (Fv F v)
  set Q : Matrix (Fin n) (Fin n) E := P.map σ with hQdef
  have hQdet : Q.det ≠ 0 := by
    have h := RingHom.map_det (σ : E →+* E) P
    rw [RingHom.mapMatrix_apply] at h
    change Q.det ≠ 0 at *
    have h' : Q.det = σ P.det := h.symm
    rw [h']
    exact (map_ne_zero (σ : E →+* E)).2 hP
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.2 hQdet)
  have hQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.2 hQdet)
  set D : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := diagonal fun i => ι (c i)⁻¹ with hD
  set D' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := diagonal fun i => ι (c i) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    rw [← map_mul, inv_mul_cancel₀ (hc0 i), map_one]
  have hDD' : D' * D = 1 := by
    rw [hD, hD', diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    rw [← map_mul, mul_inv_cancel₀ (hc0 i), map_one]
  have hm : ∀ A B : Matrix (Fin n) (Fin n) E, (A * B).map φ = A.map φ * B.map φ := fun A B =>
    Matrix.map_mul
  have hone : (1 : Matrix (Fin n) (Fin n) E).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have hQr : Q.map φ * Q⁻¹.map φ = 1 := by rw [← hm, hQ, hone]
  have hQr' : Q⁻¹.map φ * Q.map φ = 1 := by rw [← hm, hQ', hone]
  have h1 : Formalism.UG.cT s (Q.map φ) * JR (F := F) (Fv F v) J * Q.map φ =
      diagonal fun i => φ (algebraMap F E (a i)) := by
    have e1 : Formalism.UG.cT s (Q.map φ) = Pᵀ.map φ := by
      ext i j
      simp [Formalism.UG.cT, hQdef, hsφ, hinv]
    have e2 : JR (F := F) (Fv F v) J = J.map φ := rfl
    rw [e1, e2, ← hm, ← hm, hPd, Matrix.diagonal_map (map_zero φ)]
  have h2 : Formalism.UG.cT s D * JR (F := F) (Fv F v) (diagonal fun i => algebraMap F E (e i)) * D =
      diagonal fun i => φ (algebraMap F E (a i)) := by
    have e1 : Formalism.UG.cT s D = D := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [Formalism.UG.cT, hD, hsι]
      · simp [Formalism.UG.cT, hD, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]
    have e2 : JR (F := F) (Fv F v) (diagonal fun i => algebraMap F E (e i)) =
        diagonal fun i => ι (algebraMap F (Fv F v) (e i)) := by
      change (diagonal fun i => algebraMap F E (e i)).map φ = _
      rw [Matrix.diagonal_map (map_zero φ)]
      congr 1
      ext i
      exact hφι _
    rw [e1, e2, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    rw [hφι, ← map_mul, ← map_mul, ← hc i]
    congr 1
    field_simp [hc0 i]
  obtain ⟨Φ, -⟩ := GlobalTheory.LocIsoConj.exists_locIso σ J (diagonal fun i => algebraMap F E (e i)) v
    (D * Q⁻¹.map φ) (Q.map φ * D') (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (Q.map φ), hQr', Matrix.one_mul, hDD]) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc D', hDD', Matrix.one_mul, hQr])
    (cT_congr s _ _ _ _ _ _ hQr h1 h2)
  exact ⟨Φ⟩

theorem stDefinite : StDefinite := by
  intro F E _ _ _ _ _ σ hc n J hJ v
  obtain ⟨hinv, hfix⟩ := GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hc
  obtain ⟨P, d, hP, hPd, hdf, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) (G := J) two_ne_zero
    (fun t => hinv t) (fun a b => hJ.1 b a)
  choose a ha using fun i => hfix (d i) (hdf i)
  have had : d = fun i => algebraMap F E (a i) := funext fun i => (ha i).symm
  have ha0 : ∀ i, a i ≠ 0 := fun i h => hd0 hJ.2 i (by rw [← ha i, h, map_zero])
  obtain ⟨N, hN, hsq⟩ := exists_large_sq v a ha0 (∑ i, ∑ τ : E →+* ℂ, |(τ (d i)).re|)
  have hpos : ∀ (τ : E →+* ℂ) i, 0 < (τ (algebraMap F E (a i + N))).re := by
    intro τ i
    have hle : |(τ (d i)).re| ≤ ∑ i, ∑ τ : E →+* ℂ, |(τ (d i)).re| :=
      (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ (d i)).re|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (f := fun i => ∑ τ : E →+* ℂ, |(τ (d i)).re|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    have h3 := neg_abs_le (τ (d i)).re
    rw [map_add, map_add, ha i, map_natCast, map_natCast, Complex.add_re, Complex.natCast_re]
    linarith
  have he0 : ∀ i, a i + N ≠ 0 := by
    intro i h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hpos τ i
    rw [h, map_zero, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  choose c hc' using hsq
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h
    have := hc' i
    rw [h, zero_mul, zero_mul] at this
    exact (map_ne_zero _).2 (he0 i) this.symm
  refine ⟨diagonal fun i => algebraMap F E (a i + N), isHermND_diagonal σ _ he0,
    isPosDef_diagonal σ hc.2.2.2 _ hpos, ?_⟩
  rw [had] at hPd
  exact locIso σ hinv J P hP a _ hPd v c hc0 hc'

end GlobalTheory.CompanionTheory.DefiniteForm

end
