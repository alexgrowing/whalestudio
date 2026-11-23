import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise

namespace GlobalTheory.SnMass.VolN.IntG

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in

theorem _root_.GlobalTheory.SnMass.VolN.IntG.Hpk_mulVec_esI (k r : ℕ) (a : Fin r) (y : Fin (2 * r + k + 1) → ℂ) :
    (_root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ y) (_root_.Formalism.QuantumDeterminants.esI k r a) = y (_root_.Formalism.QuantumDeterminants.eI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (_root_.Formalism.QuantumDeterminants.eI k r a)]
  · simp [_root_.Formalism.QuantumDeterminants.Hpk, _root_.Formalism.QuantumDeterminants.eI, _root_.Formalism.QuantumDeterminants.esI]
    omega
  · intro j _ hj
    have hj' : (j : ℕ) ≠ a := fun h => hj (Fin.ext (by simp [_root_.Formalism.QuantumDeterminants.eI, h]))
    simp only [_root_.Formalism.QuantumDeterminants.Hpk, _root_.Formalism.QuantumDeterminants.esI, Matrix.of_apply, Fin.val_mk]
    have c1 : ¬(2 * r + k - (a : ℕ) < r ∧ 2 * r + k - (a : ℕ) + (j : ℕ) = 2 * r + k) := by omega
    have c2 : ¬((j : ℕ) < r ∧ 2 * r + k - (a : ℕ) + (j : ℕ) = 2 * r + k) := by omega
    have c3 : ¬(2 * r + k - (a : ℕ) ≤ r + k) := by omega
    simp [c1, c2, c3]
  · simp

section Field

variable {E : Type} [Field E] [NumberField E]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in
variable {E : Type} [Field E] [NumberField E] in
private lemma algEquiv_map_mem_one_fractionalIdeal {E : Type} [Field E] [NumberField E] (t : E ≃ₐ[ℚ] E) {x : E}
    (hx : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) : t x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  have hint : IsIntegral ℤ (t (algebraMap (𝓞 E) E y)) :=
    (y.isIntegral_coe).map (t.toAlgHom.restrictScalars ℤ)
  exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in
variable {E : Type} [Field E] [NumberField E] in
private lemma trace_map_mul_eq_trace_mul_map_of_involutive {E : Type} [Field E] [NumberField E] (t : E ≃ₐ[ℚ] E)
    (ht : ∀ x, t (t x) = x) (y a : E) :
    Algebra.trace ℚ E (t y * a) = Algebra.trace ℚ E (y * t a) := by
  have h : t y * a = t (y * t a) := by rw [map_mul, ht]
  rw [h, Algebra.trace_eq_of_algEquiv]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in
variable {E : Type} [Field E] [NumberField E] in
private lemma map_mem_dual_one_of_involutive {E : Type} [Field E] [NumberField E] (t : E ≃ₐ[ℚ] E)
    (ht : ∀ x, t (t x) = x) {y : E}
    (hy : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    t y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := Ne.symm (zero_ne_one' _)
  rw [FractionalIdeal.mem_dual h1] at hy ⊢
  intro a ha
  have := hy (t a) (algEquiv_map_mem_one_fractionalIdeal t ha)
  simpa [Algebra.traceForm_apply, trace_map_mul_eq_trace_mul_map_of_involutive t ht] using this

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in
variable {E : Type} [Field E] [NumberField E] in
private lemma map_mem_differentIdeal_of_involutive {E : Type} [Field E] [NumberField E] (t : E ≃ₐ[ℚ] E)
    (ht : ∀ x, t (t x) = x) {x : E}
    (hx : x ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))) :
    t x ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) := by
  rw [coeIdeal_differentIdeal ℤ ℚ] at hx ⊢
  have h0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ (Ne.symm (zero_ne_one' (FractionalIdeal (𝓞 E)⁰ E)))
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have h1 := algEquiv_map_mem_one_fractionalIdeal t (hx (t y) (map_mem_dual_one_of_involutive t ht hy))
  rwa [map_mul, ht] at h1

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in
variable {E : Type} [Field E] [NumberField E] in
private lemma map_mem_differentIdeal_pow_of_involutive {E : Type} [Field E] [NumberField E] (t : E ≃ₐ[ℚ] E)
    (ht : ∀ x, t (t x) = x) (m : ℕ) {x : E}
    (hx : x ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) ^ m) :
    t x ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) ^ m := by
  induction m generalizing x with
  | zero => rw [pow_zero] at hx ⊢; exact algEquiv_map_mem_one_fractionalIdeal t hx
  | succ n ih =>
    rw [pow_succ] at hx ⊢
    refine FractionalIdeal.mul_induction_on (C := fun z => t z ∈ _) hx ?_ ?_
    · intro i hi j hj
      rw [map_mul]
      exact FractionalIdeal.mul_mem_mul (ih hi) (map_mem_differentIdeal_of_involutive t ht hj)
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.SnMass.VolN.IntG.mem_dInv_two_mul (t : E ≃ₐ[ℚ] E) (ht : ∀ x, t (t x) = x) (m : ℕ) (c : E)
    (h : ∀ x ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) ^ m,
      ∀ y ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) ^ m,
      x * t y * c ∈ (algebraMap (𝓞 E) E).range) :
    c ∈ _root_.GlobalTheory.SgGlob.dInv E (2 * m) := by
  unfold _root_.GlobalTheory.SgGlob.dInv
  have hD : ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [inv_pow, two_mul, pow_add, FractionalIdeal.mem_inv_iff (mul_ne_zero (pow_ne_zero _ hD) (pow_ne_zero _ hD))]
  intro z hz
  refine FractionalIdeal.mul_induction_on (C := fun w => c * w ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) hz ?_ ?_
  · intro i hi j hj
    obtain ⟨u, hu⟩ := h i hi (t j) (map_mem_differentIdeal_pow_of_involutive t ht m hj)
    refine (FractionalIdeal.mem_one_iff _).2 ⟨u, ?_⟩
    rw [hu, ht]; ring
  · intro a b ha hb
    rw [mul_add]
    exact Submodule.add_mem _ ha hb

end Field

section Place

variable {E : Type} [Field E]

end Place

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in
variable {E : Type} [Field E] in
private lemma modelEntry_eq_sq_mul_pairing_lemma_6 (σ : E →+* E) {k r : ℕ}
    (J γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (s : Fin r → ℝ) (w : InfinitePlace E) (a : Fin r)
    (hconj : ∀ x, w.embedding (σ x) = star (w.embedding x))
    (hA : (A w)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * A w = J.map w.embedding)
    (hdet : (A w).det ≠ 0) (hs : s a ≠ 0)
    (hf : (A w *ᵥ fun i => w.embedding (f i a)) = ((s a : ℂ))⁻¹ • Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1) :
    _root_.GlobalTheory.SnMass.VolN.gM A γ w (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.esI k r a) =
      ((s a : ℂ)) ^ 2 * w.embedding ((fun i => σ (f i a)) ⬝ᵥ (J *ᵥ (γ *ᵥ fun i => f i a))) := by
  set fw : Fin (2 * r + k + 1) → ℂ := fun i => w.embedding (f i a) with hfw
  have hs' : ((s a : ℂ)) ≠ 0 := by exact_mod_cast hs
  have hinv : (A w)⁻¹ *ᵥ Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1 = ((s a : ℂ)) • fw := by
    have h : Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) = A w *ᵥ (((s a : ℂ)) • fw) := by
      rw [Matrix.mulVec_smul, hf, smul_smul, mul_inv_cancel₀ hs', one_smul]
    rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have h1 : _root_.GlobalTheory.SnMass.VolN.gM A γ w (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.esI k r a) =
      ((s a : ℂ)) * (A w *ᵥ (γ.map w.embedding *ᵥ fw)) (_root_.Formalism.QuantumDeterminants.eI k r a) := by
    unfold _root_.GlobalTheory.SnMass.VolN.gM
    have e : (A w * γ.map w.embedding * (A w)⁻¹) (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.esI k r a) =
        ((A w * γ.map w.embedding * (A w)⁻¹) *ᵥ Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1) (_root_.Formalism.QuantumDeterminants.eI k r a) := by
      rw [Matrix.mulVec_single_one]; rfl
    rw [e, ← Matrix.mulVec_mulVec, hinv, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul,
      Matrix.mulVec_smul]
    rfl
  have h2 : w.embedding ((fun i => σ (f i a)) ⬝ᵥ (J *ᵥ (γ *ᵥ fun i => f i a))) =
      ((s a : ℂ))⁻¹ * (A w *ᵥ (γ.map w.embedding *ᵥ fw)) (_root_.Formalism.QuantumDeterminants.eI k r a) := by
    have e1 : w.embedding ((fun i => σ (f i a)) ⬝ᵥ (J *ᵥ (γ *ᵥ fun i => f i a))) =
        star fw ⬝ᵥ (J.map w.embedding *ᵥ (γ.map w.embedding *ᵥ fw)) := by
      simp [dotProduct, Matrix.mulVec, map_sum, hconj, hfw]
    rw [e1, ← hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec, hf, star_smul, smul_dotProduct,
      show star (Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1 : Fin (2 * r + k + 1) → ℂ) =
        Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1 by
          ext i; by_cases h : i = _root_.Formalism.QuantumDeterminants.esI k r a <;> simp [Pi.single_apply, h],
      single_dotProduct, one_mul, _root_.GlobalTheory.SnMass.VolN.IntG.Hpk_mulVec_esI]
    simp [Complex.conj_ofReal]
  rw [h1, h2]
  field_simp

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Pointwise in

theorem _root_.GlobalTheory.SnMass.VolN.IntG.antidiag_mem_skewLat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    _root_.GlobalTheory.SnMass.VolN.IsVolData σ J Λ P f T A s → ∀ γ ∈ _root_.GlobalTheory.SnMass.VolN.GN (σ : E →+* E) J Λ P, ∀ a : Fin r,
      (∀ w, (_root_.GlobalTheory.SnMass.VolN.gM A γ w (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.esI k r a)).re = 0) →
      (fun w => (_root_.GlobalTheory.SnMass.VolN.gM A γ w (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.esI k r a)).im) ∈
        _root_.GlobalTheory.SnMass.VolN.skewLat (σ : E →+* E) (_root_.GlobalTheory.SgGlob.dInv E (2 * (r - a.val))) (s a ^ 2) := by
  intro hV γ hγ a hre
  unfold _root_.GlobalTheory.SnMass.VolN.IsVolData at hV
  obtain ⟨hT, -, hJ, hΛ, -, -, hspan, hA, hs, hAd⟩ := hV
  simp only [_root_.GlobalTheory.SnMass.VolN.GN, Set.mem_setOf_eq, _root_.GlobalTheory.SgGlob.latMap] at hγ
  obtain ⟨-, hγΛ⟩ := hγ
  have hconj : ∀ (w : InfinitePlace E) (x : E), w.embedding (σ x) = star (w.embedding x) :=
    fun w x => hT.2.2.2 _ x
  set c : E := (fun i => σ (f i a)) ⬝ᵥ (J *ᵥ (γ *ᵥ fun i => f i a)) with hc
  have hdet : ∀ w : InfinitePlace E, (A w).det ≠ 0 := by
    intro w h
    have hd := congrArg Matrix.det (hA w)
    rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero] at hd
    have hw : w.embedding J.det = 0 := by
      rw [RingHom.map_det]
      exact hd.symm
    exact hJ.2 ((map_eq_zero_iff _ w.embedding.injective).1 hw)
  have hentry : ∀ w, _root_.GlobalTheory.SnMass.VolN.gM A γ w (_root_.Formalism.QuantumDeterminants.eI k r a) (_root_.Formalism.QuantumDeterminants.esI k r a) =
      ((s a : ℂ)) ^ 2 * w.embedding c := fun w =>
    modelEntry_eq_sq_mul_pairing_lemma_6 (σ : E →+* E) J γ A f s w a (hconj w) (hA w) (hdet w) (hs a).ne'
      (hAd w a).2
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hinvol : ∀ x, σ (σ x) = x := fun x =>
    w₀.embedding.injective (by rw [hconj, hconj, star_star])
  have hsc : σ c = -c := by
    apply w₀.embedding.injective
    have h0 := hre w₀
    rw [hentry] at h0
    have hre0 : (w₀.embedding c).re = 0 := by
      have e : (((s a : ℂ)) ^ 2 * w₀.embedding c).re = (s a) ^ 2 * (w₀.embedding c).re := by
        rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
      rw [e] at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (hs a).ne')
    rw [hconj, map_neg]
    apply Complex.ext <;> simp [hre0]
  have hmemΛ : ∀ z ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)) ^ (r - a.val),
      (z • fun i => f i a) ∈ Λ := by
    intro z hz
    apply hspan
    unfold _root_.GlobalTheory.SnMass.tupLat
    apply Submodule.subset_span
    refine ⟨Fin.natAdd (r + 1) a, z, ?_, ?_⟩
    · simp only [_root_.GlobalTheory.SnMass.id1, Fin.append_right]
      rw [_root_.GlobalTheory.SgGlob.dInv, inv_pow, inv_inv]
      exact hz
    · funext i
      simp [_root_.GlobalTheory.SnMass.sideM, Fin.append_right]
  let t : E ≃ₐ[ℚ] E :=
    { toFun := σ, invFun := σ, left_inv := hinvol, right_inv := hinvol,
      map_mul' := map_mul σ, map_add' := map_add σ,
      commutes' := fun q => by rw [eq_ratCast (algebraMap ℚ E) q]; exact map_ratCast σ q }
  have ht : ∀ x, t x = σ x := fun x => rfl
  unfold _root_.GlobalTheory.SnMass.VolN.skewLat
  refine ⟨c, ?_, hsc, fun w => ?_⟩
  · refine _root_.GlobalTheory.SnMass.VolN.IntG.mem_dInv_two_mul t (fun x => by rw [ht, ht, hinvol])
      (r - a.val) c ?_
    intro x hx y hy
    have hγmem : γ *ᵥ (x • fun i => f i a) ∈ Λ := by
      have hm := Submodule.mem_map_of_mem
        (f := (γ.mulVecLin.restrictScalars (𝓞 E))) (hmemΛ x hx)
      rw [hγΛ] at hm
      exact hm
    have hpair := (hΛ.2 _).1 hγmem _ (hmemΛ y hy)
    convert hpair using 1
    unfold _root_.GlobalTheory.SgAlg.form
    have e : (fun i => (σ : E →+* E) ((y • fun i => f i a) i)) =
        σ y • fun i => (σ : E →+* E) (f i a) := by
      funext i; simp
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, e, smul_dotProduct, dotProduct_smul, ht]
    change x * σ y * c = σ y * (x * c)
    ring
  · beta_reduce
    rw [hentry, ← Complex.ofReal_pow, Complex.im_ofReal_mul]

end GlobalTheory.SnMass.VolN.IntG
