import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatricesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominatorStatement

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.UnRep.SplitRep

def mix {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (κ : GL (Fin n) R) : GL (Fin n) R where
  val := ε • κ.1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)
  inv := ε • (κ⁻¹).1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)
  val_inv := by
    have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, hε]; ring
    have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
    have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, h2]; ring
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3,
      Units.mul_inv, zero_smul, add_zero, zero_add, mul_one]
    rw [← add_smul]; simp
  inv_val := by
    have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, hε]; ring
    have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
    have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, h2]; ring
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hε, h1, h2, h3,
      Units.inv_mul, zero_smul, add_zero, zero_add, mul_one]
    rw [← add_smul]; simp

theorem mix_val {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (κ : GL (Fin n) R) :
    (mix ε hε κ).1 = ε • κ.1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := rfl

theorem mix_inv_val {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (κ : GL (Fin n) R) :
    ((mix ε hε κ)⁻¹).1 = ε • (κ⁻¹).1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := rfl

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
theorem _root_.GlobalTheory.UnRep.SplitRep.mix_mul_mix {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε)
    (hε' : (1 - ε) * (1 - ε) = 1 - ε) (κ : GL (Fin n) R) :
    (_root_.GlobalTheory.UnRep.SplitRep.mix ε hε κ).1 * (_root_.GlobalTheory.UnRep.SplitRep.mix (1 - ε) hε' κ).1 = κ.1 := by
  rw [_root_.GlobalTheory.UnRep.SplitRep.mix_val, _root_.GlobalTheory.UnRep.SplitRep.mix_val]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
  linear_combination (norm := module) hε • ((2 : R) • κ.1 - κ.1 * κ.1 - 1)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.UnRep.SplitRep.isUnA_mix (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ε : _root_.GlobalTheory.AdLat.RA F E) (hε : ε * ε = ε)
    (hs : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ε = ε) (κ : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (hκ : _root_.GlobalTheory.UnRep.IsUnA c G κ.1) :
    _root_.GlobalTheory.UnRep.IsUnA c G (_root_.GlobalTheory.UnRep.SplitRep.mix ε hε κ).1 := by
  intro x y
  have hκxy := hκ x y
  unfold _root_.GlobalTheory.AdLat.hermA at hκxy ⊢
  rw [_root_.GlobalTheory.UnRep.SplitRep.mix_val]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_mul, map_sub, map_one, hs]
  set σ := _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c
  calc _ = ε * (∑ a, ∑ b, (κ.1 *ᵥ x) a * 1 ⊗ₜ[F] G a b * σ ((κ.1 *ᵥ y) b)) +
        (1 - ε) * (∑ a, ∑ b, x a * 1 ⊗ₜ[F] G a b * σ (y b)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        linear_combination ((κ.1 *ᵥ x) a * 1 ⊗ₜ[F] G a b * σ ((κ.1 *ᵥ y) b) -
          (κ.1 *ᵥ x) a * 1 ⊗ₜ[F] G a b * σ (y b) - x a * 1 ⊗ₜ[F] G a b * σ ((κ.1 *ᵥ y) b) +
          x a * 1 ⊗ₜ[F] G a b * σ (y b)) * hε
    _ = _ := by rw [hκxy]; ring

def inc (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : E →+* RA F E :=
  (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom

theorem hermA_eq (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c G x y = x ⬝ᵥ (fm F G *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
  simp only [hermA, dotProduct, Matrix.mulVec, fm, Matrix.map_apply, Finset.mul_sum, mul_assoc]

variable [NumberField E]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
variable [NumberField E] in

theorem _root_.GlobalTheory.UnRep.SplitRep.exists_multiple (s : 𝓞 E) (hs : s ≠ 0) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ s ∣ algebraMap (𝓞 F) (𝓞 E) m ∧ ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal →
      ∃ P : Ideal (𝓞 E), P.IsPrime ∧ s ∈ P ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  classical
  set J := Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {s}) with hJdef
  have hJ : J ≠ ⊥ := Ideal.comap_ne_bot_of_integral_mem hs (Ideal.mem_span_singleton_self s)
    (Algebra.IsIntegral.isIntegral s)
  have hJ0 : J ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero hJ
  set h := Fintype.card (ClassGroup (𝓞 F))
  have hprin : (J ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hJ0 h)]
    have : ClassGroup.mk0 (⟨J, hJ0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact this
  set m := Submodule.IsPrincipal.generator (J ^ h)
  have hspan : J ^ h = Ideal.span {m} := (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hmJ : m ∈ J := Ideal.pow_le_self (Fintype.card_ne_zero) (hspan ▸ Ideal.mem_span_singleton_self m)
  refine ⟨m, ?_, ?_, ?_⟩
  · intro hm0
    apply pow_ne_zero h hJ
    rw [hspan, hm0, Ideal.span_singleton_eq_bot.2 rfl]
    rfl
  · exact Ideal.mem_span_singleton.1 hmJ
  · intro v hv
    have hle : J ≤ v.asIdeal := by
      apply v.isPrime.le_of_pow_le (n := h)
      rw [hspan, Ideal.span_le, Set.singleton_subset_iff]
      exact hv
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (Ideal.span {s}) hle
    exact ⟨Q, hQp, hQ (Ideal.mem_span_singleton_self s), hQc⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
variable [NumberField E] in
omit [NumberField E] in
theorem _root_.GlobalTheory.UnRep.SplitRep.exists_div (m : 𝓞 F) (hm : m ≠ 0) (e : FiniteAdeleRing (𝓞 F) F)
    (h1 : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → e v = 1)
    (h0 : ∀ v : HeightOneSpectrum (𝓞 F), m ∉ v.asIdeal → e v = 0) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ (m : F) • a = 1 - e := by
  have hmF : (m : F) ≠ 0 := by simpa using hm
  refine ⟨(m : F)⁻¹ • (1 - e), fun v => ?_, ?_⟩
  · show (((m : F)⁻¹ : F) : v.adicCompletion F) * (1 - e v) ∈ v.adicCompletionIntegers F
    by_cases hv : m ∈ v.asIdeal
    · rw [h1 v hv, sub_self, mul_zero]
      exact zero_mem _
    · rw [h0 v hv, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap]
      rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v m).mpr hv, inv_one]
  · rw [smul_smul, mul_inv_cancel₀ hmF, one_smul]

end GlobalTheory.UnRep.SplitRep

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem galoisAut_one_tmul_eq_one_tmul (c : E ≃ₐ[F] E) (z : E) :
    _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] z) = 1 ⊗ₜ[F] c z := by
  simp [_root_.GlobalTheory.AdLat.sg]

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
private theorem isUnA_fm_of_isUnE (c : E ≃ₐ[F] E) (G γ : Matrix (Fin n) (Fin n) E)
    (hγ : _root_.GlobalTheory.UnRep.IsUnE c G γ) :
    _root_.GlobalTheory.UnRep.IsUnA c G (_root_.GlobalTheory.UnRep.fm F γ) := by
  have hmat : ∀ i j, ∑ a, ∑ b, γ a i * G a b * c (γ b j) = G i j := by
    intro i j
    have := hγ (Pi.single i 1) (Pi.single j 1)
    simp [_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot, Matrix.mulVec, dotProduct, Pi.single_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  intro x y
  unfold _root_.GlobalTheory.AdLat.hermA
  set σ := _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c with hσ
  have h1 : ∀ z : E, σ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] z) = 1 ⊗ₜ[F] c z := fun z => galoisAut_one_tmul_eq_one_tmul c z
  have hG : ∀ i j, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] G i j = ∑ a, ∑ b,
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] γ a i) * (1 ⊗ₜ[F] G a b) * (1 ⊗ₜ[F] c (γ b j)) := by
    intro i j
    rw [← hmat i j, TensorProduct.tmul_sum]
    simp_rw [TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  calc _ = ∑ a, ∑ b, ∑ i, ∑ j, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] γ a i) * x i * (1 ⊗ₜ[F] G a b) *
        ((1 ⊗ₜ[F] c (γ b j)) * σ (y j)) := by
        simp only [Matrix.mulVec, dotProduct, _root_.GlobalTheory.UnRep.fm, Matrix.map_apply, map_sum,
          map_mul, h1, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] γ a i) * x i * (1 ⊗ₜ[F] G a b) *
        ((1 ⊗ₜ[F] c (γ b j)) * σ (y j)) := by
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hG i j, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in

theorem _root_.GlobalTheory.UnRep.exists_rep_suppSplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UnRep.IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (N : ℕ), _root_.GlobalTheory.UnRep.IsUnA c G g.1 → 0 < N → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)), _root_.GlobalTheory.UnRep.IsUnE c G γ.1 ∧ _root_.GlobalTheory.UnRep.IsUnA c G h.1 ∧ _root_.GlobalTheory.UnRep.IsUnA c G k.1 ∧ g.1 = _root_.GlobalTheory.UnRep.fm F γ.1 * h.1 * k.1 ∧ _root_.GlobalTheory.UnRep.SuppSplit c N h.1 ∧ (∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), ∃ w ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧ ∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ c n G hG hdeg L hL hspan g N hg hN
  obtain ⟨γ, hγ, hcong, s, hsm, hsL⟩ :=
    _root_.GlobalTheory.UnRep.LatForm.exists_rep_split_denominator F E c n G hG hdeg L hL hspan g N hg hN
  obtain ⟨hs0, hsP⟩ := hsm
  obtain ⟨t, ht, htw⟩ := hcong
  obtain ⟨m, hm0, hsdvd, hmP⟩ := _root_.GlobalTheory.UnRep.SplitRep.exists_multiple (F := F) s hs0
  obtain ⟨d, hd⟩ := hsdvd
  have hfin : {v : HeightOneSpectrum (𝓞 F) | m ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {m}) ?_).subset fun v hv => ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hm0
    · exact Ideal.dvd_span_singleton.2 hv
  obtain ⟨e, he1, he0⟩ := _root_.GlobalTheory.UnRep.SmallMat.exists_indicator (F := F) hfin.toFinset
  have he1' : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → e v = 1 :=
    fun v hv => he1 v (hfin.mem_toFinset.2 hv)
  have he0' : ∀ v : HeightOneSpectrum (𝓞 F), m ∉ v.asIdeal → e v = 0 :=
    fun v hv => he0 v fun h => hv (hfin.mem_toFinset.1 h)
  obtain ⟨a, haint, ha⟩ := _root_.GlobalTheory.UnRep.SplitRep.exists_div m hm0 e he1' he0'
  have hee : e * e = e := by
    refine FiniteAdeleRing.ext F fun v => ?_
    show e v * e v = e v
    by_cases hv : m ∈ v.asIdeal
    · rw [he1' v hv, one_mul]
    · rw [he0' v hv, zero_mul]
  have heint : ∀ v : HeightOneSpectrum (𝓞 F), e v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases hv : m ∈ v.asIdeal
    · rw [he1' v hv]; exact one_mem _
    · rw [he0' v hv]; exact zero_mem _
  have h1eint : ∀ v : HeightOneSpectrum (𝓞 F), (1 - e) v ∈ v.adicCompletionIntegers F :=
    fun v => sub_mem (one_mem _) (heint v)
  set ε : _root_.GlobalTheory.AdLat.RA F E := e ⊗ₜ[F] (1 : E) with hεdef
  have hε : ε * ε = ε := by rw [hεdef, Algebra.TensorProduct.tmul_mul_tmul, hee, mul_one]
  have hε' : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
  have hσε : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ε = ε := by
    simp [hεdef, _root_.GlobalTheory.AdLat.sg]
  have hσε' : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (1 - ε) = 1 - ε := by
    rw [map_sub, map_one, hσε]
  have hcompl : (1 : _root_.GlobalTheory.AdLat.RA F E) - ε = (1 - e) ⊗ₜ[F] (1 : E) := by
    rw [hεdef, Algebra.TensorProduct.one_def, TensorProduct.sub_tmul]
  have hfac : (1 : _root_.GlobalTheory.AdLat.RA F E) - ε =
      (a ⊗ₜ[F] (1 : E)) * (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (d : E)) * (1 ⊗ₜ[F] (s : E))) := by
    rw [hcompl, ← ha, TensorProduct.smul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have hmE : ((algebraMap (𝓞 F) (𝓞 E) m : 𝓞 E) : E) = (m : F) • (1 : E) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [← hmE, hd]
    push_cast
    ring
  have hcomplmem : ∀ u : Fin n → _root_.GlobalTheory.AdLat.RA F E,
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • u ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) →
      (1 - ε) • u ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
    intro u hu
    rw [hfac, mul_smul, mul_smul]
    exact _root_.GlobalTheory.AdLat.Translate.hat_smul_int haint (_root_.GlobalTheory.AdLat.Translate.hat_smul_ring L d hu)
  set γA : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E) :=
    Units.map (_root_.GlobalTheory.UnRep.SplitRep.inc F E).mapMatrix.toMonoidHom γ with hγA
  have hγAval : γA.1 = _root_.GlobalTheory.UnRep.fm F γ.1 := rfl
  have hγAinv : (γA⁻¹).1 = _root_.GlobalTheory.UnRep.fm F (γ⁻¹).1 := rfl
  set x := γA * g with hx
  have hxval : x.1 = _root_.GlobalTheory.UnRep.fm F γ.1 * g.1 := by rw [hx, Units.val_mul, hγAval]
  have hxinv : (x⁻¹).1 = g⁻¹.1 * _root_.GlobalTheory.UnRep.fm F (γ⁻¹).1 := by
    rw [hx, mul_inv_rev, Units.val_mul, hγAinv]
  have hxU : _root_.GlobalTheory.UnRep.IsUnA c G x.1 := by
    intro u w
    rw [hxval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      isUnA_fm_of_isUnE c G γ.1 hγ (g.1 *ᵥ u) (g.1 *ᵥ w), hg u w]
  refine ⟨γ⁻¹, _root_.GlobalTheory.UnRep.SplitRep.mix ε hε x, _root_.GlobalTheory.UnRep.SplitRep.mix (1 - ε) hε' x, ?_,
    _root_.GlobalTheory.UnRep.SplitRep.isUnA_mix c G ε hε hσε x hxU,
    _root_.GlobalTheory.UnRep.SplitRep.isUnA_mix c G (1 - ε) hε' hσε' x hxU, ?_, ?_, ?_, ?_⟩
  · intro u w
    rw [← hγ ((γ⁻¹).1 *ᵥ u) ((γ⁻¹).1 *ᵥ w), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec]
  · rw [mul_assoc, _root_.GlobalTheory.UnRep.SplitRep.mix_mul_mix ε hε hε' x, ← hγAinv, hx,
      ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  · refine ⟨e, hee, hfin.subset fun v hv => ?_, fun v hv => ?_, ?_⟩
    · by_contra hm
      exact hv (he0' v hm)
    · have hmv : m ∈ v.asIdeal := by
        by_contra hm
        exact hv (he0' v hm)
      obtain ⟨P, hP, hsP', hPc⟩ := hmP v hmv
      obtain ⟨hmov, hNP⟩ := hsP P hP hsP'
      refine ⟨⟨P, hP, hPc, hmov⟩, fun hN' => hNP ?_⟩
      have hmem : algebraMap (𝓞 F) (𝓞 E) (N : 𝓞 F) ∈ P := by
        rw [← Ideal.mem_comap, hPc]; exact hN'
      simpa using hmem
    · rw [_root_.GlobalTheory.UnRep.SplitRep.mix_val]
      have hsub : ε • x.1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) - 1 =
          ε • (x.1 - 1) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [hsub, smul_smul, hε]
  · intro z hz
    obtain ⟨w, hw, htw'⟩ := htw z hz
    rw [← hxval] at htw'
    set y := (1 - ε) • (x.1 *ᵥ z - z) with hydef
    set w' := (1 - ε) • w with hw'def
    have hyL : y ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
      rw [hydef, smul_sub]
      refine sub_mem (hcomplmem _ ?_) ?_
      · rw [hxval]; exact (hsL z hz).1
      · rw [hcompl]; exact _root_.GlobalTheory.AdLat.Translate.hat_smul_int h1eint hz
    have hw'L : w' ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
      rw [hw'def, hcompl]; exact _root_.GlobalTheory.AdLat.Translate.hat_smul_int h1eint hw
    have hky : (_root_.GlobalTheory.UnRep.SplitRep.mix (1 - ε) hε' x).1 *ᵥ z - z = y := by
      rw [_root_.GlobalTheory.UnRep.SplitRep.mix_val, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hydef, sub_sub_cancel, smul_sub]
      simp only [sub_smul, one_smul]
      abel
    have hty : t • y = N • w' := by rw [hydef, hw'def, smul_comm, htw', smul_comm]
    have hty' : (t : ℤ) • y = (N : ℤ) • w' := by rw [natCast_zsmul, natCast_zsmul, hty]
    have hgcd : (1 : ℤ) = t * Nat.gcdA t N + N * Nat.gcdB t N := by
      rw [← Nat.gcd_eq_gcd_ab, ht, Nat.cast_one]
    refine ⟨Nat.gcdA t N • w' + Nat.gcdB t N • y,
      add_mem (zsmul_mem hw'L _) (zsmul_mem hyL _), ?_⟩
    rw [hky, ← natCast_zsmul]
    calc y = (1 : ℤ) • y := (one_smul _ _).symm
      _ = ((t : ℤ) * Nat.gcdA t N + N * Nat.gcdB t N) • y := by rw [hgcd]
      _ = Nat.gcdA t N • ((t : ℤ) • y) + (N : ℤ) • (Nat.gcdB t N • y) := by
        rw [add_smul, mul_comm (t : ℤ), mul_smul, mul_smul]
      _ = (N : ℤ) • (Nat.gcdA t N • w' + Nat.gcdB t N • y) := by
        rw [hty', smul_comm (Nat.gcdA t N), smul_add]
  · intro z hz
    rw [_root_.GlobalTheory.UnRep.SplitRep.mix_inv_val, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_sub_cancel]
    refine add_mem (hcomplmem _ ?_) ?_
    · rw [hxinv]; exact (hsL z hz).2
    · exact _root_.GlobalTheory.AdLat.Translate.hat_smul_int heint hz
