import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.SmallMat

open GlobalTheory.AdLat.Translate

theorem exists_dvd_pow_mul_coprime (N m : ℕ) (hm : m ≠ 0) :
    ∃ t k : ℕ, t.Coprime N ∧ m ∣ N ^ k * t := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one => exact ⟨1, 0, by simp, by simp⟩
  | prime_mul p a hp ih =>
    obtain ⟨t, k, ht, h⟩ := ih (right_ne_zero_of_mul hm)
    by_cases hpN : p ∣ N
    · refine ⟨t, k + 1, ht, ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_dvd_mul hpN h
    · refine ⟨p * t, k, Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN) ht, ?_⟩
      rw [mul_left_comm]
      exact mul_dvd_mul_left p h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem exists_indicator (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0 := by
  classical
  refine ⟨⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩,
    fun v hv => if_pos hv, fun v hv => if_neg hv⟩
  beta_reduce
  split_ifs
  · exact one_mem (v.adicCompletionIntegers F)
  · exact zero_mem (v.adicCompletionIntegers F)

theorem exists_nsmul_integral (b : FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ v, (m • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F 1 one_pos b
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset F)
  have hc : IsIntegral ℤ (y • x) := hy x (by simp)
  have hc' : IsIntegral ℤ (y.natAbs • x) := by
    rcases Int.natAbs_eq y with h | h
    · have : y.natAbs • x = y • x := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc
    · have : y.natAbs • x = -(y • x) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, fun v => ?_⟩
  rw [smul_add, ← map_nsmul]
  refine add_mem ?_ (nsmul_mem (nsmul_mem (ha v) 1) _)
  exact v.coe_mem_adicCompletionIntegers (K := F) (⟨y.natAbs • x, hc'⟩ : 𝓞 F)

theorem exists_coprime_nsmul_integral (N : ℕ) (b : FiniteAdeleRing (𝓞 F) F)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → b v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ v, (t • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨m, hm, h⟩ := exists_nsmul_integral b
  obtain ⟨t, k, ht, c, hc⟩ := exists_dvd_pow_mul_coprime N m hm
  refine ⟨t, ht, fun v => ?_⟩
  change t • b v ∈ _
  by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
  · rw [hb v hv, smul_zero]; exact zero_mem _
  · have h1 : c • (m • b v) ∈ v.adicCompletionIntegers F := nsmul_mem (h v) c
    rw [smul_smul, mul_comm, ← hc, mul_smul, nsmul_eq_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow] at h1
    have hN : Valued.v ((N : ℕ) : v.adicCompletion F) = 1 := by
      have h1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hv
      have h2 := v.valuedAdicCompletion_eq_valuation' (K := F) ((N : ℕ) : F)
      have h3 : (algebraMap F (v.adicCompletion F)) ((N : ℕ) : F) =
        ((N : ℕ) : v.adicCompletion F) := map_natCast _ _
      rw [← h3]
      have h4 : (((N : ℕ) : 𝓞 F) : F) = ((N : ℕ) : F) :=
        map_natCast (algebraMap (𝓞 F) F) _
      exact h2.trans (h4 ▸ h1)
    rw [hN, one_pow, one_mul] at h1
    exact h1

theorem fm_add (A B : Matrix (Fin n) (Fin n) E) : fm F (A + B) = fm F A + fm F B := by
  ext i j
  simp [fm, TensorProduct.tmul_add]

theorem fm_zero : fm F (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j
  simp [fm]

theorem nsmul_tmul_one (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) :
    ((d • a) ⊗ₜ[F] (1 : E) : RA F E) = d • (a ⊗ₜ[F] (1 : E) : RA F E) := by
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, ih]

theorem exists_approx (S : Set (Fin n → E))
    (hS : ∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ) (hD : 0 < D) :
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w := by
  let P : Matrix (Fin n) (Fin n) (RA F E) → Prop := fun M =>
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w
  have hadd : ∀ A B, P A → P B → P (A + B) := by
    rintro A B ⟨A₀, hA⟩ ⟨B₀, hB⟩
    refine ⟨A₀ + B₀, fun z hz => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hA z hz
    obtain ⟨w, hw, hw'⟩ := hB z hz
    refine ⟨u + w, add_mem hu hw, ?_⟩
    rw [smul_add, ← hu', ← hw', ← Matrix.add_mulVec, fm_add, add_sub_add_comm]
  have hzero : P 0 := ⟨0, fun z _ => ⟨0, zero_mem _, by simp [fm_zero]⟩⟩
  have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (B : Matrix (Fin n) (Fin n) E),
      P ((a ⊗ₜ[F] (1 : E) : RA F E) • fm F B) := by
    intro a B
    obtain ⟨d, hd, hB⟩ := hS (fm F B)
    obtain ⟨r, a', ha', rfl⟩ := exists_eq_algebraMap_add_nsmul F (D * d) (Nat.mul_pos hD hd) a
    refine ⟨r • B, fun z hz => ⟨_, hat_smul_int ha' (hB z hz), ?_⟩⟩
    have h1 : fm F (r • B) =
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) r ⊗ₜ[F] (1 : E) : RA F E) • fm F B := by
      ext i j
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [h1, TensorProduct.add_tmul, add_smul, add_sub_cancel_left, Matrix.smul_mulVec,
      nsmul_tmul_one, smul_assoc, mul_smul, smul_comm d]
  have hsingle : ∀ i j (t : RA F E), P (Matrix.single i j t) := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a y =>
      have := hgen a (Matrix.single i j y)
      convert this using 1
      ext k l
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Matrix.single_apply]
      split_ifs <;> simp
    | add s t hs ht => rw [Matrix.single_add]; exact hadd _ _ hs ht
  change P M
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ P hadd hzero fun i _ =>
    Finset.sum_induction _ P hadd hzero fun j _ => hsingle i j _

theorem exists_coprime_small (S : Set (Fin n → E)) (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hD : 0 < D)
    (hM : ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (he : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F S, ∃ w ∈ hat F S,
      t • (((e ⊗ₜ[F] (1 : E) : RA F E) • M) *ᵥ z) = D • w := by
  obtain ⟨d, hd, hM⟩ := hM
  have hK : ((D * d : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hD hd).ne'
  set b : FiniteAdeleRing (𝓞 F) F :=
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ((D * d : ℕ) : F)⁻¹ * e with hb
  have hbe : e = (D * d) • b := by
    rw [hb, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_mul, mul_inv_cancel₀ hK, map_one, one_mul]
  obtain ⟨t, ht, h⟩ := exists_coprime_nsmul_integral N b fun v hv => by
    change _ * e v = 0
    rw [he v hv, mul_zero]
  refine ⟨t, ht, fun z hz => ⟨_, hat_smul_int h (hM z hz), ?_⟩⟩
  rw [hbe, Matrix.smul_mulVec, nsmul_tmul_one, nsmul_tmul_one, smul_assoc, smul_assoc, mul_smul,
    smul_comm t D, smul_comm d]

end GlobalTheory.UnRep.SmallMat

open GlobalTheory.UnRep.SmallMat GlobalTheory.AdLat.Translate in

theorem GlobalTheory.UnRep.idempotent_adeles_small_matrices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0) ∧ (∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))) ∧ (∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), (M - fm F M₀) *ᵥ z = D • w) ∧ (∀ (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), 0 < D → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) → ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (((e ⊗ₜ[F] (1 : E)) • M) *ᵥ z) = D • w) ∧ ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ z ∈ hat F (L : Set (Fin n → E)), (a ⊗ₜ[F] (1 : E)) • z ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n L hL hsp
  have h4 := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hsp).2.2.2
  have h2 := fun M : Matrix (Fin n) (Fin n) (RA F E) => exists_bound M hL h4
  exact ⟨exists_indicator, h2, exists_approx _ h2,
    fun N D e M hD he => exists_coprime_small _ N D e M hD (h2 M) he,
    fun a ha z hz => hat_smul_int ha hz⟩
