import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.SW.QuadField

section Val

variable {K : Type} [Field K] (w : Valuation K (WithZero (Multiplicative ℤ)))

theorem exists_exp {x : K} (hx : x ≠ 0) (h1 : w x ≤ 1) :
    ∃ k : ℕ, w x = WithZero.exp (-(k : ℤ)) := by
  have h0 : w x ≠ 0 := (Valuation.ne_zero_iff w).2 hx
  obtain ⟨a, ha⟩ : ∃ a : ℤ, w x = WithZero.exp a := ⟨WithZero.log (w x), (WithZero.exp_log h0).symm⟩
  rw [ha] at h1
  have ha0 : a ≤ 0 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  refine ⟨(-a).toNat, ?_⟩
  rw [ha, Int.toNat_of_nonneg (by omega), neg_neg]

theorem val_pow {ϖ : K} (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) :
    w (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.exp_nsmul]
  congr 1
  simp

variable {D : K}

theorem norm_ne_zero (hD : w D = 1) (hsq : ∀ e : K, w e ≤ 1 → ¬ w (e ^ 2 - D) < 1) {x y : K}
    (h : x ≠ 0 ∨ y ≠ 0) : x ^ 2 - D * y ^ 2 ≠ 0 := by
  intro hN
  rcases eq_or_ne y 0 with rfl | hy
  · have hx : x ≠ 0 := h.resolve_right (by simp)
    exact hx (by simpa using hN)
  · have he : (x / y) ^ 2 = D := by
      field_simp
      linear_combination hN
    by_cases hle : w (x / y) ≤ 1
    · apply hsq _ hle
      rw [he, sub_self, map_zero]
      exact zero_lt_one
    · push_neg at hle
      have h2 : w (x / y) ^ 2 = 1 := by rw [← map_pow, he, hD]
      have h3 : (1 : WithZero (Multiplicative ℤ)) < w (x / y) ^ 2 := one_lt_pow' hle two_ne_zero
      rw [h2] at h3
      exact lt_irrefl _ h3

theorem norm_val (hD : w D = 1) (hsq : ∀ e : K, w e ≤ 1 → ¬ w (e ^ 2 - D) < 1) {p q : K}
    (hp : w p ≤ 1) (hq : w q ≤ 1) (h : w p = 1 ∨ w q = 1) : w (p ^ 2 - D * q ^ 2) = 1 := by
  rcases lt_or_eq_of_le hq with hq1 | hq1
  · have hp1 : w p = 1 := h.resolve_right (ne_of_lt hq1)
    have hA : w (p ^ 2) = 1 := by rw [map_pow, hp1, one_pow]
    have hB : w (D * q ^ 2) < 1 := by
      rw [map_mul, map_pow, hD, one_mul]
      exact pow_lt_one₀ zero_le' hq1 two_ne_zero
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left w (by rwa [Valuation.map_neg, hA]), hA]
  · have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hq1
      exact zero_ne_one hq1
    have hsplit : p ^ 2 - D * q ^ 2 = q ^ 2 * ((p / q) ^ 2 - D) := by
      field_simp
    have he : w (p / q) ≤ 1 := by rw [map_div₀, hq1, div_one]; exact hp
    have hle : w ((p / q) ^ 2 - D) ≤ 1 := by
      refine le_trans (Valuation.map_sub w _ _) (max_le ?_ (le_of_eq hD))
      rw [map_pow]
      exact pow_le_one₀ zero_le' he
    have hge : ¬ w ((p / q) ^ 2 - D) < 1 := hsq _ he
    rw [hsplit, map_mul, map_pow, hq1, one_pow, one_mul]
    exact le_antisymm hle (not_lt.1 hge)

end Val

section Quad

open GlobalTheory.CompanionTheory.SW.GoodRing

variable {K A : Type} [Field K] [CommRing A] [Algebra K A]
  (w : Valuation K (WithZero (Multiplicative ℤ))) (B : Module.Basis (Fin 2) K A) {D : K}

theorem mul_conj_div (hBD : B 1 * B 1 = algebraMap K A D) (p q : K)
    (hN : p ^ 2 - D * q ^ 2 ≠ 0) :
    (algebraMap K A p + algebraMap K A q * B 1) *
      (algebraMap K A (p / (p ^ 2 - D * q ^ 2)) +
        algebraMap K A (-q / (p ^ 2 - D * q ^ 2)) * B 1) = 1 := by
  have hc : algebraMap K A (p ^ 2 - D * q ^ 2) * algebraMap K A (1 / (p ^ 2 - D * q ^ 2)) = 1 := by
    rw [← map_mul, mul_one_div_cancel hN, map_one]
  rw [← hc, div_eq_mul_one_div p, div_eq_mul_one_div (-q)]
  simp only [map_mul, map_sub, map_neg, map_pow, ← hBD]
  ring

theorem isField (hB0 : B 0 = 1) (hBD : B 1 * B 1 = algebraMap K A D)
    (hne : ∀ p q : K, p ≠ 0 ∨ q ≠ 0 → p ^ 2 - D * q ^ 2 ≠ 0) : IsField A := by
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h
    have h1 := B.ne_zero 0
    rw [hB0] at h1
    exact h1 h.symm
  · intro x hx
    have hxpq : x = algebraMap K A (B.repr x 0) + algebraMap K A (B.repr x 1) * B 1 := by
      conv_lhs => rw [← B.sum_repr x]
      rw [Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
    have hpq : B.repr x 0 ≠ 0 ∨ B.repr x 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hx
      rw [hxpq, hc.1, hc.2]
      simp
    obtain ⟨p, q, hxe, hpq'⟩ : ∃ p q : K,
        x = algebraMap K A p + algebraMap K A q * B 1 ∧ (p ≠ 0 ∨ q ≠ 0) := ⟨_, _, hxpq, hpq⟩
    have hN := hne p q hpq'
    refine ⟨algebraMap K A (p / (p ^ 2 - D * q ^ 2)) + algebraMap K A (-q / (p ^ 2 - D * q ^ 2)) * B 1, ?_⟩
    have hc : algebraMap K A (p ^ 2 - D * q ^ 2) * algebraMap K A (1 / (p ^ 2 - D * q ^ 2)) = 1 := by
      rw [← map_mul, mul_one_div_cancel hN, map_one]
    rw [hxe, ← hc, div_eq_mul_one_div p, div_eq_mul_one_div (-q)]
    simp only [map_mul, map_sub, map_neg, map_pow, ← hBD]
    ring

variable {ϖ : K}

theorem exists_factor (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (hB0 : B 0 = 1)
    (hBD : B 1 * B 1 = algebraMap K A D) (hD : w D = 1)
    (hsq : ∀ e : K, w e ≤ 1 → ¬ w (e ^ 2 - D) < 1) (x : A) (hx : ∀ j, w (B.repr x j) ≤ 1)
    (hx0 : x ≠ 0) :
    ∃ (i : ℕ) (u u' : A), (∀ j, w (B.repr u j) ≤ 1) ∧ (∀ j, w (B.repr u' j) ≤ 1) ∧ u * u' = 1 ∧
      x = (algebraMap K A ϖ) ^ i * u := by
  have hrep : ∀ a b : K, B.repr (algebraMap K A a + algebraMap K A b * B 1) 0 = a ∧
      B.repr (algebraMap K A a + algebraMap K A b * B 1) 1 = b := by
    intro a b
    have h : algebraMap K A a + algebraMap K A b * B 1 = a • B 0 + b • B 1 := by
      rw [hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [h]
    simp [Finsupp.single_apply]
  obtain ⟨p, q, hxpq, hp, hq⟩ : ∃ p q : K, x = algebraMap K A p + algebraMap K A q * B 1 ∧
      w p ≤ 1 ∧ w q ≤ 1 := by
    refine ⟨B.repr x 0, B.repr x 1, ?_, hx 0, hx 1⟩
    conv_lhs => rw [← B.sum_repr x]
    rw [Fin.sum_univ_two, hB0, Algebra.smul_def, Algebra.smul_def, mul_one]
  subst hxpq
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hx0
    rw [hc.1, hc.2]
    simp
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  obtain ⟨m, hpm, hqm, hor⟩ : ∃ m : ℕ, w p ≤ WithZero.exp (-(m : ℤ)) ∧ w q ≤ WithZero.exp (-(m : ℤ)) ∧
      (w p = WithZero.exp (-(m : ℤ)) ∨ w q = WithZero.exp (-(m : ℤ))) := by
    by_cases hp0 : p = 0
    · obtain ⟨b, hb⟩ := exists_exp w (hpq.resolve_left (not_not.2 hp0)) hq
      exact ⟨b, (by rw [hp0, map_zero]; exact zero_le'), le_of_eq hb, Or.inr hb⟩
    by_cases hq0 : q = 0
    · obtain ⟨a, ha⟩ := exists_exp w hp0 hp
      exact ⟨a, le_of_eq ha, (by rw [hq0, map_zero]; exact zero_le'), Or.inl ha⟩
    obtain ⟨a, ha⟩ := exists_exp w hp0 hp
    obtain ⟨b, hb⟩ := exists_exp w hq0 hq
    rcases le_total a b with hab | hab
    · refine ⟨a, le_of_eq ha, ?_, Or.inl ha⟩
      rw [hb, WithZero.exp_le_exp]
      omega
    · refine ⟨b, ?_, le_of_eq hb, Or.inr hb⟩
      rw [ha, WithZero.exp_le_exp]
      omega
  have hc : w ((ϖ ^ m)⁻¹) = WithZero.exp (m : ℤ) := by
    rw [map_inv₀, val_pow w hϖ m, ← WithZero.exp_neg, neg_neg]
  have hone : WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ) = 1 := by
    rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have hp' : w (p * (ϖ ^ m)⁻¹) ≤ 1 := by
    rw [map_mul, hc, ← hone]
    exact mul_le_mul' hpm le_rfl
  have hq' : w (q * (ϖ ^ m)⁻¹) ≤ 1 := by
    rw [map_mul, hc, ← hone]
    exact mul_le_mul' hqm le_rfl
  have hor' : w (p * (ϖ ^ m)⁻¹) = 1 ∨ w (q * (ϖ ^ m)⁻¹) = 1 := by
    rcases hor with h | h
    · left
      rw [map_mul, hc, h, hone]
    · right
      rw [map_mul, hc, h, hone]
  have hN1 := norm_val w hD hsq hp' hq' hor'
  have hN : (p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hN1
    exact zero_ne_one hN1
  refine ⟨m, algebraMap K A (p * (ϖ ^ m)⁻¹) + algebraMap K A (q * (ϖ ^ m)⁻¹) * B 1,
    algebraMap K A (p * (ϖ ^ m)⁻¹ / ((p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2)) +
      algebraMap K A (-(q * (ϖ ^ m)⁻¹) / ((p * (ϖ ^ m)⁻¹) ^ 2 - D * (q * (ϖ ^ m)⁻¹) ^ 2)) * B 1,
    ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, (hrep _ _).1]
      exact hp'
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, (hrep _ _).2]
      exact hq'
  · intro j
    fin_cases j
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, (hrep _ _).1, map_div₀, hN1, div_one]
      exact hp'
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, (hrep _ _).2, map_div₀, hN1, div_one,
        Valuation.map_neg]
      exact hq'
  · exact mul_conj_div B hBD _ _ hN
  · have e1 : ϖ ^ m * (p * (ϖ ^ m)⁻¹) = p := by field_simp
    have e2 : ϖ ^ m * (q * (ϖ ^ m)⁻¹) = q := by field_simp
    rw [mul_add, ← mul_assoc, ← map_pow, ← map_mul, ← map_mul, e1, e2]

theorem le_of_eq_mul (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (hB0 : B 0 = 1) {i j : ℕ} {u : A}
    (hu : ∀ l, w (B.repr u l) ≤ 1)
    (h : (algebraMap K A ϖ) ^ i = (algebraMap K A ϖ) ^ j * u) : j ≤ i := by
  by_contra hji
  push_neg at hji
  obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hi : IsUnit ((algebraMap K A ϖ) ^ i) := (IsUnit.map (algebraMap K A) (Ne.isUnit hϖ0)).pow i
  have h1 : (1 : A) = algebraMap K A (ϖ ^ (k + 1)) * u := by
    apply hi.mul_left_cancel
    rw [mul_one, map_pow, ← mul_assoc, ← pow_add]
    exact h
  have hu' : u = algebraMap K A ((ϖ ^ (k + 1))⁻¹) := by
    have hk : algebraMap K A ((ϖ ^ (k + 1))⁻¹) * algebraMap K A (ϖ ^ (k + 1)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), map_one]
    calc u = algebraMap K A ((ϖ ^ (k + 1))⁻¹) * (algebraMap K A (ϖ ^ (k + 1)) * u) := by
          rw [← mul_assoc, hk, one_mul]
      _ = algebraMap K A ((ϖ ^ (k + 1))⁻¹) := by rw [← h1, mul_one]
  have hr : B.repr u 0 = (ϖ ^ (k + 1))⁻¹ := by
    rw [hu', Algebra.algebraMap_eq_smul_one, ← hB0, map_smul, B.repr_self]
    simp
  have h2 := hu 0
  rw [hr, map_inv₀, map_pow, hϖ, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h2
  simp at h2
  omega

end Quad

section Place

variable {F : Type} [Field F] [NumberField F]

theorem exists_unif (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : Fv F v, Valued.v ϖ = WithZero.exp (-1 : ℤ) ∧
      ‖ϖ‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  refine ⟨(π : v.adicCompletion F), hv, ?_⟩
  have h0 : WithZero.exp (-1 : ℤ) ≠ 0 := WithZero.exp_ne_zero
  rw [NumberField.FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ h0]
  have he : Multiplicative.toAdd (WithZero.unzero h0) = -1 := rfl
  rw [he, zpow_neg_one, NNReal.coe_inv]
  simp

end Place

private theorem basis_repr_mem_subring_of_change_of_basis {K V ι ι' : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (S : Subring K) (B : Module.Basis ι K V) (B' : Module.Basis ι' K V)
    (hB : ∀ k j, B'.repr (B k) j ∈ S) (y : V) (hy : ∀ k, B.repr y k ∈ S) (j : ι') :
    B'.repr y j ∈ S := by
  rw [← B.sum_repr y]
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy k) (hB k j)

theorem inert_content : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → (¬ ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1) → IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (2 * i))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  intro F E _ _ _ _ _ σ _ d b b₂ D hb0 _ hbD v hD _ H1 H2 hno
  have hB0 : Algebra.TensorProduct.basis (Fv F v) b₂ 0 = 1 := by
    rw [Algebra.TensorProduct.basis_apply, hb0]
    rfl
  have hBD : Algebra.TensorProduct.basis (Fv F v) b₂ 1 * Algebra.TensorProduct.basis (Fv F v) b₂ 1 =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) D) := by
    rw [Algebra.TensorProduct.basis_apply,
      ← Algebra.TensorProduct.includeRight_apply (R := F) (A := Fv F v), ← map_mul, hbD, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hsq : ∀ e : Fv F v, Valued.v e ≤ 1 → ¬ Valued.v (e ^ 2 - algebraMap F (Fv F v) D) < 1 :=
    fun e he hlt => hno ⟨⟨e, he⟩, hlt⟩
  have hfield : IsField (Fv F v ⊗[F] E) :=
    isField (Algebra.TensorProduct.basis (Fv F v) b₂) hB0 hBD
      (fun p q h => norm_ne_zero Valued.v hD hsq h)
  haveI := hfield.nontrivial
  obtain ⟨ϖ, hϖ, hnorm⟩ := exists_unif v
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hϖO : ϖ ∈ v.adicCompletionIntegers F := by
    show Valued.v ϖ ≤ 1
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hincl2 : ∀ j, Algebra.TensorProduct.basis (Fv F v) b₂ j = inclR (Fv F v) (b₂ j) := by
    intro j
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have hincl : ∀ k, Algebra.TensorProduct.basis (Fv F v) b k = inclR (Fv F v) (b k) := by
    intro k
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  have T1 : ∀ y : Fv F v ⊗[F] E,
      (∀ j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr y j ∈ v.adicCompletionIntegers F) → y ∈ intK b v := by
    intro y hy
    simp only [intK, Set.mem_setOf_eq]
    intro k
    exact basis_repr_mem_subring_of_change_of_basis (v.adicCompletionIntegers F).toSubring (Algebra.TensorProduct.basis (Fv F v) b₂)
      (Algebra.TensorProduct.basis (Fv F v) b) (fun j k => by rw [hincl2]; exact H2 j k) y hy k
  have T2 : ∀ y ∈ intK b v, ∀ j,
      (Algebra.TensorProduct.basis (Fv F v) b₂).repr y j ∈ v.adicCompletionIntegers F := by
    intro y hy j
    simp only [intK, Set.mem_setOf_eq] at hy
    exact basis_repr_mem_subring_of_change_of_basis (v.adicCompletionIntegers F).toSubring (Algebra.TensorProduct.basis (Fv F v) b)
      (Algebra.TensorProduct.basis (Fv F v) b₂) (fun k j => by rw [hincl]; exact H1 k j) y hy j
  have hsig : sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  refine ⟨hfield, fun i => (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(IsUnit.map _ (Ne.isUnit hϖ0)).pow i, T1 _ fun j => ?_⟩
    dsimp only
    rw [← map_pow, Algebra.algebraMap_eq_smul_one, ← hB0, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, smul_eq_mul]
    refine (v.adicCompletionIntegers F).mul_mem _ _ ((v.adicCompletionIntegers F).pow_mem hϖO i) ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem
  · intro i
    refine ⟨ϖ ^ (2 * i), ?_, ?_⟩
    · rw [map_pow (algebraMap (Fv F v) (Fv F v ⊗[F] E)), map_pow (sigR (Fv F v) σ), hsig, ← pow_add, two_mul]
    · rw [norm_pow, hnorm, inv_pow]
      simp [qv]
  · intro x hx hux
    obtain ⟨i, u, u', hu, hu', huu, hxu⟩ := exists_factor Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂)
      hϖ hB0 hBD hD hsq x (fun j => T2 x hx j) hux.ne_zero
    exact ⟨i, u, T1 u hu, u', T1 u' hu', huu, hxu⟩
  · intro i j u hu u' hu' huu h
    have h' : (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i = (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ j * u := h
    have h1 := le_of_eq_mul Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂) hϖ hB0 (fun l => T2 u hu l) h'
    have h'' : (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ j = (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) ^ i * u' := by
      rw [h', mul_assoc, huu, mul_one]
    have h2 := le_of_eq_mul Valued.v (Algebra.TensorProduct.basis (Fv F v) b₂) hϖ hB0 (fun l => T2 u' hu' l) h''
    omega

end GlobalTheory.CompanionTheory.SW.QuadField
