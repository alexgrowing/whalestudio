import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Polynomial

def laurentSubalgebra : Subalgebra ℂ (RatFunc ℂ) :=
  Algebra.adjoin ℂ {RatFunc.X, RatFunc.X⁻¹}

theorem X_mem_laurentSubalgebra : (RatFunc.X : RatFunc ℂ) ∈ laurentSubalgebra :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem X_inv_mem_laurentSubalgebra : (RatFunc.X : RatFunc ℂ)⁻¹ ∈ laurentSubalgebra :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem C_mem_laurentSubalgebra (c : ℂ) : RatFunc.C c ∈ laurentSubalgebra := by
  rw [← RatFunc.algebraMap_eq_C]
  exact Subalgebra.algebraMap_mem _ c

theorem algebraMap_mem_laurentSubalgebra (P : ℂ[X]) :
    algebraMap ℂ[X] (RatFunc ℂ) P ∈ laurentSubalgebra := by
  refine Polynomial.induction_on P (fun a => ?_) (fun p q hp hq => ?_) (fun k a h => ?_)
  · rw [RatFunc.algebraMap_C]
    exact C_mem_laurentSubalgebra a
  · rw [map_add]
    exact add_mem hp hq
  · rw [pow_succ, ← mul_assoc, map_mul, RatFunc.algebraMap_X]
    exact mul_mem h X_mem_laurentSubalgebra

theorem mem_laurentSubalgebra_iff {R : RatFunc ℂ} :
    R ∈ laurentSubalgebra ↔
      ∃ (P : ℂ[X]) (k : ℕ), R = algebraMap ℂ[X] (RatFunc ℂ) P / RatFunc.X ^ k := by
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  constructor
  · intro hR
    induction hR using Algebra.adjoin_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X, 0, by simp [RatFunc.algebraMap_X]⟩
      · exact ⟨1, 1, by simp⟩
    | algebraMap r =>
      exact ⟨Polynomial.C r, 0, by simp [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]⟩
    | add x y _ _ hx hy =>
      obtain ⟨P, k, rfl⟩ := hx
      obtain ⟨Q, l, rfl⟩ := hy
      refine ⟨P * Polynomial.X ^ l + Q * Polynomial.X ^ k, k + l, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X]
      field_simp
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨P, k, rfl⟩ := hx
      obtain ⟨Q, l, rfl⟩ := hy
      refine ⟨P * Q, k + l, ?_⟩
      rw [map_mul, pow_add]
      field_simp
  · rintro ⟨P, k, rfl⟩
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (algebraMap_mem_laurentSubalgebra P) (pow_mem X_inv_mem_laurentSubalgebra k)

theorem eval_div_algebraMap (P Q : ℂ[X]) {x : ℂ} (hx : Q.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q).eval (RingHom.id ℂ) x =
      P.eval x / Q.eval x := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    simp at hx
  set y := algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) Q with hydef
  have hy : (y.denom).eval₂ (RingHom.id ℂ) x ≠ 0 := by
    intro h0
    apply hx
    have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) x
      (RatFunc.denom_div_dvd P Q) h0
    simpa [Polynomial.eval₂_id] using this
  have hQd : ((algebraMap ℂ[X] (RatFunc ℂ) Q).denom).eval₂ (RingHom.id ℂ) x ≠ 0 := by
    rw [RatFunc.denom_algebraMap]
    simp
  have hmul := RatFunc.eval_mul (RingHom.id ℂ) x hy hQd
  have hyQ : y * algebraMap ℂ[X] (RatFunc ℂ) Q = algebraMap ℂ[X] (RatFunc ℂ) P :=
    div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hQ)
  rw [hyQ, RatFunc.eval_algebraMap, RatFunc.eval_algebraMap] at hmul
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Polynomial.eval₂_id] at hmul
  rw [eq_div_iff hx, ← hmul]

theorem eq_of_eval_eq {R₁ R₂ : RatFunc ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → R₁.eval (RingHom.id ℂ) x = R₂.eval (RingHom.id ℂ) x) :
    R₁ = R₂ := by
  set Q : ℂ[X] := R₁.num * R₂.denom - R₂.num * R₁.denom with hQdef
  have hT : {x : ℂ | x ≠ 0 ∧ ‖x‖ < ε}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((ε / ((k : ℝ) + 2) : ℝ) : ℂ))
      ?_ ?_
    · intro a b hab
      have ha : (0 : ℝ) < (a : ℝ) + 2 := by positivity
      have hb : (0 : ℝ) < (b : ℝ) + 2 := by positivity
      have h1 : ε / ((a : ℝ) + 2) = ε / ((b : ℝ) + 2) := Complex.ofReal_injective hab
      rw [div_eq_div_iff ha.ne' hb.ne'] at h1
      have h2 : (b : ℝ) + 2 = (a : ℝ) + 2 := mul_left_cancel₀ hε.ne' h1
      have h3 : (a : ℝ) = b := by linarith
      exact_mod_cast h3
    · intro k
      have hk : 0 < ε / ((k : ℝ) + 2) := by positivity
      refine ⟨Complex.ofReal_ne_zero.2 hk.ne', ?_⟩
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
      exact div_lt_self hε (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hroots : ({x | IsRoot R₁.denom x} ∪ {x | IsRoot R₂.denom x}).Finite :=
    (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero _)).union
      (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero _))
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (hT.sdiff hroots).mono ?_
    rintro x ⟨⟨hx0, hxε⟩, hxr⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Polynomial.IsRoot.def] at hxr
    have h1 := h x hx0 hxε
    simp only [RatFunc.eval, Polynomial.eval₂_id] at h1
    rw [div_eq_div_iff hxr.1 hxr.2] at h1
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hQdef, Polynomial.eval_sub,
      Polynomial.eval_mul, h1, sub_self]
  rw [← RatFunc.num_div_denom R₁, ← RatFunc.num_div_denom R₂,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _)), ← map_mul, ← map_mul]
  congr 1
  exact sub_eq_zero.1 hQ

section Ideal

variable {I : Submodule ℂ (RatFunc ℂ)}

theorem X_pow_mul_mem (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (k : ℕ) {R : RatFunc ℂ} (hR : R ∈ I) :
    RatFunc.X ^ k * R ∈ I := by
  induction k with
  | zero => simpa using hR
  | succ k ih =>
    rw [pow_succ, mul_comm _ RatFunc.X, mul_assoc]
    exact hX _ ih

theorem X_inv_pow_mul_mem (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I) (k : ℕ) {R : RatFunc ℂ}
    (hR : R ∈ I) : RatFunc.X⁻¹ ^ k * R ∈ I := by
  induction k with
  | zero => simpa using hR
  | succ k ih =>
    rw [pow_succ, mul_comm _ RatFunc.X⁻¹, mul_assoc]
    exact hXinv _ ih

theorem algebraMap_mul_mem (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (P : ℂ[X]) {R : RatFunc ℂ}
    (hR : R ∈ I) : algebraMap ℂ[X] (RatFunc ℂ) P * R ∈ I := by
  suffices h : ∀ R ∈ I, algebraMap ℂ[X] (RatFunc ℂ) P * R ∈ I from h R hR
  refine Polynomial.induction_on P (fun a => ?_) (fun p q hp hq => ?_) (fun k a h => ?_)
  · intro R hR
    rw [RatFunc.algebraMap_C, ← RatFunc.smul_eq_C_mul]
    exact I.smul_mem a hR
  · intro R hR
    rw [map_add, add_mul]
    exact I.add_mem (hp R hR) (hq R hR)
  · intro R hR
    have : algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C a * Polynomial.X ^ (k + 1)) * R =
        RatFunc.X * (algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C a * Polynomial.X ^ k) * R) := by
      rw [pow_succ, ← mul_assoc, map_mul _ (Polynomial.C a * Polynomial.X ^ k), RatFunc.algebraMap_X]
      ring
    rw [this]
    exact hX _ (h R hR)

theorem laurent_mul_mem (hX : ∀ R ∈ I, RatFunc.X * R ∈ I)
    (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I) {L : RatFunc ℂ} (hL : L ∈ laurentSubalgebra)
    {R : RatFunc ℂ} (hR : R ∈ I) : L * R ∈ I := by
  obtain ⟨P, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL
  rw [div_eq_mul_inv, ← inv_pow, mul_assoc]
  exact algebraMap_mul_mem hX P (X_inv_pow_mul_mem hXinv k hR)

end Ideal

theorem dvd_of_inv_eq_laurent_div {P P' : ℂ[X]} (hP' : P'.eval 0 ≠ 0) {L : RatFunc ℂ}
    (hL : L ∈ laurentSubalgebra)
    (h : (algebraMap ℂ[X] (RatFunc ℂ) P')⁻¹ = L / algebraMap ℂ[X] (RatFunc ℂ) P) : P' ∣ P := by
  have hP'0 : P' ≠ 0 := by
    rintro rfl
    simp at hP'
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, inv_eq_zero] at h
    exact RatFunc.algebraMap_ne_zero hP'0 h
  obtain ⟨Q, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hφP := RatFunc.algebraMap_ne_zero hP0
  have hφP' := RatFunc.algebraMap_ne_zero hP'0
  have heq : P * Polynomial.X ^ k = Q * P' := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp at h
    linear_combination h
  have hXP' : ¬ Polynomial.X ∣ P' := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hP'
  have hcop : IsCoprime P' (Polynomial.X ^ k) :=
    Irreducible.coprime_pow_of_not_dvd k Polynomial.irreducible_X hXP'
  exact hcop.dvd_of_dvd_mul_right ⟨Q, by rw [heq, mul_comm]⟩

theorem eq_of_laurent_div_iff {P P' : ℂ[X]} (hP : P.eval 0 = 1) (hP' : P'.eval 0 = 1)
    (h : ∀ R : RatFunc ℂ, (∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P) ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P') : P = P' := by
  have h1 : P' ∣ P := by
    obtain ⟨L, hL, hLeq⟩ := (h (algebraMap ℂ[X] (RatFunc ℂ) P')⁻¹).2
      ⟨1, one_mem _, by rw [one_div]⟩
    exact dvd_of_inv_eq_laurent_div (by rw [hP']; exact one_ne_zero) hL hLeq
  have h2 : P ∣ P' := by
    obtain ⟨L, hL, hLeq⟩ := (h (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹).1
      ⟨1, one_mem _, by rw [one_div]⟩
    exact dvd_of_inv_eq_laurent_div (by rw [hP]; exact one_ne_zero) hL hLeq
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have hBA : B * A = 1 := by
    have : P * (B * A) = P * 1 := by
      rw [mul_one, ← mul_assoc, ← hB, ← hA]
    exact mul_left_cancel₀ hP0 this
  obtain ⟨a, -, ha⟩ := Polynomial.isUnit_iff.1 (IsUnit.of_mul_eq_one_right B hBA)
  have ha1 : a = 1 := by
    have := congrArg (Polynomial.eval 0) hA
    rw [Polynomial.eval_mul, ← ha, Polynomial.eval_C, hP, hP', one_mul] at this
    exact this.symm
  rw [hA, ← ha, ha1, map_one, mul_one]

theorem existsUnique_eq_laurent_div (I : Submodule ℂ (RatFunc ℂ))
    (hX : ∀ R ∈ I, RatFunc.X * R ∈ I) (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I)
    (h1 : (1 : RatFunc ℂ) ∈ I)
    (hD : ∃ D : ℂ[X], D ≠ 0 ∧ ∀ R ∈ I, algebraMap ℂ[X] (RatFunc ℂ) D * R ∈ laurentSubalgebra) :
    ∃! P : ℂ[X], P.eval 0 = 1 ∧
      ∀ R : RatFunc ℂ, R ∈ I ↔
        ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P := by
  classical
  obtain ⟨D, hD0, hDI⟩ := hD
  have hXne : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have hφD : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := RatFunc.algebraMap_ne_zero hD0

  let J : Ideal ℂ[X] :=
    { carrier := {Q | algebraMap ℂ[X] (RatFunc ℂ) Q / algebraMap ℂ[X] (RatFunc ℂ) D ∈ I}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add, add_div] at ha hb ⊢
        exact I.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, zero_div]
        exact I.zero_mem
      smul_mem' := fun c {Q} hQ => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_div_assoc] at hQ ⊢
        exact algebraMap_mul_mem hX c hQ }
  have hJ : ∀ Q, Q ∈ J ↔
      algebraMap ℂ[X] (RatFunc ℂ) Q / algebraMap ℂ[X] (RatFunc ℂ) D ∈ I := fun Q => Iff.rfl
  set G := Submodule.IsPrincipal.generator J with hGdef
  have hGJ : G ∈ J := Submodule.IsPrincipal.generator_mem J
  have hdvd : ∀ Q, Q ∈ J ↔ G ∣ Q := fun Q => Submodule.IsPrincipal.mem_iff_generator_dvd J
  have hDJ : D ∈ J := by
    rw [hJ, div_self hφD]
    exact h1
  have hG0 : G ≠ 0 := by
    intro h
    have := (hdvd D).1 hDJ
    rw [h, zero_dvd_iff] at this
    exact hD0 this
  have hφG : algebraMap ℂ[X] (RatFunc ℂ) G ≠ 0 := RatFunc.algebraMap_ne_zero hG0
  have hGX : ¬ Polynomial.X ∣ G := by
    rintro ⟨G', hG'⟩
    have hG'0 : G' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hG'
      exact hG0 hG'
    have hG'J : G' ∈ J := by
      rw [hJ]
      have : algebraMap ℂ[X] (RatFunc ℂ) G' / algebraMap ℂ[X] (RatFunc ℂ) D =
          RatFunc.X⁻¹ * (algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D) := by
        rw [hG', map_mul, RatFunc.algebraMap_X]
        field_simp
      rw [this]
      exact hXinv _ hGJ
    have hle := Polynomial.natDegree_le_of_dvd ((hdvd G').1 hG'J) hG'0
    rw [hG', Polynomial.natDegree_mul Polynomial.X_ne_zero hG'0, Polynomial.natDegree_X] at hle
    omega

  have hchar : ∀ R, R ∈ I ↔ ∃ L ∈ laurentSubalgebra,
      R = algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D * L := by
    intro R
    constructor
    · intro hR
      obtain ⟨P, k, hPk⟩ := mem_laurentSubalgebra_iff.1 (hDI R hR)
      have hPJ : P ∈ J := by
        rw [hJ]
        have : algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) D =
            RatFunc.X ^ k * R := by
          rw [eq_div_iff (pow_ne_zero _ hXne)] at hPk
          rw [div_eq_iff hφD, ← hPk]
          ring
        rw [this]
        exact X_pow_mul_mem hX k hR
      obtain ⟨H, rfl⟩ := (hdvd P).1 hPJ
      refine ⟨algebraMap ℂ[X] (RatFunc ℂ) H / RatFunc.X ^ k,
        mem_laurentSubalgebra_iff.2 ⟨H, k, rfl⟩, ?_⟩
      rw [map_mul, eq_div_iff (pow_ne_zero _ hXne)] at hPk
      field_simp
      linear_combination hPk
    · rintro ⟨L, hL, rfl⟩
      rw [mul_comm]
      exact laurent_mul_mem hX hXinv hL hGJ

  obtain ⟨L1, hL1, h1eq⟩ := (hchar 1).1 h1
  obtain ⟨H, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL1
  have hDXk : D * Polynomial.X ^ k = G * H := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp at h1eq
    linear_combination h1eq
  have hGD : G ∣ D := by
    have hcop : IsCoprime G (Polynomial.X ^ k) :=
      Irreducible.coprime_pow_of_not_dvd k Polynomial.irreducible_X hGX
    exact hcop.dvd_of_dvd_mul_right ⟨H, hDXk⟩
  obtain ⟨E, hE⟩ := hGD
  have hE0 : E ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hE
    exact hD0 hE
  obtain ⟨E₁, hE₁, hE₁X⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd E hE0 0
  simp only [map_zero, sub_zero] at hE₁ hE₁X
  set j := E.rootMultiplicity 0
  have hc : E₁.eval 0 ≠ 0 := by
    intro h
    apply hE₁X
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact h
  set c := E₁.eval 0 with hcdef
  have hE₁0 : E₁ ≠ 0 := by
    rintro rfl
    exact hE₁X (dvd_zero _)
  have hφE₁ : algebraMap ℂ[X] (RatFunc ℂ) E₁ ≠ 0 := RatFunc.algebraMap_ne_zero hE₁0
  have hCc : RatFunc.C c ≠ 0 := by
    rw [← RatFunc.algebraMap_eq_C]
    exact (_root_.map_ne_zero _).2 hc
  have hGD' : algebraMap ℂ[X] (RatFunc ℂ) G / algebraMap ℂ[X] (RatFunc ℂ) D =
      (RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) E₁)⁻¹ := by
    rw [hE, hE₁, map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp
  have hφP : algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c⁻¹ * E₁) =
      (RatFunc.C c)⁻¹ * algebraMap ℂ[X] (RatFunc ℂ) E₁ := by
    rw [map_mul, RatFunc.algebraMap_C, map_inv₀]
  have hexists : (Polynomial.C c⁻¹ * E₁).eval 0 = 1 ∧ ∀ R : RatFunc ℂ, R ∈ I ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c⁻¹ * E₁) := by
    refine ⟨by rw [Polynomial.eval_mul, Polynomial.eval_C, ← hcdef, inv_mul_cancel₀ hc], ?_⟩
    intro R
    rw [hchar R, hφP, hGD']
    constructor
    · rintro ⟨L, hL, rfl⟩
      refine ⟨L * (RatFunc.X ^ j)⁻¹ * (RatFunc.C c)⁻¹,
        mul_mem (mul_mem hL (by rw [← inv_pow]; exact pow_mem X_inv_mem_laurentSubalgebra j))
          (by rw [← map_inv₀]; exact C_mem_laurentSubalgebra _), ?_⟩
      field_simp
    · rintro ⟨L, hL, rfl⟩
      refine ⟨L * RatFunc.X ^ j * RatFunc.C c,
        mul_mem (mul_mem hL (pow_mem X_mem_laurentSubalgebra j)) (C_mem_laurentSubalgebra c), ?_⟩
      field_simp
  refine ⟨Polynomial.C c⁻¹ * E₁, hexists, ?_⟩
  rintro P' ⟨hP'0, hP'⟩
  exact (eq_of_laurent_div_iff hexists.1 hP'0 fun R => (hexists.2 R).symm.trans (hP' R)).symm

end GodementJacquet

end GroundTheory.Automorphic
