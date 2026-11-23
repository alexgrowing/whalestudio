import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.NormOneSplit

open Polynomial in

theorem exists_good {K : Type} [Field K] [CharZero K] (a p q : K) (ha : a ≠ 0) :
    ∃ m : K, m ≠ 0 ∧ a - m * p ≠ 0 ∧ a - m⁻¹ * q ≠ 0 ∧ 2 * a - m * p - m⁻¹ * q ≠ 0 := by
  set P1 : K[X] := C a - C p * X with hP1
  set P2 : K[X] := C a * X - C q with hP2
  set P3 : K[X] := C (2 * a) * X - C p * X ^ 2 - C q with hP3
  have h1 : P1 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 0) h
    simp [hP1] at this
    exact ha this
  have h2 : P2 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 1) h
    simp [hP2, Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact ha this
  have h3 : P3 ≠ 0 := by
    intro h
    have := congrArg (fun f => Polynomial.coeff f 1) h
    simp [hP3, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at this
    exact ha this
  have hP : (X * P1 * P2 * P3 : K[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero X_ne_zero h1) h2) h3
  have hex : ∃ m : K, (X * P1 * P2 * P3 : K[X]).eval m ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hP (Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_univ.mono fun m _ => hcon m))
  obtain ⟨m, hm⟩ := hex
  simp only [eval_mul, eval_X] at hm
  have hm0 : m ≠ 0 := fun h => hm (by simp [h])
  have e1 : a - m * p ≠ 0 := by
    intro h
    apply hm
    have : eval m P1 = 0 := by simp [hP1]; linear_combination h
    simp [this]
  have e2 : a * m - q ≠ 0 := by
    intro h
    apply hm
    have : eval m P2 = 0 := by simp [hP2]; linear_combination h
    simp [this]
  have e3 : 2 * a * m - p * m ^ 2 - q ≠ 0 := by
    intro h
    apply hm
    have : eval m P3 = 0 := by simp [hP3]; linear_combination h
    simp [this]
  refine ⟨m, hm0, e1, ?_, ?_⟩
  · intro h
    apply e2
    have : a * m - q = m * (a - m⁻¹ * q) := by field_simp
    rw [this, h, mul_zero]
  · intro h
    apply e3
    have : 2 * a * m - p * m ^ 2 - q = m * (2 * a - m * p - m⁻¹ * q) := by field_simp
    rw [this, h, mul_zero]

section Ring

variable {K R : Type} [Field K] [CharZero K] [CommRing R] [Nontrivial R] [Algebra K R]

theorem normOneGen_of_idem (c : R →+* R) (hK : ∀ a : K, c (algebraMap K R a) = algebraMap K R a)
    (e : R) (he : e * e = e) (hs : e + c e = 1) (hz : e * c e = 0)
    (hsp : ∀ r : R, ∃ a b : K, r = algebraMap K R a * e + algebraMap K R b * c e) :
    NormOneGen c := by
  set f := c e with hf
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hcf : c f = e := by
    have h := congrArg c hs
    rw [map_add, map_one] at h
    have : c f = 1 - f := by rw [← h]; ring
    rw [this, ← hs]; ring
  have he0 : e ≠ 0 := by
    intro h
    have hf0 : f = 0 := by rw [hf, h, map_zero]
    rw [h, hf0, add_zero] at hs
    exact zero_ne_one hs
  have hinj : ∀ x : K, algebraMap K R x * e = 0 → x = 0 := by
    intro x hx
    by_contra hne
    apply he0
    calc e = algebraMap K R (x⁻¹ * x) * e := by rw [inv_mul_cancel₀ hne, map_one, one_mul]
      _ = algebraMap K R x⁻¹ * (algebraMap K R x * e) := by rw [map_mul]; ring
      _ = 0 := by rw [hx, mul_zero]
  have hunit : ∀ x y : K, x ≠ 0 → y ≠ 0 → IsUnit (algebraMap K R x * e + algebraMap K R y * f) := by
    intro x y hx hy
    refine IsUnit.of_mul_eq_one (algebraMap K R x⁻¹ * e + algebraMap K R y⁻¹ * f) ?_
    have h1 : algebraMap K R x * algebraMap K R x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hx, map_one]
    have h2 : algebraMap K R y * algebraMap K R y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hy, map_one]
    calc _ = (algebraMap K R x * algebraMap K R x⁻¹) * (e * e)
          + (algebraMap K R y * algebraMap K R y⁻¹) * (f * f)
          + (algebraMap K R x * algebraMap K R y⁻¹ + algebraMap K R y * algebraMap K R x⁻¹) * (e * f) := by ring
      _ = 1 := by rw [h1, h2, he, hff, hz, mul_zero, add_zero, one_mul, one_mul]; exact hs
  intro α p hα hcα
  obtain ⟨a, b, hab⟩ := hsp α
  obtain ⟨p₁, p₂, hp⟩ := hsp p
  have hba : a = b := by
    have h := hcα
    rw [hab, map_add, map_mul, map_mul, hK, hK, hcf, ← hf] at h
    have h' := congrArg (fun t => t * e) h
    have : algebraMap K R (a - b) * e = 0 := by
      rw [map_sub]
      linear_combination (-1 : R) * h' + (algebraMap K R b - algebraMap K R a) * he
        + (algebraMap K R a - algebraMap K R b) * hz
    exact sub_eq_zero.1 (hinj _ this)
  subst hba
  have ha : a ≠ 0 := by
    rintro rfl
    have h0 : α * e = 0 := by
      rw [hab, map_zero, zero_mul, zero_mul, add_zero, zero_mul]
    exact he0 (hα.mul_right_eq_zero.1 h0)
  obtain ⟨m, hm, c1, c2, c3⟩ := exists_good a p₁ p₂ ha
  have hmm : algebraMap K R m * algebraMap K R m⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hm, map_one]
  have hμp : (algebraMap K R m * e + algebraMap K R m⁻¹ * f) * p =
      algebraMap K R (m * p₁) * e + algebraMap K R (m⁻¹ * p₂) * f := by
    rw [hp, map_mul, map_mul]
    linear_combination (algebraMap K R m * algebraMap K R p₁) * he +
      (algebraMap K R m⁻¹ * algebraMap K R p₂) * hff +
      (algebraMap K R m * algebraMap K R p₂ + algebraMap K R m⁻¹ * algebraMap K R p₁) * hz
  refine ⟨algebraMap K R m * e + algebraMap K R m⁻¹ * f, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, hK, hcf]
    rw [← hf]
    linear_combination (algebraMap K R m * algebraMap K R m⁻¹) * he +
      (algebraMap K R m * algebraMap K R m⁻¹) * hff +
      (algebraMap K R m ^ 2 + algebraMap K R m⁻¹ ^ 2) * hz + (e + f) * hmm + hs
  · rw [hμp, hab]
    have := hunit (a - m * p₁) (a - m⁻¹ * p₂) c1 c2
    convert this using 1
    simp only [map_sub]; ring
  · rw [hμp, hab]
    simp only [map_add, map_mul, hK, hcf]
    have := hunit (2 * a - m * p₁ - m⁻¹ * p₂) (2 * a - m * p₁ - m⁻¹ * p₂) c3 c3
    convert this using 1
    simp only [map_sub, map_mul, map_ofNat]; ring

end Ring

end GlobalTheory.CompanionTheory.SaGen.NormOneSplit

open GlobalTheory.CompanionTheory.SaGen.NormOneSplit in

theorem GlobalTheory.CompanionTheory.SaGen.normOneGen_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → NormOneGen (sigR K σ) := by
  intro F E _ _ _ _ _ σ hcm K _ _ e he hs hz
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hrank : Module.finrank K (K ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hcm.2.2.1
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hK : ∀ a : K, sigR K σ (algebraMap K (K ⊗[F] E) a) = algebraMap K (K ⊗[F] E) a := by
    intro a
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  refine normOneGen_of_idem (K := K) (sigR K σ) hK e he hs hz ?_
  set f := sigR K σ e with hf
  have he0 : e ≠ 0 := by
    intro h
    have hf0 : f = 0 := by rw [hf, h, map_zero]
    rw [h, hf0, add_zero] at hs
    exact zero_ne_one hs
  have hf0 : f ≠ 0 := by
    intro h
    have h1 : e = 1 := by rw [h, add_zero] at hs; exact hs
    have : f = 1 := by rw [hf, h1, map_one]
    rw [this] at h
    exact one_ne_zero h
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def] at hst
    have h1 : algebraMap K (K ⊗[F] E) s * e = 0 := by
      linear_combination e * hst - algebraMap K (K ⊗[F] E) s * he - algebraMap K (K ⊗[F] E) t * hz
    have h2 : algebraMap K (K ⊗[F] E) t * f = 0 := by
      linear_combination f * hst - algebraMap K (K ⊗[F] E) s * hz - algebraMap K (K ⊗[F] E) t * hff
    have key : ∀ (x : K) (y : K ⊗[F] E), y ≠ 0 → algebraMap K (K ⊗[F] E) x * y = 0 → x = 0 := by
      intro x y hy hxy
      by_contra hx
      apply hy
      calc y = algebraMap K (K ⊗[F] E) (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
        _ = algebraMap K (K ⊗[F] E) x⁻¹ * (algebraMap K (K ⊗[F] E) x * y) := by rw [map_mul]; ring
        _ = 0 := by rw [hxy, mul_zero]
    exact ⟨key s e he0 h1, key t f hf0 h2⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by simp [hrank])
  intro r
  have hr : r ∈ Submodule.span K (Set.range ![e, f]) := by rw [htop]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hr
  obtain ⟨a, b, hab⟩ := hr
  exact ⟨a, b, by rw [← hab, Algebra.smul_def, Algebra.smul_def]⟩
