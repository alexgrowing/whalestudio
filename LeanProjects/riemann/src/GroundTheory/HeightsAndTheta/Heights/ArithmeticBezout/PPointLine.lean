import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace PointLine

variable {n : ℕ}

def pairing (y : Fin n → ℂ) : MvPolynomial (Fin 1 × Fin n) ℂ :=
  ∑ j, C (y j) * X ((0 : Fin 1), j)

theorem eval_pairing (y : Fin n → ℂ) (u : Fin 1 × Fin n → ℂ) :
    eval u (pairing y) = ∑ j, y j * u (0, j) := by
  simp [pairing]

theorem coeff_pairing (y : Fin n → ℂ) (j : Fin n) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (pairing y) = y j := by
  classical
  simp [pairing, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]

theorem exists_ne_zero {y : Fin n → ℂ} (hy : y ≠ 0) : ∃ a, y a ≠ 0 := by
  by_contra h
  push Not at h
  exact hy (funext h)

theorem eval_smul_of_isHomogeneous {φ : MvPolynomial (Fin n) ℂ} {m : ℕ} (hφ : φ.IsHomogeneous m)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ m * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem smul_mem_zeroSet {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W)
    {x : Fin n → ℂ} (hx : ∀ q ∈ W, eval x q = 0) (t : ℂ) : ∀ q ∈ W, eval (t • x) q = 0 := by
  intro q hq
  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

theorem pairing_dvd_of_vanish {y : Fin n → ℂ} (hy : y ≠ 0) (f : MvPolynomial (Fin 1 × Fin n) ℂ)
    (hf : ∀ u, eval u (pairing y) = 0 → eval u f = 0) : pairing y ∣ f := by
  obtain ⟨a, ha⟩ := exists_ne_zero hy
  set ℓ := pairing y with hℓ
  let c : Fin 1 × Fin n → ℂ := Pi.single ((0 : Fin 1), a) (y a)⁻¹
  let s : Fin 1 × Fin n → MvPolynomial (Fin 1 × Fin n) ℂ := fun ij => X ij - C (c ij) * ℓ
  have hsum : ∀ L : ℂ, ∑ j, y j * c (0, j) * L = L := by
    intro L
    rw [← Finset.sum_mul]
    have : ∑ j, y j * c (0, j) = y a * (y a)⁻¹ := by
      rw [Finset.sum_eq_single a]
      · simp [c]
      · intro j _ hj
        simp [c, hj]
      · simp
    rw [this, mul_inv_cancel₀ ha, one_mul]
  have hs0 : bind₁ s f = 0 := by
    apply MvPolynomial.funext
    intro u
    rw [map_zero]
    have he : eval u (bind₁ s f) = eval (fun ij => eval u (s ij)) f := by
      simp only [eval, eval₂Hom_bind₁]
    rw [he]
    apply hf
    rw [eval_pairing]
    simp only [s, map_sub, map_mul, eval_X, eval_C, mul_sub, Finset.sum_sub_distrib]
    have h2 : ∀ j, y j * (c (0, j) * eval u ℓ) = y j * c (0, j) * eval u ℓ := fun j => by ring
    simp only [h2, hsum]
    rw [hℓ, eval_pairing, sub_self]
  have hmem : f - bind₁ s f ∈ Ideal.span {ℓ} := by
    have hcomp : (Ideal.Quotient.mkₐ ℂ (Ideal.span {ℓ})).comp (bind₁ s) =
        Ideal.Quotient.mkₐ ℂ (Ideal.span {ℓ}) := by
      apply MvPolynomial.algHom_ext
      intro ij
      simp only [AlgHom.comp_apply, bind₁_X_right, s, Ideal.Quotient.mkₐ_eq_mk, map_sub, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ℓ), mul_zero, sub_zero]
    have h := DFunLike.congr_fun hcomp f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
    exact Ideal.Quotient.eq.mp h.symm
  rw [hs0, sub_zero, Ideal.mem_span_singleton] at hmem
  exact hmem

theorem irreducible_pairing {y : Fin n → ℂ} (hy : y ≠ 0) : Irreducible (pairing y) := by
  obtain ⟨a, ha⟩ := exists_ne_zero hy
  have hne : pairing y ≠ 0 := fun h => ha (by rw [← coeff_pairing y a, h, coeff_zero])
  have hhom : (pairing y).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _
  refine irreducible_of_totalDegree_eq_one (hhom.totalDegree hne) fun c hc => ?_
  have h := hc (Finsupp.single ((0 : Fin 1), a) 1)
  rw [coeff_pairing] at h
  exact isUnit_iff_ne_zero.mpr (by rintro rfl; exact ha (zero_dvd_iff.mp h))

theorem eq_smul_of_associated {x y : Fin n → ℂ} (h : Associated (pairing y) (pairing x)) :
    ∃ t : ℂ, x = t • y := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, -, hc⟩ := (isUnit_iff_eq_C_of_isReduced).mp u.isUnit
  refine ⟨c, funext fun j => ?_⟩
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) hu
  rw [hc, mul_comm, coeff_C_mul, coeff_pairing, coeff_pairing] at h
  rw [← h, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem chowForm_vanish {W : Ideal (MvPolynomial (Fin n) ℂ)} {g : MvPolynomial (Fin 1 × Fin n) ℂ}
    (hg : IsChowForm W 1 g) {y : Fin n → ℂ} (hy0 : y ≠ 0) (hy : ∀ q ∈ W, eval y q = 0)
    (u : Fin 1 × Fin n → ℂ) (hu : eval u (pairing y) = 0) : eval u g = 0 := by
  set φ := algebraMap ℂ (AlgebraicClosure ℂ) with hφ
  have hu' : ∑ j, u (0, j) * y j = 0 := by
    rw [eval_pairing] at hu
    simpa [mul_comm] using hu
  have hinc : (φ ∘ u) ∈ incidence W 1 := by
    refine ⟨φ ∘ y, ?_, ?_, ?_⟩
    · intro h
      apply hy0
      funext j
      have := congrFun h j
      simpa using this
    · intro q hq
      rw [aeval_algebraMap_apply]
      simp [hy q hq]
    · intro i
      obtain rfl := Subsingleton.elim i 0
      simp only [Function.comp_apply, ← map_mul, ← map_sum, hu', map_zero]
  have h := (hg.2 g).mpr dvd_rfl _ hinc
  rw [aeval_algebraMap_apply] at h
  simpa using h

end PointLine

open PointLine in

theorem PointLine.proof : PointLine.Statement := by
  classical
  intro n W g hW hg
  have := hW.isPrime
  set V : Set (Fin n → ℂ) := {x | ∀ q ∈ W, eval x q = 0} with hV
  have hNS : ∀ q, q ∈ W ↔ ∀ x ∈ V, eval x q = 0 := by
    intro q
    rw [← SetLike.ext_iff.mp (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W) q,
      mem_vanishingIdeal_iff]
    have hae : ∀ (x : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ), aeval x p = eval x p := fun _ _ => rfl
    simp only [mem_zeroLocus_iff, hae, hV, Set.mem_ofPred_eq]
  have hcone : ∀ x ∈ V, ∀ t : ℂ, t • x ∈ V := fun x hx t => smul_mem_zeroSet hW.isHomog hx t
  have hdvd : ∀ x ∈ V, x ≠ 0 → pairing x ∣ g := fun x hx hx0 =>
    pairing_dvd_of_vanish hx0 g (chowForm_vanish hg hx0 hx)
  have hrel : ∀ S : Set (Fin n → ℂ), vanishingIdeal ℂ S ≤ W → ∃ y ∈ S, y ≠ 0 := by
    intro S hS
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hW.isRelevant
    refine hj (hS ?_)
    rw [mem_vanishingIdeal_iff]
    intro x hx
    simp [h x hx]
  obtain ⟨y₀, hy₀, hy₀0⟩ := hrel V (fun q hq => (hNS q).mpr fun x hx => by
    simpa using (mem_vanishingIdeal_iff.mp hq) x hx)
  let T := (UniqueFactorizationMonoid.factors g).toFinset
  let S : MvPolynomial (Fin 1 × Fin n) ℂ → Set (Fin n → ℂ) :=
    fun p => {x | x ∈ V ∧ (x = 0 ∨ Associated (pairing x) p)}
  have hcover : ∏ p ∈ T, vanishingIdeal ℂ (S p) ≤ W := by
    intro q hq
    rw [hNS]
    intro x hx
    obtain ⟨p, hpT, hxp⟩ : ∃ p ∈ T, x ∈ S p := by
      by_cases hx0 : x = 0
      · obtain ⟨p, hp, -⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hg.1
          (irreducible_pairing hy₀0) (hdvd y₀ hy₀ hy₀0)
        exact ⟨p, Multiset.mem_toFinset.mpr hp, hx, Or.inl hx0⟩
      · obtain ⟨p, hp, hxp⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hg.1
          (irreducible_pairing hx0) (hdvd x hx hx0)
        exact ⟨p, Multiset.mem_toFinset.mpr hp, hx, Or.inr hxp⟩
    have hq' : q ∈ vanishingIdeal ℂ (S p) := (Ideal.prod_le_inf.trans (Finset.inf_le hpT)) hq
    simpa using (mem_vanishingIdeal_iff.mp hq') x hxp
  obtain ⟨p, -, hpW⟩ := (Ideal.IsPrime.prod_le hW.isPrime).mp hcover
  obtain ⟨y, ⟨hyV, hyp⟩, hy0⟩ := hrel (S p) hpW
  have hyp' : Associated (pairing y) p := hyp.resolve_left hy0
  have hline : ∀ q, q ∈ W ↔ ∀ t : ℂ, eval (t • y) q = 0 := by
    intro q
    refine ⟨fun hq t => hcone y hyV t q hq, fun hq => hpW ?_⟩
    rw [mem_vanishingIdeal_iff]
    rintro x ⟨-, hx⟩
    rcases hx with rfl | hx
    · simpa using hq 0
    · obtain ⟨t, rfl⟩ := eq_smul_of_associated (hyp'.trans hx.symm)
      simpa using hq t
  refine ⟨y, hy0, fun x => ⟨fun hx => ?_, ?_⟩, hline⟩
  · obtain ⟨a, ha⟩ := exists_ne_zero hy0
    refine ⟨x a / y a, funext fun b => ?_⟩
    have hmem : C (y a) * X b - C (y b) * X a ∈ W := (hline _).mpr fun t => by
      simp only [map_sub, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
      ring
    have h := hx _ hmem
    simp only [map_sub, map_mul, eval_C, eval_X] at h
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h
  · rintro ⟨t, rfl⟩
    exact hcone y hyV t

end

end GroundTheory.Heights₂.Heights
