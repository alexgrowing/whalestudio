import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelFiniteness.ExistsNatMulMemFracFam

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerDetFinW

open PI.KerIso

lemma det_mem_of_entries {K : Type} [Field K] (R : Subring K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (h : ∀ i j, A i j ∈ R) : A.det ∈ R := by
  have hB : R.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : R)) = A := by
    ext i j
    rfl
  rw [← hB, ← RingHom.map_det]
  exact SetLike.coe_mem _

lemma det_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (A : Matrix ι ι K) (u : ι → ℕ) (hu : ∀ j, Nat.Coprime (u j) p)
    (hA : ∀ i j, (u j : K) * A i j ∈ (algebraMap (𝓞 K) K).range) :
    ∃ U : ℕ, Nat.Coprime U p ∧ (U : K) * A.det ∈ (algebraMap (𝓞 K) K).range := by
  refine ⟨∏ j, u j, Nat.Coprime.prod_left (fun j _ => hu j), ?_⟩
  have h1 : ((∏ j, u j : ℕ) : K) * A.det = (A * Matrix.diagonal (fun j => (u j : K))).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    push_cast
    ring
  rw [h1]
  apply det_mem_of_entries
  intro i j
  rw [Matrix.mul_diagonal, mul_comm]
  exact hA i j

lemma valuation_natCast_eq_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) :
    𝔭.valuation K (U : K) = 1 := by
  have hU' : ((U : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hU
    apply 𝔭.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : ((a * (U : ℤ) + b * (p : ℤ) : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      push_cast
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hp𝔭)
    rw [hab, Int.cast_one] at h2
    exact h2
  have hK : ((U : ℕ) : K) = algebraMap (𝓞 K) K (U : 𝓞 K) := (map_natCast _ _).symm
  rw [hK, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  refine le_antisymm (𝔭.intValuation_le_one _) (not_lt.mp fun hlt => hU' ?_)
  exact Ideal.dvd_span_singleton.mp ((𝔭.intValuation_lt_one_iff_dvd _).mp hlt)

lemma valuation_le_one_of_denom {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {p U : ℕ}
    (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hU : Nat.Coprime U p) {x : K}
    (hx : (U : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by
  obtain ⟨r, hr⟩ := hx
  have h1 : 𝔭.valuation K (U : K) = 1 := valuation_natCast_eq_one 𝔭 hp𝔭 hU
  have h2 : 𝔭.valuation K ((U : K) * x) ≤ 1 := by
    rw [← hr, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact 𝔭.intValuation_le_one r
  rwa [map_mul, h1, one_mul] at h2

lemma comp_denom {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ u : ℕ, Nat.Coprime u p ∧ ∀ w, (u : K) * (g.symm.trans g') v w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨s, hs, hsM⟩ := hg.2 v hv
  have hx : ∀ a, ((s : K) • g.symm v) a ∈ M := by
    intro a
    rw [Pi.smul_apply, Algebra.smul_def, map_natCast]
    exact hsM a
  obtain ⟨t, ht, htM⟩ := hg'.1 ((s : K) • g.symm v) hx
  refine ⟨t * s, Nat.Coprime.mul ht hs, fun w => ?_⟩
  have h := htM w
  rw [map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc] at h
  rw [LinearEquiv.trans_apply, Nat.cast_mul]
  exact h

lemma det_valuation_le_one {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) :
    𝔭.valuation K (LinearMap.det ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
      (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))) ≤ 1 := by
  classical
  set f := ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
    (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) with hf
  have hcol : ∀ j : Fin 4 × n, ∃ u : ℕ, Nat.Coprime u p ∧
      ∀ i, (u : K) * LinearMap.toMatrix' f i j ∈ (algebraMap (𝓞 K) K).range := by
    intro j
    have hv : ∀ w, (Pi.single j (1 : K) : Fin 4 × n → K) w ∈ (algebraMap (𝓞 K) K).range := by
      intro w
      by_cases hw : w = j
      · subst hw
        rw [Pi.single_eq_same]
        exact one_mem _
      · rw [Pi.single_eq_of_ne hw]
        exact zero_mem _
    obtain ⟨u, hu, hu'⟩ := comp_denom hg hg' (Pi.single j (1 : K)) hv
    exact ⟨u, hu, fun i => by rw [LinearMap.toMatrix'_apply]; exact hu' i⟩
  choose u hu hu' using hcol
  obtain ⟨U, hU, hUd⟩ := det_denom p (LinearMap.toMatrix' f) u hu (fun i j => hu' j i)
  rw [LinearMap.det_toMatrix'] at hUd
  exact valuation_le_one_of_denom 𝔭 hp𝔭 hU hUd

theorem ordK_detRel_eq_zero {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) : ordK 𝔭 (detRel g' g) = 0 := by
  have h1 : 𝔭.valuation K (detRel g' g) ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg hg'
  have h2 : 𝔭.valuation K (detRel g g') ≤ 1 := det_valuation_le_one 𝔭 hp𝔭 hg' hg
  have hprod : detRel g' g * detRel g g' = 1 := by
    unfold detRel
    rw [← LinearMap.det_comp]
    have hc : ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)).comp
        ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) :
        (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) = LinearMap.id :=
      LinearMap.ext fun x => by simp
    rw [hc, LinearMap.det_id]
  have hm : 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') = 1 := by
    rw [← map_mul, hprod, map_one]
  have hv : 𝔭.valuation K (detRel g' g) = 1 := by
    refine le_antisymm h1 ?_
    calc 1 = 𝔭.valuation K (detRel g' g) * 𝔭.valuation K (detRel g g') := hm.symm
      _ ≤ 𝔭.valuation K (detRel g' g) * 1 := by gcongr
      _ = 𝔭.valuation K (detRel g' g) := mul_one _
  unfold ordK
  rw [hv]
  simp

end PI.KerDetFinW
