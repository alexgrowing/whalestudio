import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitCoeffGaloisLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg GlobalTheory.QFam Cardinal

namespace GlobalTheory.KZ.GalUnits

theorem exists_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  let : Algebra R K := f.toAlgebra
  let : Algebra R L := g.toAlgebra
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' R L
  have h1 : #K = #ι := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' v hv hR hK
  have h2 : #L = #κ :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' w hw hR (hKL ▸ hK)
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis w hw
  let e' : Algebra.adjoin R (Set.range v) ≃ₐ[R] Algebra.adjoin R (Set.range w) :=
    (hv.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R e)).trans hw.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  have hf : f r = algebraMap R K r := rfl
  have hg : g r = algebraMap R L r := rfl
  rw [hf, hg, IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range v)) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  have : e'.toRingEquiv (algebraMap R _ r) = algebraMap R _ r := e'.commutes r
  rw [this, ← IsScalarTower.algebraMap_apply]

theorem exists_ext {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x : Ω, σ (ε x) = ε (s x) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hR : #Ω ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Ω).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  exact exists_equiv_comp ε (ε.comp (s : Ω →+* Ω)) hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl

theorem mem_range_of_pow_eq_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ε : Ω →+* ℂ) {n : ℕ}
    (hn : 0 < n) {w : ℂ} (hw : w ^ n = 1) : ∃ y, ε y = w := by
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos n Ω hn))
  have hz' : IsPrimitiveRoot z n := Polynomial.isRoot_cyclotomic_iff.1 hz
  have he : IsPrimitiveRoot (ε z) n := hz'.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := he.eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow, hi]⟩

theorem eps_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = ee (x : ℂ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = x.num * (2 * Real.pi * Complex.I) := by
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      have : (x : ℂ) = (x.num : ℂ) / x.den := by exact_mod_cast (Rat.num_div_den x).symm
      rw [this]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hex := mem_range_of_pow_eq_one ε x.den_pos hw
  unfold eOm ee
  exact Function.invFun_eq hex

open Classical in

def lc {R : Type} [Zero R] (M : ℕ) (k : ℤ) (A : ℕ → R) (r : ℚ) : R :=
  if h : ∃ n : ℕ, r = ((k : ℚ) + n) / M then A h.choose else 0

theorem lc_eq {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) (k : ℤ) (A : ℕ → R) (n : ℕ) :
    lc M k A (((k : ℚ) + n) / M) = A n := by
  have h : ∃ m : ℕ, ((k : ℚ) + n) / M = ((k : ℚ) + m) / M := ⟨n, rfl⟩
  unfold lc
  rw [dif_pos h]
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have := h.choose_spec
  rw [div_left_inj' hM', add_right_inj] at this
  have : h.choose = n := by exact_mod_cast this.symm
  rw [this]

theorem lc_zero {R : Type} [Zero R] {M : ℕ} {k : ℤ} (A : ℕ → R) {r : ℚ} (h : ∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) :
    lc M k A r = 0 := by
  unfold lc
  rw [dif_neg]
  push_neg
  exact h

theorem lc_map {R S : Type} [Zero R] [Zero S] (M : ℕ) (k : ℤ) (A : ℕ → R) (g : R → S) (hg : g 0 = 0) (r : ℚ) :
    lc M k (fun n => g (A n)) r = g (lc M k A r) := by
  unfold lc
  split_ifs <;> simp [hg]

theorem eq_lc {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) {k : ℤ} {A : ℕ → R} {F : ℚ → R}
    (h1 : ∀ n : ℕ, F (((k : ℚ) + n) / M) = A n) (h2 : ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → F r = 0) :
    ∀ r, F r = lc M k A r := by
  intro r
  by_cases h : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := h
    rw [h1, lc_eq hM]
  · push_neg at h
    rw [h2 r h, lc_zero A h]

theorem lc_unique {M : ℕ} (hM : 0 < M) {f : ℍ → ℂ} {k k' : ℤ} {A A' : ℕ → ℂ}
    (h : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A)
    (h' : HasQ M (fun τ => f τ * ee (-((k' : ℂ) / M) * (τ : ℂ))) A') : lc M k A = lc M k' A' := by
  wlog hk : k ≤ k' generalizing k k' A A'
  · exact (this h' h (le_of_not_ge hk)).symm
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k' = k + m := ⟨(k' - k).toNat, by omega⟩
  have hs : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => if m ≤ n then A' (n - m) else 0) := by
    rw [hasQ_iff] at h' ⊢
    intro τ
    set Q := Complex.exp (2 * Real.pi * Complex.I * τ / M) with hQ
    have h2 := (h' τ).mul_right (Q ^ m)
    have e : f τ * ee (-(((k + m : ℤ) : ℂ) / M) * (τ : ℂ)) * Q ^ m = f τ * ee (-((k : ℂ) / M) * (τ : ℂ)) := by
      rw [mul_assoc]; congr 1
      unfold ee
      rw [hQ, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [e] at h2
    refine (Function.Injective.hasSum_iff (f := fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n)
      (add_left_injective m) ?_).mp ?_
    · intro x hx
      have : ¬ m ≤ x := by
        intro hmx; exact hx ⟨x - m, by simp only; omega⟩
      simp [this]
    · rw [← hQ] at h2
      have e2 : (fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n) ∘ (· + m) = fun i => A' i * Q ^ i * Q ^ m := by
        funext n
        simp only [Function.comp, le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, pow_add]
        ring
      rw [e2]; exact h2
  have hA := HasQ.coeff_unique hM h hs
  subst hA
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  funext r
  by_cases hr : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := hr
    rw [lc_eq hM]
    by_cases hmn : m ≤ n
    · rw [if_pos hmn]
      have : ((k : ℚ) + n) / M = (((k + m : ℤ) : ℚ) + ((n - m : ℕ) : ℚ)) / M := by
        push_cast [Nat.cast_sub hmn]; ring
      rw [this, lc_eq hM]
    · rw [if_neg hmn, lc_zero]
      intro n' hn'
      rw [div_left_inj' hM'] at hn'
      push_cast at hn'
      have : (n : ℚ) = m + n' := by linarith
      have : n = m + n' := by exact_mod_cast this
      omega
  · push_neg at hr
    rw [lc_zero _ hr, lc_zero]
    intro n' hn'
    apply hr (m + n')
    rw [hn']; push_cast; ring

end GlobalTheory.KZ.GalUnits

namespace GlobalTheory.KZ

open GalUnits

theorem gal_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  intro Ω _ _ _ ε T c M a b d s hM ha hs h1 h2
  obtain ⟨σ, hσ⟩ := exists_ext ε s
  have hσM : σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) := by
    have e1 := eps_eOm ε (1 / M)
    have e2 := eps_eOm ε (d / M)
    push_cast at e1 e2
    rw [← e1, hσ, hs, e2]
  obtain ⟨k0, B, hB, hB'⟩ := GlobalTheory.T.smoothedSiegelUnit_coeff_galois_level c M a b d σ hM ha hσM h1 h2
  obtain ⟨k1, A1, hA1, c1, z1⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a b hM ha h1
  obtain ⟨k2, A2, hA2, c2, z2⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a (d * b) hM ha h2
  have L1 := eq_lc hM c1 z1
  have L2 := eq_lc hM c2 z2
  have U1 := lc_unique hM hA1 hB
  have U2 := lc_unique hM hB' hA2
  apply T.exp.toRingHom.injective
  ext r
  apply ε.injective
  show ε ((T.exp (T.gal s _)).coeff r) = ε ((T.exp _).coeff r)
  rw [T.gal_exp, ← hσ, L1, L2, ← lc_map M k1 A1 ε (map_zero ε), U1, ← lc_map M k0 B σ (map_zero σ), U2,
    lc_map M k2 A2 ε (map_zero ε)]

end GlobalTheory.KZ
