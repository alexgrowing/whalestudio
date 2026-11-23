import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.Conj

open UniformSpace Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem exists_padicAlgCl_factor {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ_[p]) :
    ∃ φ : K →+* PadicAlgCl p, ∀ a, ((φ a : PadicAlgCl p) : ℂ_[p]) = κ a := by
  let j : PadicAlgCl p →+* ℂ_[p] := UniformSpace.Completion.coeRingHom
  have hjinj : Function.Injective j := j.injective
  let _ : Algebra (PadicAlgCl p) ℂ_[p] := j.toAlgebra
  have hmem : ∀ a : K, ∃ y, j y = κ a := by
    intro a
    have ha : IsIntegral ℚ a := IsIntegral.of_finite ℚ a
    have hκ : aeval (κ a) (minpoly ℚ a) = κ (aeval a (minpoly ℚ a)) :=
      Polynomial.aeval_algHom_apply κ.toRatAlgHom a _
    have hint : IsIntegral (PadicAlgCl p) (κ a) := by
      refine ⟨(minpoly ℚ a).map (algebraMap ℚ (PadicAlgCl p)), (minpoly.monic ha).map _, ?_⟩
      rw [eval₂_map]
      have hc : (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap ℚ (PadicAlgCl p)) =
          algebraMap ℚ ℂ_[p] := RingHom.ext_rat _ _
      rw [hc, ← aeval_def, hκ, minpoly.aeval, map_zero]
    exact RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (PadicAlgCl p) (κ a)
      (IsAlgClosed.degree_eq_one_of_irreducible (PadicAlgCl p) (minpoly.irreducible hint)))
  choose f hf using hmem
  refine ⟨{ toFun := f
            map_one' := hjinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hjinj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hjinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hjinj (by rw [hf, map_add, map_add, hf, hf]) }, fun a => hf a⟩

theorem norm_aeval_monomial_sub (x : PadicAlgCl p) (n : ℕ) (r : ℚ) (c : ℚ_[p]) :
    ‖aeval x (monomial n r) - aeval x (monomial n c)‖ = ‖(r : ℚ_[p]) - c‖ * ‖x‖ ^ n := by
  rw [aeval_monomial, aeval_monomial, ← sub_mul, norm_mul, norm_pow,
    eq_ratCast (algebraMap ℚ (PadicAlgCl p)) r,
    ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) r, ← map_sub, PadicAlgCl.norm_extends]

theorem exists_rat_poly_approx (x y : PadicAlgCl p) (e : ℚ_[p][X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℚ[X], ‖aeval x u - aeval x e‖ < ε ∧ ‖aeval y u - aeval y e‖ < ε := by
  obtain ⟨N, hN⟩ : ∃ N, e.natDegree < N := ⟨_, Nat.lt_succ_self _⟩
  have hSx : 0 ≤ ∑ i ∈ Finset.range N, ‖x‖ ^ i := Finset.sum_nonneg fun i _ => by positivity
  have hSy : 0 ≤ ∑ i ∈ Finset.range N, ‖y‖ ^ i := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδx, hδy⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ∑ i ∈ Finset.range N, ‖x‖ ^ i < ε ∧
      δ * ∑ i ∈ Finset.range N, ‖y‖ ^ i < ε := by
    have hD : 0 < ∑ i ∈ Finset.range N, ‖x‖ ^ i + ∑ i ∈ Finset.range N, ‖y‖ ^ i + 1 := by linarith
    refine ⟨ε / (∑ i ∈ Finset.range N, ‖x‖ ^ i + ∑ i ∈ Finset.range N, ‖y‖ ^ i + 1),
      div_pos hε hD, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      nlinarith [mul_nonneg hε.le hSy]
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      nlinarith [mul_nonneg hε.le hSx]
  have hr' : ∀ i, ∃ r : ℚ, ‖e.coeff i - (r : ℚ_[p])‖ < δ := fun i => Padic.rat_dense p (e.coeff i) hδ0
  choose r hr using hr'
  have key : ∀ z : PadicAlgCl p, ‖aeval z (∑ i ∈ Finset.range N, monomial i (r i)) - aeval z e‖ ≤
      δ * ∑ i ∈ Finset.range N, ‖z‖ ^ i := by
    intro z
    conv_lhs => rw [e.as_sum_range' N hN]
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_aeval_monomial_sub, norm_sub_rev]
    exact mul_le_mul_of_nonneg_right (hr i).le (by positivity)
  exact ⟨_, (key x).trans_lt hδx, (key y).trans_lt hδy⟩

theorem norm_natCast_prime : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem minpoly_eq_of_unit_ball {K : Type} [Field K] [NumberField K] (φ ψ : K →+* PadicAlgCl p)
    (h : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1) (θ : K) :
    minpoly ℚ_[p] (φ θ) = minpoly ℚ_[p] (ψ θ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnorm : ∀ (χ : K →+* PadicAlgCl p) (j : ℕ), ‖χ ((p : K) ^ j)⁻¹‖ = ((p : ℝ)⁻¹ ^ j)⁻¹ := by
    intro χ j
    rw [map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, norm_natCast_prime]
  have core : ∀ φ₁ ψ₁ : K →+* PadicAlgCl p, (∀ a, ‖φ₁ a‖ ≤ 1 → ‖ψ₁ a‖ ≤ 1) →
      aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) = 0 := by
    intro φ₁ ψ₁ h₁
    have hφ : ∀ v : ℚ[X], aeval (φ₁ θ) v = φ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply φ₁.toRatAlgHom θ v
    have hψ : ∀ v : ℚ[X], aeval (ψ₁ θ) v = ψ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply ψ₁.toRatAlgHom θ v
    by_contra hne
    have hz : 0 < ‖aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ))‖ := norm_pos_iff.mpr hne
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (half_pos hz) (inv_lt_one_of_one_lt₀ hp1)
    have ht : 0 < (p : ℝ)⁻¹ ^ j := pow_pos (inv_pos.mpr (by linarith)) j
    obtain ⟨u, hux, huy⟩ := exists_rat_poly_approx (φ₁ θ) (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) ht
    rw [minpoly.aeval, sub_zero, hφ] at hux
    have h1 : ‖φ₁ (((p : K) ^ j)⁻¹ * aeval θ u)‖ ≤ 1 := by
      rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one]
      exact hux.le
    have h2 := h₁ _ h1
    rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one, ← hψ] at h2
    have h4 := norm_sub_le (aeval (ψ₁ θ) u) (aeval (ψ₁ θ) u - aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)))
    rw [sub_sub_cancel] at h4
    linarith
  have hx : IsIntegral ℚ_[p] (φ θ) := Algebra.IsIntegral.isIntegral _
  have hy : IsIntegral ℚ_[p] (ψ θ) := Algebra.IsIntegral.isIntegral _
  have hPQ : minpoly ℚ_[p] (φ θ) ∣ minpoly ℚ_[p] (ψ θ) :=
    minpoly.dvd _ _ (core ψ φ fun a => (h a).mpr)
  refine minpoly.unique' ℚ_[p] (ψ θ) (minpoly.monic hx) (core φ ψ fun a => (h a).mp) fun q hq => ?_
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · refine Or.inr fun hqy => ?_
    have h3 := Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ hqy) hq0
    have h4 := Polynomial.natDegree_le_of_dvd hPQ (minpoly.ne_zero hy)
    have h5 := Polynomial.natDegree_lt_natDegree hq0 hq
    omega

theorem exists_extension (σ : PadicAlgCl p ≃+* PadicAlgCl p) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧
      ∀ x : PadicAlgCl p, g (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) := by
  have hσs : ∀ x, ‖σ.symm x‖ = ‖x‖ := fun x => by rw [← hσ, RingEquiv.apply_symm_apply]
  have hσi : Isometry σ := AddMonoidHomClass.isometry_of_norm σ hσ
  have hτi : Isometry σ.symm := AddMonoidHomClass.isometry_of_norm σ.symm hσs
  let F : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ : PadicAlgCl p →+* PadicAlgCl p) hσi.continuous
  let G : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ.symm : PadicAlgCl p →+* PadicAlgCl p) hτi.continuous
  have hF : ∀ x : PadicAlgCl p, F x = (σ x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hσi.continuous x
  have hG : ∀ x : PadicAlgCl p, G x = (σ.symm x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hτi.continuous x
  have hFc : Continuous F := UniformSpace.Completion.continuous_extension
  have hGc : Continuous G := UniformSpace.Completion.continuous_extension
  have hGF : ∀ z, G (F z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hGc.comp hFc) continuous_id) fun x => ?_
    rw [hF, hG, RingEquiv.symm_apply_apply]
  have hFG : ∀ z, F (G z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hFc.comp hGc) continuous_id) fun x => ?_
    rw [hG, hF, RingEquiv.apply_symm_apply]
  have hFn : ∀ z, ‖F z‖ = ‖z‖ := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (continuous_norm.comp hFc) continuous_norm) fun x => ?_
    rw [hF, PadicComplex.norm_extends, PadicComplex.norm_extends, hσ]
  refine ⟨{ toFun := fun z => F z
            invFun := fun z => G z
            left_inv := hGF
            right_inv := hFG
            map_mul' := map_mul F
            map_add' := map_add F }, hFn, hF⟩

theorem exists_isometry_conj_of_unit_ball (K : Type) [Field K] [NumberField K] (p : Nat.Primes)
    (κ κ' : K →+* ℂ_[p]) (h : ∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  obtain ⟨φ, hφ⟩ := exists_padicAlgCl_factor κ
  obtain ⟨ψ, hψ⟩ := exists_padicAlgCl_factor κ'
  have hb : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1 := fun a => by
    rw [← PadicComplex.norm_extends, ← PadicComplex.norm_extends, hφ, hψ]
    exact h a
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ K
  have hm := minpoly_eq_of_unit_ball φ ψ hb θ
  have : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal _ _
  obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).mp hm.symm)
  have hτ' : τ (φ θ) = ψ θ := by rw [← AlgEquiv.smul_def]; exact hτ
  have hτn : ∀ x, ‖τ.toRingEquiv x‖ = ‖x‖ := fun x => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    unfold spectralNorm
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_eq]
  obtain ⟨g, hgn, hg⟩ := exists_extension τ.toRingEquiv hτn
  have hv : ∀ v : ℚ[X], τ (φ (aeval θ v)) = ψ (aeval θ v) := by
    intro v
    have e1 : φ (aeval θ v) = aeval (φ θ) v := (Polynomial.aeval_algHom_apply φ.toRatAlgHom θ v).symm
    have e2 : ψ (aeval θ v) = aeval (ψ θ) v := (Polynomial.aeval_algHom_apply ψ.toRatAlgHom θ v).symm
    have e3 : τ (aeval (φ θ) v) = aeval (τ (φ θ)) v :=
      (Polynomial.aeval_algHom_apply (τ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).toRatAlgHom
        (φ θ) v).symm
    rw [e1, e2, e3, hτ']
  refine ⟨g, hgn, fun a => ?_⟩
  have ha : a ∈ IntermediateField.adjoin ℚ {θ} := by
    rw [hθ]
    exact IntermediateField.mem_top
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ a).mp ha
  have key : τ (φ a) = ψ a := by
    rw [hrs, map_div₀, map_div₀, map_div₀, hv, hv]
  rw [← hφ, ← hψ, hg]
  exact congrArg _ key

end GlobalTheory.CompanionTheory.Ar.Br.Conj
