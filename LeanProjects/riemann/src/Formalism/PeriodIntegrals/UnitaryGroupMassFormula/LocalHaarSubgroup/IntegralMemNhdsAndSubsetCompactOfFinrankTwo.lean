import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.ExistsHaarOfSubgroup

noncomputable section

open ValuativeRel Topology Polynomial

namespace PI.LocHaarRRW

section None

variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

theorem key_bound [Nontrivial V] [Module.Finite K V] {θ : V} {d : K}
    (hθr : θ ∉ (algebraMap K V).range) (hθ : θ * θ = algebraMap K V d) (hdO : d ∈ 𝒪[K])
    {a b : K} (hx : IsIntegral 𝒪[K] (algebraMap K V a + algebraMap K V b * θ)) :
    2 * a ∈ 𝒪[K] ∧ 2 * b * d ∈ 𝒪[K] := by
  obtain ⟨hxi, hx'⟩ : IsIntegral 𝒪[K] (algebraMap K V a + algebraMap K V b * θ) ∧
      IsIntegral 𝒪[K] (algebraMap K V a - algebraMap K V b * θ) := by
    refine ⟨hx, ?_⟩
    by_cases hb : b = 0
    · subst hb
      simpa using hx
    · obtain ⟨p, hpm, hp⟩ := hx
      have hqm : ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]).Monic := by monicity!
      have hqd : ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]).natDegree = 2 := by compute_degree!
      have hQx : ∀ y : V, (y - algebraMap K V a) ^ 2 = algebraMap K V (b ^ 2 * d) →
          aeval y ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]) = 0 := by
        intro y hy
        simp only [map_sub, map_pow, aeval_X, aeval_C, hy, sub_self]
      generalize ((X - C a) ^ 2 - C (b ^ 2 * d) : K[X]) = Q at hqm hqd hQx
      have e : ∀ y : V, aeval y (p.map (algebraMap 𝒪[K] K)) = eval₂ (algebraMap 𝒪[K] V) y p :=
        fun y => by rw [aeval_map_algebraMap, aeval_def]
      generalize p.map (algebraMap 𝒪[K] K) = P at e
      have key : ∀ y : V, aeval y Q = 0 → aeval y P = aeval y (P %ₘ Q) := by
        intro y hy
        conv_lhs => rw [← modByMonic_add_div P Q]
        simp [hy]
      have hQ1 : Q ≠ 1 := by
        rintro rfl
        simp at hqd
      have hrd : (P %ₘ Q).natDegree ≤ 1 := by
        have := natDegree_modByMonic_lt P hqm hQ1
        omega
      generalize P %ₘ Q = r at key hrd
      have hr := eq_X_add_C_of_natDegree_le_one hrd
      have hx1 : (algebraMap K V a + algebraMap K V b * θ - algebraMap K V a) ^ 2 =
          algebraMap K V (b ^ 2 * d) := by
        rw [map_mul, map_pow, ← hθ]; ring
      have hx2 : (algebraMap K V a - algebraMap K V b * θ - algebraMap K V a) ^ 2 =
          algebraMap K V (b ^ 2 * d) := by
        rw [map_mul, map_pow, ← hθ]; ring
      have hrx : aeval (algebraMap K V a + algebraMap K V b * θ) r = 0 := by
        rw [← key _ (hQx _ hx1), e]
        exact hp
      rw [hr] at hrx
      simp only [map_add, map_mul, aeval_X, aeval_C] at hrx
      have hw : r.coeff 1 = 0 := by
        by_contra hw
        apply hθr
        have hwb : r.coeff 1 * b ≠ 0 := mul_ne_zero hw hb
        have hinv : algebraMap K V (r.coeff 1 * b)⁻¹ *
            (algebraMap K V (r.coeff 1) * algebraMap K V b) = 1 := by
          rw [← map_mul, ← map_mul, inv_mul_cancel₀ hwb, map_one]
        refine ⟨-(r.coeff 1 * a + r.coeff 0) * (r.coeff 1 * b)⁻¹, ?_⟩
        rw [map_mul, map_neg, map_add, map_mul]
        linear_combination (-(algebraMap K V (r.coeff 1 * b)⁻¹)) * hrx + θ * hinv
      have hu : r.coeff 0 = 0 := by
        rw [hw] at hrx
        apply (algebraMap K V).injective
        simpa using hrx
      refine ⟨p, hpm, ?_⟩
      rw [← e, key _ (hQx _ hx2), hr, hw, hu]
      simp
  have hθi : IsIntegral 𝒪[K] θ := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hθ]
    exact integral_V_of_memO hdO
  have hA : algebraMap K V (2 * a) = (algebraMap K V a + algebraMap K V b * θ) +
      (algebraMap K V a - algebraMap K V b * θ) := by
    rw [map_mul, map_ofNat]; ring
  have hB : algebraMap K V (2 * b * d) = (algebraMap K V a + algebraMap K V b * θ) * θ +
      (algebraMap K V a - algebraMap K V b * θ) * (-θ) := by
    rw [map_mul, map_mul, map_ofNat]
    linear_combination (-2 * algebraMap K V b) * hθ
  refine ⟨memO_of_integral_V (V := V) ?_, memO_of_integral_V (V := V) ?_⟩
  · rw [hA]; exact hxi.add hx'
  · rw [hB]; exact (hxi.mul hθi).add (hx'.mul hθi.neg)

theorem integral_mem_nhds_and_subset_compact_of_finrank_two [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V]
    [TopologicalSpace V] [IsModuleTopology K V]
    (O : Subring V) (hO : ∀ x, x ∈ O ↔ IsIntegral 𝒪[K] x) :
    ∃ _ : K × K ≃ₜ V, (O : Set V) ∈ 𝓝 (0 : V) ∧ ∃ C : Set V, IsCompact C ∧ (O : Set V) ⊆ C := by
  classical
  obtain ⟨θ, d, hθr, hθ, hd0, hdO⟩ := exists_sq (K := K) (V := V) hr
  haveI : Module.Finite K V := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hr]; norm_num)
  have hθi : IsIntegral 𝒪[K] θ := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [pow_two, hθ]
    exact integral_V_of_memO hdO
  let L : K × K →ₗ[K] V :=
    (LinearMap.fst K K K).smulRight (1 : V) + (LinearMap.snd K K K).smulRight θ
  have hL : ∀ p : K × K, L p = algebraMap K V p.1 + algebraMap K V p.2 * θ := by
    intro p
    simp [L, Algebra.smul_def]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    rw [hL] at hp
    have hb : p.2 = 0 := by
      by_contra hb
      apply hθr
      refine ⟨-p.1 * p.2⁻¹, ?_⟩
      have hinv : algebraMap K V p.2⁻¹ * algebraMap K V p.2 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hb, map_one]
      rw [map_mul, map_neg]
      linear_combination (-(algebraMap K V p.2⁻¹)) * hp + θ * hinv
    have ha : p.1 = 0 := by
      rw [hb] at hp
      apply (algebraMap K V).injective
      simpa using hp
    exact Prod.ext ha hb
  have hsurj : Function.Surjective L := by
    have : Module.finrank K (K × K) = Module.finrank K V := by
      rw [Module.finrank_prod, Module.finrank_self, hr]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).mp hinj
  obtain ⟨e, he⟩ : ∃ e : (K × K) ≃ₗ[K] V,
      ∀ p, e p = algebraMap K V p.1 + algebraMap K V p.2 * θ :=
    ⟨LinearEquiv.ofBijective L (show Function.Bijective L from ⟨hinj, hsurj⟩), fun p => hL p⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd (R := K) (A := V)
  haveI : ContinuousSMul K V := IsModuleTopology.toContinuousSMul (R := K) (A := V)
  obtain ⟨h, hh⟩ : ∃ h : K × K ≃ₜ V, ∀ p, h p = e p :=
    ⟨{ toEquiv := e.toEquiv
       continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
       continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
     fun _ => rfl⟩
  refine ⟨h, ?_, ?_⟩
  · have hsub : h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) ⊆ (O : Set V) := by
      rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
      show h p ∈ O
      rw [hO, hh, he]
      exact (integral_V_of_memO hp1).add ((integral_V_of_memO hp2).mul hθi)
    have hopen : IsOpen (h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K))) :=
      h.isOpenMap _ ((isOpen_integer' (K := K)).prod (isOpen_integer' (K := K)))
    have h0 : (0 : V) ∈ h '' ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K)) :=
      ⟨(0, 0), ⟨Subring.zero_mem _, Subring.zero_mem _⟩, by rw [hh]; exact map_zero e⟩
    exact Filter.mem_of_superset (hopen.mem_nhds h0) hsub
  · refine ⟨h '' ((fun q : K × K => (q.1 * 2⁻¹, q.2 * (2 * d)⁻¹)) ''
      ((𝒪[K] : Set K) ×ˢ (𝒪[K] : Set K))), ?_, ?_⟩
    · exact (((isCompact_integer (K := K)).prod (isCompact_integer (K := K))).image
        (by fun_prop)).image h.continuous
    · intro x hx
      have hpx : h (h.symm x) = x := h.apply_symm_apply x
      have hint : IsIntegral 𝒪[K]
          (algebraMap K V (h.symm x).1 + algebraMap K V (h.symm x).2 * θ) := by
        rw [← he, ← hh, hpx]
        exact (hO x).mp hx
      obtain ⟨h1, h2⟩ := key_bound hθr hθ hdO hint
      refine ⟨h.symm x, ⟨(2 * (h.symm x).1, 2 * (h.symm x).2 * d), ⟨h1, h2⟩, ?_⟩, hpx⟩
      refine Prod.ext ?_ ?_ <;> dsimp only <;> first | (field_simp; done) | (field_simp; ring)

end None

end PI.LocHaarRRW
