import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.EmbedReadsValuation

section Dvr

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem vV_unit_mul_pow {ϖ : V} (hϖ : Irreducible ϖ) (u : Vˣ) (k : ℕ) :
    vV V (algebraMap V (FractionRing V) (u * ϖ ^ k)) = k := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).intValuation ϖ = WithZero.exp (-1 : ℤ) :=
    HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  have h2 : (IsDiscreteValuationRing.maximalIdeal V).intValuation (u : V) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  unfold vV valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2, one_mul, ← WithZero.exp_nsmul,
    WithZero.log_exp]
  simp

variable {C : Type} [NormedField C] (eF : FractionRing V →+* C)

theorem norm_unit (h1 : ∀ a : V, ‖eF (algebraMap V _ a)‖ ≤ 1) (u : Vˣ) :
    ‖eF (algebraMap V _ (u : V))‖ = 1 := by
  have h : ‖eF (algebraMap V _ (u : V))‖ * ‖eF (algebraMap V _ ((u⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul]; simp
  have a := h1 u
  have b := h1 ((u⁻¹ : Vˣ) : V)
  nlinarith [norm_nonneg (eF (algebraMap V _ (u : V))), norm_nonneg (eF (algebraMap V _ ((u⁻¹ : Vˣ) : V)))]

theorem norm_eq_zpow (h1 : ∀ a : V, ‖eF (algebraMap V _ a)‖ ≤ 1) {ϖ : V} (hϖ : Irreducible ϖ)
    (z : FractionRing V) (hz : z ≠ 0) :
    ‖eF z‖ = ‖eF (algebraMap V _ ϖ)‖ ^ (vV V z) := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  have hc0 : ‖eF (algebraMap V _ ϖ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff, map_ne_zero, Ne, ← map_zero (algebraMap V (FractionRing V)), hinj.eq_iff]
    exact hϖ.ne_zero
  have key : ∀ a : V, a ≠ 0 → ‖eF (algebraMap V _ a)‖ = ‖eF (algebraMap V _ ϖ)‖ ^ (vV V (algebraMap V (FractionRing V) a)) := by
    intro a ha
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    rw [vV_unit_mul_pow hϖ, map_mul, map_mul, norm_mul, norm_unit eF h1, one_mul, map_pow, map_pow, norm_pow,
      zpow_natCast]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap V (FractionRing V) b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V)), hinj.eq_iff]; exact hb0
  have ha' : algebraMap V (FractionRing V) a ≠ 0 := by
    intro h; apply hz; rw [h, zero_div]
  have ha0 : a ≠ 0 := by intro h; apply ha'; rw [h, map_zero]
  have hv : vV V (algebraMap V (FractionRing V) a / algebraMap V (FractionRing V) b) =
      vV V (algebraMap V (FractionRing V) a) - vV V (algebraMap V (FractionRing V) b) := by
    have := vV_mul (V := V) hz hb'
    rw [div_mul_cancel₀ _ hb'] at this
    omega
  rw [hv, zpow_sub₀ hc0, ← key a ha0, ← key b hb0, map_div₀, norm_div]

end Dvr

theorem norm_l (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
  exact h

theorem norm_natCast_of_coprime (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : Nat.Coprime n l) : ‖(n : ℂ_[l])‖ = 1 := by
  have h := PadicComplex.norm_extends' l (n : ℚ_[l])
  rw [(Padic.norm_natCast_eq_one_iff).2 hn.symm, map_natCast, PadicComplex.coe_natCast] at h
  exact h

theorem mem_int_iff {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem exists_embedding_norm_eq :
    ∀ {K : Type} [Field K] [NumberField K] (pl : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime],
      (p : 𝓞 K) ∈ pl.asIdeal → ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa pl T.V io e → T.FinRes →
      ∃ jm : T.Fr →+* ℂ_[p], ∀ z : T.Fr, z ≠ 0 →
        ‖jm z‖ = (p : ℝ) ^ (-((vV T.V z : ℝ) / (vV T.V (io (p : K)) : ℝ))) := by
  intro K _ _ pl p _ hpl T io e ho hT
  obtain ⟨q, hq, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
  have h1 : ∀ a : T.V, ‖k (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
    rw [← hk]
    exact (mem_int_iff _).1 (kO a).2
  have hp : p.Prime := Fact.out
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hn := norm_eq_zpow k h1 hϖ
  set c := ‖k (algebraMap T.V T.Fr ϖ)‖ with hcdef
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hc0 : 0 < c := by
    rw [hcdef, norm_pos_iff, map_ne_zero, Ne, ← map_zero (algebraMap T.V T.Fr), hinj.eq_iff]
    exact hϖ.ne_zero
  have hnat : ∀ n : ℕ, n ≠ 0 → (n : T.Fr) ≠ 0 := fun n hn0 => by
    rw [← map_natCast (algebraMap T.V T.Fr), Ne, ← map_zero (algebraMap T.V T.Fr), hinj.eq_iff]
    exact_mod_cast hn0
  have hc1 : c ≠ 1 := by
    intro h
    have h3 := hn (q : T.Fr) (hnat q hq.out.ne_zero)
    rw [h, one_zpow, map_natCast, norm_l] at h3
    have : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    have h4 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  have hio : io (p : K) = (p : T.Fr) := map_natCast io p
  have hN0 : vV T.V (io (p : K)) ≠ 0 := by
    rw [ho.2, mul_ne_zero_iff]
    refine ⟨by exact_mod_cast ho.1.ne', ?_⟩
    intro h2
    have e1 : ((p : ℕ) : K) = algebraMap (𝓞 K) K (p : 𝓞 K) := by simp
    have h0 : pl.intValuation ((p : ℕ) : 𝓞 K) ≠ 0 := pl.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
    rw [vLa, e1, HeightOneSpectrum.valuation_of_algebraMap, neg_eq_zero, ← WithZero.exp_inj, WithZero.exp_log h0,
      WithZero.exp_zero, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h2
    exact h2 hpl
  have hpc : ‖(p : ℂ_[q])‖ = c ^ vV T.V (io (p : K)) := by
    rw [← hn _ (by rw [hio]; exact hnat p hp.ne_zero), hio, map_natCast]
  have hqp : p = q := by
    by_contra hne
    have h3 : ‖(p : ℂ_[q])‖ = 1 := norm_natCast_of_coprime q ((Nat.coprime_primes hp hq.out).2 hne)
    rw [h3] at hpc
    have h4 := congrArg Real.log hpc
    rw [Real.log_one, Real.log_zpow] at h4
    have hl : Real.log c ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hc0 hc1
    rcases mul_eq_zero.1 h4.symm with h5 | h5
    · exact hN0 (by exact_mod_cast h5)
    · exact hl h5
  subst hqp
  refine ⟨k, fun z hz => ?_⟩
  have hpn : c ^ vV T.V (io (p : K)) = (p : ℝ)⁻¹ := by rw [← hpc, norm_l]
  have hN' : (vV T.V (io (p : K)) : ℝ) ≠ 0 := by exact_mod_cast hN0
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  calc ‖k z‖ = c ^ vV T.V z := hn z hz
    _ = c ^ (vV T.V z : ℝ) := (Real.rpow_intCast _ _).symm
    _ = c ^ ((vV T.V (io (p : K)) : ℝ) * ((vV T.V z : ℝ) / (vV T.V (io (p : K)) : ℝ))) := by
      congr 1; field_simp
    _ = (c ^ vV T.V (io (p : K))) ^ ((vV T.V z : ℝ) / (vV T.V (io (p : K)) : ℝ)) := by
      rw [Real.rpow_mul hc0.le, Real.rpow_intCast]
    _ = (p : ℝ) ^ (-((vV T.V z : ℝ) / (vV T.V (io (p : K)) : ℝ))) := by
      rw [hpn, Real.inv_rpow hp0, Real.rpow_neg hp0]

end GlobalTheory.EmbedReadsValuation
