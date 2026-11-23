import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsDedekindDomain

section
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)

noncomputable abbrev algOTKT : Algebra (OT K D N) (KTf K D N) :=
  ((algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N)).toAlgebra

noncomputable abbrev algOpKT (la : HeightOneSpectrum (𝓞 K)) : Algebra (Op D N la) (KTf K D N) :=
  (OpToKT D N la).toAlgebra

theorem isFractionRing_OT :
    letI := algOTKT (K := K) D N
    IsFractionRing (OT K D N) (KTf K D N) := by
  letI := algOTKT (K := K) D N
  have hinj : Function.Injective (algebraMap (OT K D N) (KTf K D N)) :=
    (IsFractionRing.injective (KTp K D N) (KTf K D N)).comp
      (MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K))
  haveI : FaithfulSMul (OT K D N) (KTf K D N) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (KTp K D N) z
  letI : Algebra (OT K D N) (KTp K D N) := MvPolynomial.algebraMvPolynomial
  haveI := MvPolynomial.isLocalization (σ := TVar D N) (nonZeroDivisors (𝓞 K)) K
  obtain ⟨⟨P, ⟨_, a, ha, rfl⟩⟩, hP⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) p
  obtain ⟨⟨Q, ⟨_, b, hb, rfl⟩⟩, hQ⟩ :=
    IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map (MvPolynomial.C (σ := TVar D N))) q
  refine ⟨P * MvPolynomial.C b, Q * MvPolynomial.C a, ?_⟩
  have e : ∀ X : OT K D N, algebraMap (OT K D N) (KTf K D N) X =
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) X) := fun X => rfl
  have hC : ∀ c ∈ nonZeroDivisors (𝓞 K),
      algebraMap (KTp K D N) (KTf K D N) (algebraMap (OT K D N) (KTp K D N) (MvPolynomial.C c)) ≠ 0 := by
    intro c hc
    rw [← e]
    exact (map_ne_zero_iff _ hinj).mpr (by
      rw [Ne, MvPolynomial.C_eq_zero]; exact nonZeroDivisors.ne_zero hc)
  have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (KTp K D N) (KTf K D N))).mpr
      (nonZeroDivisors.ne_zero hq)
  simp only at hP hQ
  rw [e, e, map_mul, map_mul, map_mul, map_mul, ← hP, ← hQ, map_mul, map_mul]
  have ha := hC a ha
  have hb := hC b hb
  field_simp

theorem isFractionRing_Op (la : HeightOneSpectrum (𝓞 K)) :
    letI := algOpKT (K := K) D N la
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := algOTKT (K := K) D N
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_OT (K := K) D N
  haveI : IsScalarTower (OT K D N) (Op D N la) (KTf K D N) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = OpToKT D N la (algebraMap _ _ x)
      rw [OpToKT, IsLocalization.lift_eq]
      rfl
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (laT D N la).primeCompl
    (Op D N la) (KTf K D N)

theorem OpToKT_injective (la : HeightOneSpectrum (𝓞 K)) : Function.Injective (OpToKT D N la) := by
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_Op (K := K) D N la
  exact IsFractionRing.injective (Op D N la) (KTf K D N)

omit [NumberField K] in
theorem unif_mem [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (Data.unif la : 𝓞 K) ∈ la.asIdeal ∧ (Data.unif la : 𝓞 K) ∉ la.asIdeal ^ 2 := by
  have hex : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 := by
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    refine ⟨π, ?_, ?_⟩
    · rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    · rw [← la.intValuation_le_pow_iff_mem, hπ, WithZero.exp_le_exp]
      norm_num
  rw [Data.unif, dif_pos hex]
  exact hex.choose_spec

noncomputable def unifOp (la : HeightOneSpectrum (𝓞 K)) : Op D N la :=
  algebraMap (OT K D N) (Op D N la) (MvPolynomial.C (Data.unif la))

theorem unifOp_irreducible (la : HeightOneSpectrum (𝓞 K)) : Irreducible (unifOp D N la) := by
  classical
  haveI := Op_isDVR (K := K) D N la
  obtain ⟨hmem, hnot⟩ := unif_mem la
  have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
    IsLocalization.injective (Op D N la) (laT D N la).primeCompl_le_nonZeroDivisors
  have hne : unifOp D N la ≠ 0 := by
    intro h
    have h0 : MvPolynomial.C (Data.unif la) = (0 : OT K D N) := hinj (h.trans (map_zero _).symm)
    rw [MvPolynomial.C_eq_zero] at h0
    exact hnot (h0 ▸ zero_mem _)
  have hmax : unifOp D N la ∈ IsLocalRing.maximalIdeal (Op D N la) := by
    rw [unifOp, IsLocalization.AtPrime.to_map_mem_maximal_iff (Op D N la) (laT D N la)]
    exact Ideal.mem_map_of_mem _ hmem
  have hnu : ¬ IsUnit (unifOp D N la) := (IsLocalRing.mem_maximalIdeal _).mp hmax
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Op D N la)
  obtain ⟨j, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  rcases j with _ | _ | j
  · exact absurd (by rw [hu, pow_zero, mul_one]; exact u.isUnit) hnu
  · rw [hu, pow_one]
    exact (irreducible_isUnit_mul u.isUnit).mpr hϖ
  · exfalso
    have h2 : unifOp D N la ∈ (IsLocalRing.maximalIdeal (Op D N la)) ^ 2 := by
      have hpow : (u : Op D N la) * ϖ ^ (j + 1 + 1) = (u * ϖ ^ j) * (ϖ * ϖ) := by ring
      rw [hu, hpow, pow_two]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hϖm hϖm)
    have hL2 : laT D N la ^ 2 = Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) (la.asIdeal ^ 2) := by
      unfold laT
      rw [Ideal.map_pow]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, hL2,
      IsLocalization.mem_map_algebraMap_iff (laT D N la).primeCompl (Op D N la)] at h2
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := h2
    simp only [unifOp, ← map_mul] at hx
    have hx' := hinj hx
    rw [← hx', MvPolynomial.mem_map_C_iff] at ha
    have hs' : s ∉ Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal := hs
    rw [MvPolynomial.mem_map_C_iff, not_forall] at hs'
    obtain ⟨mm, hmm⟩ := hs'
    have h3 := ha mm
    rw [MvPolynomial.coeff_C_mul] at h3
    have v1 : la.intValuation (Data.unif la) = la.intValuation (Data.unif la) * la.intValuation (MvPolynomial.coeff mm s) := by
      have : la.intValuation (MvPolynomial.coeff mm s) = 1 := by
        apply le_antisymm (la.intValuation_le_one _)
        rw [← not_lt, la.intValuation_lt_one_iff_mem]
        exact hmm
      rw [this, mul_one]
    have h4 : la.intValuation (Data.unif la) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
      rw [v1, ← map_mul]
      exact (la.intValuation_le_pow_iff_mem _ 2).mpr h3
    exact hnot ((la.intValuation_le_pow_iff_mem _ 2).mp h4)

theorem algK_unif (la : HeightOneSpectrum (𝓞 K)) :
    algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) = OpToKT D N la (unifOp D N la) := by
  rw [unifOp, OpToKT, IsLocalization.lift_eq, RingHom.comp_apply, OTtoKT, MvPolynomial.map_C,
    IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]

theorem exp_unique (la : HeightOneSpectrum (𝓞 K)) {m m' : ℤ} {u u' : Op D N la} (hu : IsUnit u)
    (hu' : IsUnit u')
    (h : (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u') : m = m' := by
  have key : ∀ {m m' : ℤ} {u u' : Op D N la}, IsUnit u → IsUnit u' →
      (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m * OpToKT D N la u =
        (algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K)) ^ m' * OpToKT D N la u' → m ≤ m' := by
    intro m m' u u' hu hu' h
    by_contra hlt
    push_neg at hlt
    have hϖ0 : algebraMap K (KTf K D N) ((Data.unif la : 𝓞 K) : K) ≠ 0 := by
      rw [algK_unif]
      exact (map_ne_zero_iff _ (OpToKT_injective D N la)).mpr (unifOp_irreducible D N la).ne_zero
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = m' + (k + 1 : ℕ) := ⟨(m - m' - 1).toNat, by omega⟩
    rw [hk, zpow_add₀ hϖ0, mul_assoc] at h
    have h' := mul_left_cancel₀ (zpow_ne_zero m' hϖ0) h
    rw [zpow_natCast, algK_unif, ← map_pow, ← map_mul] at h'
    have h'' := OpToKT_injective D N la h'
    have hunit : IsUnit (unifOp D N la ^ (k + 1) * u) := h'' ▸ hu'
    have := isUnit_of_mul_isUnit_left hunit
    exact (unifOp_irreducible D N la).not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp this)
  exact le_antisymm (key hu hu' h) (key hu' hu h.symm)

end

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem gOrd_eq (d : Data K ι Ω WT A) (la : HeightOneSpectrum (𝓞 K)) {q : KTf K d.D d.N} {m : ℤ}
    {u : Op d.D d.N la} (hu : IsUnit u)
    (hq : q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u) :
    d.gOrd la q = m := by
  classical
  have hex : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u :=
    ⟨m, u, hu, hq⟩
  rw [gOrd, dif_pos hex]
  obtain ⟨u', hu', hq'⟩ := hex.choose_spec
  exact exp_unique d.D d.N la hu' hu (hq'.symm.trans hq)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
