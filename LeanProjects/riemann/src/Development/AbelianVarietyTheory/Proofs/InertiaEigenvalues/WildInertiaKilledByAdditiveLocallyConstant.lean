import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.WildAdditive

theorem not_isUnit_natCast (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Nontrivial O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : ¬ IsUnit (l : O) := by
  rintro ⟨u, hu⟩
  have htop : (⊤ : Submodule ℤ_[l] O) ≤ IsLocalRing.maximalIdeal ℤ_[l] • ⊤ := by
    intro x _
    have hx : x = (l : ℤ_[l]) • (((u⁻¹ : Oˣ) : O) * x) := by
      rw [Algebra.smul_def, map_natCast, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hx]
    have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span rfl
    exact Submodule.smul_mem_smul hl Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) ⊤
    (Module.finite_def.mp inferInstance) htop (IsLocalRing.maximalIdeal_le_jacobson _)
  exact top_ne_bot hbot

theorem exists_pow_nsmul_eq_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (x : KOG O 1) :
    ∃ n : ℕ, l ^ n • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := O) (y 0)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O

  have hl : (l : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_natCast l O)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton] at hl

  obtain ⟨k, hk⟩ :=
    IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  obtain ⟨c, hc⟩ := hk.dvd.trans (pow_dvd_pow_of_dvd hl k)
  refine ⟨k, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  unfold stdG
  rw [LinearMap.mem_range]
  refine ⟨fun _ => c * a, ?_⟩
  funext j
  have hj : j = 0 := Subsingleton.elim j 0
  subst hj
  have hb' : algebraMap O (FractionRing O) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hlk : ((l ^ k : ℕ) : FractionRing O) =
      algebraMap O (FractionRing O) b * algebraMap O (FractionRing O) c := by
    rw [← map_mul, ← hc, map_pow, map_natCast, Nat.cast_pow]
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, Pi.smul_apply,
    nsmul_eq_mul, ← hab]
  rw [hlk, map_mul]
  field_simp

theorem eq_zero_of_wild (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (l : ℕ)
    (hl : l.Prime) (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (hA : IsPlaceOver A v)
    (M : Type) [AddCommGroup M] (f : G E Ω → M) (hf : IsLocallyConstant f)
    (I : Subgroup (G E Ω)) (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b)
    (hM : ∀ x : M, ∃ n : ℕ, l ^ n • x = 0) (σ : G E Ω) (hI : σ ∈ I)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : f σ = 0 := by
  classical
  have hI1 : (1 : G E Ω) ∈ I := I.one_mem
  have hf1 : f 1 = 0 := by
    have h := hadd 1 hI1 1 hI1
    rw [one_mul] at h
    simpa using h
  have hpow : ∀ n : ℕ, f (σ ^ n) = n • f σ := by
    intro n
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hadd _ (I.pow_mem hI n) _ hI, ih, succ_nsmul]
  have hU : f ⁻¹' {f 1} ∈ nhds (1 : G E Ω) := (hf.isOpen_fiber (f 1)).mem_nhds rfl
  obtain ⟨L, hLfin, hLsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hU
  have hUo : IsOpen (L.fixingSubgroup : Set (G E Ω)) := L.fixingSubgroup_isOpen
  have : Finite (G E Ω ⧸ L.fixingSubgroup) := L.fixingSubgroup.quotient_finite_of_isOpen hUo
  have : L.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hd : L.fixingSubgroup.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hσU : σ ^ L.fixingSubgroup.normalCore.index ∈ L.fixingSubgroup :=
    L.fixingSubgroup.normalCore_le (L.fixingSubgroup.normalCore.pow_index_mem σ)
  obtain ⟨a, d, hdl, hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd l hl.ne_one

  have hl1 : A.valuation (l : Ω) = 1 := by
    have h1 := (hA (l : 𝓞 E)).not.mpr hlv
    have h2 := A.valuation_le_one (l : A)
    simp only [map_natCast] at h1 h2
    exact le_antisymm h2 (not_lt.mp h1)
  have hk : ¬ A.valuation ((l ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hl1, one_pow]
    exact lt_irrefl _
  have hτ : ∀ y : Ω, y ≠ 0 → A.valuation ((σ ^ d) y / y - 1) < 1 :=
    GlobalTheory.WildInertiaChar.wild_pow A σ hσ d
  have hτU : σ ^ d ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ d) hτ (l ^ a) hk x
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσU
    rw [← pow_mul, mul_comm, ← hdec]
    exact hσU x hx
  have hd0 : d • f σ = 0 := by
    rw [← hpow d]
    have := hLsub hτU
    simpa [hf1] using this
  obtain ⟨n, hn⟩ := hM (f σ)
  have hcop : IsCoprime ((l ^ n : ℕ) : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hl).mpr hdl))
  obtain ⟨u, w, huw⟩ := hcop
  calc f σ = (1 : ℤ) • f σ := (one_zsmul _).symm
    _ = (u * ((l ^ n : ℕ) : ℤ) + w * (d : ℤ)) • f σ := by rw [huw]
    _ = u • ((l ^ n) • f σ) + w • (d • f σ) := by
        rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = 0 := by rw [hn, hd0, smul_zero, smul_zero, add_zero]

private theorem valuation_apply_eq_of_valuation_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (y : Ω) :
    A.valuation (σ y) = A.valuation y := by
  by_cases hy : y = 0
  · simp [hy]
  · have h1 : A.valuation (σ y / y) = 1 := by
      have := Valuation.map_one_add_of_lt A.valuation (hσ y hy)
      simpa using this
    rw [← div_mul_cancel₀ (σ y) hy, map_mul, h1, one_mul]

private theorem mem_ine_of_valuation_div_sub_one_lt_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  rw [mem_Ine]
  let : MulAction (G E Ω) (ValuationSubring Ω) := ValuationSubring.pointwiseMulAction
  refine ⟨MulAction.mem_stabilizer_iff.mpr ?_, ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← ValuationSubring.valuation_le_one_iff,
      ← ValuationSubring.valuation_le_one_iff]
    have key : A.valuation x = A.valuation (σ⁻¹ • x) := by
      have h := valuation_apply_eq_of_valuation_div_sub_one_lt A σ hσ (σ⁻¹ • x)
      rwa [← AlgEquiv.smul_def, smul_inv_smul] at h
    rw [key]
  · intro x hx
    by_cases h0 : x = 0
    · simp [h0]
    · have h3 : σ x - x = x * (σ x / x - 1) := by
        rw [mul_sub, mul_div_cancel₀ _ h0, mul_one]
      rw [h3, map_mul]
      calc _ ≤ 1 * A.valuation (σ x / x - 1) := by gcongr
        _ < 1 := by rw [one_mul]; exact hσ x h0

theorem main : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ f : GE D.nd → KOG (D.nd.O i) 1, IsLocallyConstant f → (∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f (a * b) = f a + f b) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), f σ = 0 := by
  intro D i v hv f hf hadd σ hσ
  exact eq_zero_of_wild D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.l i) (D.nd.lPrime i).out hv
    (D.nd.plOm.2 v) (KOG (D.nd.O i) 1) f hf (Ine (F := D.host.E) (D.nd.plOm.1 v)) hadd
    (exists_pow_nsmul_eq_zero (D.nd.l i) (D.nd.O i)) σ (mem_ine_of_valuation_div_sub_one_lt_one _ σ hσ) hσ

end GlobalTheory.WildAdditive
