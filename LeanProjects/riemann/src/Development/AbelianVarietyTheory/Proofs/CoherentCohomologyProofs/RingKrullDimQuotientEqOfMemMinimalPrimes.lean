import Mathlib

open TensorProduct IsLocalRing

namespace GlobalTheory

universe u

theorem ringKrullDim_eq_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] : ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro P Q hPQ
    have : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.comap_lt_comap this
  · refine iSup_le fun l ↦ ?_
    obtain ⟨P, hP⟩ := Algebra.IsIntegral.comap_surjective R S l.head
    have : P.asIdeal.LiesOver l.head.asIdeal := ⟨by rw [← hP]; rfl⟩
    obtain ⟨L, hL, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L

theorem trdeg_eq_of_isAlgebraic_top (R S A : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [CommRing A] [NoZeroDivisors A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [FaithfulSMul R S] [FaithfulSMul S A] [Algebra.IsAlgebraic S A] :
    Algebra.trdeg R A = Algebra.trdeg R S := by
  have : Nontrivial S := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← trdeg_add_eq R S (A := A), trdeg_eq_zero (R := S) (A := A), add_zero]

theorem trdeg_eq_of_isAlgebraic_bot (R S A : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [CommRing A] [NoZeroDivisors A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [FaithfulSMul R S] [FaithfulSMul S A] [Algebra.IsAlgebraic R S] :
    Algebra.trdeg R A = Algebra.trdeg S A := by
  rw [← trdeg_add_eq R S (A := A), trdeg_eq_zero (R := R) (A := S), zero_add]

theorem exists_ringKrullDim_eq_and_trdeg_eq (k B : Type u) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    ∃ d : ℕ, ringKrullDim B = d ∧ Algebra.trdeg k B = d := by
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k B
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hint⟩
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) B,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  · rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k) B, MvPolynomial.trdeg_of_isDomain]
    simp

theorem ringKrullDim_eq_of_trdeg_eq (k B : Type u) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] {d : ℕ} (h : Algebra.trdeg k B = d) :
    ringKrullDim B = d := by
  obtain ⟨e, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq k B
  obtain rfl : e = d := by exact_mod_cast h₂.symm.trans h
  exact h₁

theorem quasiFiniteAt_of_isolated (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hmin : ∀ q' : Ideal S, q'.IsPrime → q'.under R = q.under R → q' ≤ q → q' = q)
    (hmax : ∀ q' : Ideal S, q'.IsPrime → q'.under R = q.under R → q ≤ q' → q' = q) :
    Algebra.QuasiFiniteAt R q := by
  let p := q.under R
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S p
  let q₀ : p.primesOver S := ⟨q, ‹_›, inferInstance⟩
  have h₁ : IsMin q₀ := fun q' h ↦ (hmin q'.1 q'.2.1 q'.2.2.over.symm h).ge
  have h₂ : IsMax q₀ := fun q' h ↦ (hmax q'.1 q'.2.1 q'.2.2.over.symm h).le
  have hq' : q = (e q₀).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($(e.symm_apply_apply q₀).1).symm
  have : IsJacobsonRing (p.Fiber S) := isJacobsonRing_of_finiteType (A := p.ResidueField)
  have : IsNoetherianRing (p.Fiber S) := Algebra.FiniteType.isNoetherianRing p.ResidueField _
  have : Algebra.QuasiFiniteAt p.ResidueField (e q₀).asIdeal := by
    refine .of_isOpen_singleton _ ?_
    refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
      (e q₀)).out 0 2).mpr (And.intro ?_ ?_)
    · rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal, ← PrimeSpectrum.isMax_iff]
      exact (e.isMax_apply).mpr h₂
    · rw [PrimeSpectrum.stableUnderGeneralization_singleton, ← PrimeSpectrum.isMin_iff]
      exact (e.isMin_apply).mpr h₁
  exact .of_quasiFiniteAt_residueField p q _ hq'.symm

theorem isAlgebraic_of_quasiFiniteAt (R S : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [FaithfulSMul R S] (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] : Algebra.IsAlgebraic R S := by
  have : Algebra.QuasiFiniteAt R (⊥ : Ideal S) := .of_le (Q := q) bot_le
  let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal R) (⊥ : Ideal S)
  have : Module.Finite (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField := inferInstance
  have : Algebra.IsAlgebraic (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField :=
    Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic R (⊥ : Ideal R).ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R (⊥ : Ideal S).ResidueField :=
    Algebra.IsAlgebraic.trans R (⊥ : Ideal R).ResidueField _
  exact Algebra.IsAlgebraic.of_injective
    (IsScalarTower.toAlgHom R S (⊥ : Ideal S).ResidueField) (IsFractionRing.injective S _)

section DVR

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type u} [CommRing A] [Algebra O A]

theorem liesOver_maximalIdeal_of_mem_minimalPrimes {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes) :
    q.LiesOver (maximalIdeal O) := by
  have := hq.1.1
  exact ⟨(maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
    (Ideal.map_le_iff_le_comap.mp hq.1.2)⟩

theorem map_maximalIdeal_eq_span_of_irreducible {ϖ : O} (hϖ : Irreducible ϖ) :
    (maximalIdeal O).map (algebraMap O A) = Ideal.span {algebraMap O A ϖ} := by
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

variable [IsDomain A] [Algebra.FiniteType O A] [FaithfulSMul O A]

theorem height_eq_one_of_mem_minimalPrimes_map_maximalIdeal {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes) : q.height = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  rw [map_maximalIdeal_eq_span_of_irreducible O hϖ] at hq
  have := hq.1.1
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ?_
  have hne : q ≠ ⊥ := by
    rintro rfl
    have : algebraMap O A ϖ ∈ (⊥ : Ideal A) := hq.1.2 (Ideal.mem_span_singleton_self _)
    exact hϖ.ne_zero (by simpa using this)
  have := Ideal.height_strict_mono_of_isPrime (I := ⊥) (J := q) (bot_lt_iff_ne_bot.mpr hne)
  exact Order.one_le_iff_pos.mpr (lt_of_le_of_lt zero_le this)

theorem trdeg_quotient_eq_of_mem_minimalPrimes (k : Type u) [Field k] [Algebra O k]
    (hk : Function.Surjective (algebraMap O k)) {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes)
    [Algebra k (A ⧸ q)] [IsScalarTower O k (A ⧸ q)] :
    Algebra.trdeg k (A ⧸ q) = Algebra.trdeg O A := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hqp := hq.1.1
  have : Algebra.FiniteType k (A ⧸ q) := .of_restrictScalars_finiteType O k _
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k (A ⧸ q)
  choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let φ : (MvPolynomial (Fin s) O) →ₐ[O] A := MvPolynomial.aeval x
  have hφ (r : (MvPolynomial (Fin s) O)) : Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap O k) r) := by
    have : (Ideal.Quotient.mk q).comp φ.toRingHom =
        g.toRingHom.comp (MvPolynomial.map (algebraMap O k)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
        rw [← IsScalarTower.algebraMap_apply]
        rfl
      · intro i
        simp [φ, hx]
    exact congr($this r)
  have hker : RingHom.ker (algebraMap O k) = Ideal.span {ϖ} := by
    rw [← hϖ.maximalIdeal_eq]
    exact eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
  have hmem (r : (MvPolynomial (Fin s) O)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hϖA : algebraMap O A ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) O)) := fun h ↦ hqp.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hnu
    rw [map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero] at hr
    rcases hr with hr | hr
    · exact hϖA (pow_eq_zero_iff'.mp hr).1
    · exact ha ((hmem a).mp (hr ▸ q.zero_mem))
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower O (MvPolynomial (Fin s) O) A := IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) O) A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.FiniteType (MvPolynomial (Fin s) O) A := .of_restrictScalars_finiteType O (MvPolynomial (Fin s) O) A
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q) := ⟨hint⟩
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin s) O) q := by
    refine quasiFiniteAt_of_isolated (MvPolynomial (Fin s) O) A q (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)
    · refine hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)
      rw [map_maximalIdeal_eq_span_of_irreducible O hϖ, Ideal.span_singleton_le_iff_mem]
      have : (MvPolynomial.C ϖ : (MvPolynomial (Fin s) O)) ∈ q'.under (MvPolynomial (Fin s) O) := h.ge ((hmem _).mpr dvd_rfl)
      have : φ (MvPolynomial.C ϖ) ∈ q' := this
      simpa using this
    · have : q'.map (Ideal.Quotient.mk q) = ⊥ := by
        refine Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)
        intro y hy
        obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective _ hk y
        have hy : g (MvPolynomial.map (algebraMap O k) r) ∈ q'.map (Ideal.Quotient.mk q) := hy
        rw [← hφ, Ideal.mem_quotient_iff_mem hle] at hy
        have : φ r ∈ q := h.le (show r ∈ q'.under (MvPolynomial (Fin s) O) from hy)
        rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg] at this
        exact this
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this
      exact this.antisymm hle
  have := isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) O) A q
  rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k), trdeg_eq_of_isAlgebraic_top O (MvPolynomial (Fin s) O) A,
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]

omit [IsDiscreteValuationRing O] [FaithfulSMul O A] [IsDomain A] in

theorem exists_trdeg_eq_natCast : ∃ d : ℕ, Algebra.trdeg O A = d :=
  Cardinal.lt_aleph0.mp trdeg_lt_aleph0_of_finiteType

theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes) {d : ℕ}
    (hd : Algebra.trdeg O A = d) : ringKrullDim (A ⧸ q) = d := by
  have := hq.1.1
  have := liesOver_maximalIdeal_of_mem_minimalPrimes O hq
  let := Ideal.Quotient.field (maximalIdeal O)
  have : Algebra.FiniteType (O ⧸ maximalIdeal O) (A ⧸ q) := .of_restrictScalars_finiteType O _ _
  refine ringKrullDim_eq_of_trdeg_eq (O ⧸ maximalIdeal O) _ ?_
  rw [trdeg_quotient_eq_of_mem_minimalPrimes O _ Ideal.Quotient.mk_surjective hq, hd]

omit [Algebra.FiniteType O A] [IsDiscreteValuationRing O] in

theorem trdeg_fractionRing_eq (K F : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    [Field F] [Algebra A F] [IsFractionRing A F] [Algebra O F] [Algebra K F]
    [IsScalarTower O A F] [IsScalarTower O K F] :
    Algebra.trdeg K F = Algebra.trdeg O A := by
  have : Algebra.IsAlgebraic O K := IsLocalization.isAlgebraic _ (nonZeroDivisors O)
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  rw [← trdeg_eq_of_isAlgebraic_bot O K F, trdeg_eq_of_isAlgebraic_top O A F]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [IsDiscreteValuationRing O] in

theorem ringKrullDim_genericFibre_eq (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    {d : ℕ} (hd : Algebra.trdeg O A = d) : ringKrullDim (K ⊗[O] A) = d := by
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors O)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors O) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (K ⊗[O] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have : FaithfulSMul A (K ⊗[O] A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic O K := IsLocalization.isAlgebraic _ (nonZeroDivisors O)
  have : Algebra.IsAlgebraic A (K ⊗[O] A) :=
    IsLocalization.isAlgebraic _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors O))
  refine ringKrullDim_eq_of_trdeg_eq K _ ?_
  rw [← trdeg_eq_of_isAlgebraic_bot O K, trdeg_eq_of_isAlgebraic_top O A, hd]

theorem trdeg_residueField_eq_of_mem_minimalPrimes (k : Type u) [Field k] [Algebra O k]
    (hk : Function.Surjective (algebraMap O k)) (q : Ideal A) [q.IsPrime]
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes)
    [Algebra k q.ResidueField] [IsScalarTower O k q.ResidueField] :
    Algebra.trdeg k q.ResidueField = Algebra.trdeg O A := by
  have hle : RingHom.ker (algebraMap O k) ≤ RingHom.ker (algebraMap O (A ⧸ q)) := by
    rw [eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)]
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hq.1.2 (Ideal.mem_map_of_mem _ hx))
  let := ((algebraMap O k).liftOfSurjective hk ⟨_, hle⟩).toAlgebra
  have : IsScalarTower O k (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm
  have : IsScalarTower k (A ⧸ q) q.ResidueField := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨x, rfl⟩ := hk x
    rw [← IsScalarTower.algebraMap_apply O k (A ⧸ q), ← IsScalarTower.algebraMap_apply O k,
      ← IsScalarTower.algebraMap_apply O (A ⧸ q)]
  have : Algebra.IsAlgebraic (A ⧸ q) q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  rw [trdeg_eq_of_isAlgebraic_top k (A ⧸ q), trdeg_quotient_eq_of_mem_minimalPrimes O k hk hq]

end DVR

theorem height_eq_one_and_ringKrullDim_eq_of_flat
    (O K k : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    (A F : Type u) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A]
    [Module.Flat O A] [Field F] [Algebra A F] [IsFractionRing A F] [Algebra O F] [Algebra K F]
    [IsScalarTower O A F] [IsScalarTower O K F]
    {ϖ : O} (hϖ : Irreducible ϖ) (q : Ideal A) [q.IsPrime]
    (hq : q ∈ (Ideal.span {algebraMap O A ϖ}).minimalPrimes)
    [Algebra k q.ResidueField] [IsScalarTower O k q.ResidueField] :
    q.height = 1 ∧ ∃ d : ℕ, ringKrullDim (A ⧸ q) = d ∧ Algebra.trdeg k q.ResidueField = d ∧
      Algebra.trdeg K F = d ∧ ringKrullDim (K ⊗[O] A) = d := by
  rw [← map_maximalIdeal_eq_span_of_irreducible O hϖ] at hq
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  exact ⟨height_eq_one_of_mem_minimalPrimes_map_maximalIdeal O hq, d,
    ringKrullDim_quotient_eq_of_mem_minimalPrimes O hq hd,
    (trdeg_residueField_eq_of_mem_minimalPrimes O k hk q hq).trans hd,
    (trdeg_fractionRing_eq O (A := A) K F).trans hd, ringKrullDim_genericFibre_eq O K hd⟩

theorem isLocalHom_algebraMap_localization_of_liesOver (O : Type*) [CommRing O] [IsLocalRing O]
    {A : Type*} [CommRing A] [Algebra O A] (q : Ideal A) [q.IsPrime]
    [q.LiesOver (maximalIdeal O)] : IsLocalHom (algebraMap O (Localization.AtPrime q)) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [IsScalarTower.algebraMap_apply O A, IsLocalization.AtPrime.isUnit_to_map_iff _ q] at hx
  by_contra h
  exact hx ((Ideal.mem_of_liesOver q (maximalIdeal O) x).mp h)

theorem height_eq_one_and_ringKrullDim_eq_of_flat_canonical
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A]
    [Module.Flat O A] {ϖ : O} (hϖ : Irreducible ϖ) (q : Ideal A) [q.IsPrime]
    (hq : q ∈ (Ideal.span {algebraMap O A ϖ}).minimalPrimes) :
    haveI := liesOver_maximalIdeal_of_mem_minimalPrimes O
      (map_maximalIdeal_eq_span_of_irreducible O (A := A) hϖ ▸ hq)
    haveI := isLocalHom_algebraMap_localization_of_liesOver O q
    letI := FractionRing.liftAlgebra O (FractionRing A)
    q.height = 1 ∧ ∃ d : ℕ, ringKrullDim (A ⧸ q) = d ∧
      Algebra.trdeg (ResidueField O) q.ResidueField = d ∧
      Algebra.trdeg (FractionRing O) (FractionRing A) = d ∧
      ringKrullDim (FractionRing O ⊗[O] A) = d := by
  have := liesOver_maximalIdeal_of_mem_minimalPrimes O
    (map_maximalIdeal_eq_span_of_irreducible O (A := A) hϖ ▸ hq)
  have := isLocalHom_algebraMap_localization_of_liesOver O q
  let := FractionRing.liftAlgebra O (FractionRing A)
  have := FractionRing.isScalarTower_liftAlgebra O (FractionRing A)
  exact height_eq_one_and_ringKrullDim_eq_of_flat O (FractionRing O) (ResidueField O)
    residue_surjective A (FractionRing A) hϖ q hq

section Topology

open Topology TopologicalSpace

theorem topologicalKrullDim_eq_of_isEmbedding {W X : Type*} [TopologicalSpace W]
    [TopologicalSpace X] {e : W → X} (he : IsEmbedding e) {Z : Set X} (hZ : Set.range e = Z) :
    topologicalKrullDim Z = topologicalKrullDim W := by
  subst hZ
  exact (he.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _).symm

theorem topologicalKrullDim_le_of_forall_exists_isOpen {X : Type*} [TopologicalSpace X]
    {d : WithBot ℕ∞} (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro T
  obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
  obtain ⟨U, hU, hxU, hd⟩ := h x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hU.isOpenEmbedding_subtypeVal
  obtain ⟨T', hT'⟩ := e.surjective ⟨T, ⟨x, hxU⟩, hx⟩
  have : IrreducibleCloseds.map _ hU.isOpenEmbedding_subtypeVal.continuous T' = T :=
    congr($(hT').1)
  rw [← this, hU.isOpenEmbedding_subtypeVal.coheight_map]
  exact (Order.coheight_le_krullDim T').trans hd

theorem topologicalKrullDim_eq_of_forall_exists_isOpen {X : Type*} [TopologicalSpace X]
    {Z : Set X} (hZ : Z.Nonempty) {d : WithBot ℕ∞}
    (h : ∀ x ∈ Z, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim (U ∩ Z : Set X) = d) :
    topologicalKrullDim Z = d := by
  have key (U : Set X) : topologicalKrullDim (U ∩ Z : Set X) =
      topologicalKrullDim (Subtype.val ⁻¹' U : Set Z) :=
    topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
      (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])
  apply le_antisymm
  · refine topologicalKrullDim_le_of_forall_exists_isOpen fun x ↦ ?_
    obtain ⟨U, hU, hxU, hd⟩ := h x x.2
    exact ⟨_, hU.preimage continuous_subtype_val, hxU, ((key U).symm.trans hd).le⟩
  · obtain ⟨x, hx⟩ := hZ
    obtain ⟨U, -, -, hd⟩ := h x hx
    rw [← hd, key]
    exact topologicalKrullDim_subspace_le _ _

end Topology

section Scheme

open AlgebraicGeometry CategoryTheory Topology

variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]

theorem exists_affine_chart_trdeg_eq (x : Y) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra O A)
      (_ : Algebra.FiniteType O A) (_ : FaithfulSMul O A) (j : Spec (.of A) ⟶ Y)
      (_ : IsOpenImmersion j), x ∈ Set.range j ∧
      j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)) ∧
      Algebra.trdeg O A = Algebra.trdeg O Y.functionField := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra O Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType O Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have hfl : Module.Flat O Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp (hφ ▸ inferInstance)
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcomp : φ ≫ Y.presheaf.germ U _ hη = Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_preimage, ← hU.fromSpecStalk_eq_fromSpecStalk hη,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower O Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congr($(hcomp).hom a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  refine ⟨Γ(Y, U), inferInstance, inferInstance, inferInstance, hft, inferInstance, hU.fromSpec,
    inferInstance, ?_, hφ.symm, (trdeg_eq_of_isAlgebraic_top O Γ(Y, U) Y.functionField).symm⟩
  rw [hU.range_fromSpec]
  exact hxU

end Scheme

section Fibres

open AlgebraicGeometry CategoryTheory Topology Limits

variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem topologicalKrullDim_preimage_genericPoint_eq {d : ℕ}
    (hd : letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
      Algebra.trdeg O Y.functionField = d) :
    topologicalKrullDim (f ⁻¹' {genericPoint (Spec (.of O))} : Set Y) = d := by
  have hgen : genericPoint (Spec (.of O)) = (⟨⊥, inferInstance⟩ : PrimeSpectrum O) :=
    genericPoint_eq_bot_of_affine (.of O)
  refine topologicalKrullDim_eq_of_forall_exists_isOpen ?_ fun x _ ↦ ?_
  · obtain ⟨A, _, _, _, _, _, j, _, -, hj, -⟩ :=
      exists_affine_chart_trdeg_eq f (genericPoint Y)
    refine ⟨j (⟨⊥, inferInstance⟩ : PrimeSpectrum A), ?_⟩
    change (j ≫ f) _ = _
    rw [hj, hgen]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective O A))
  · obtain ⟨A, _, _, _, _, _, j, _, hx, hj, hA⟩ := exists_affine_chart_trdeg_eq f x
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
    have := IsLocalization.tensorRight (S := A) (FractionRing O) (nonZeroDivisors O)
    rw [← ringKrullDim_genericFibre_eq O (FractionRing O) (hA.trans hd),
      ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    refine topologicalKrullDim_eq_of_isEmbedding (j.isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.localization_comap_isEmbedding (FractionRing O ⊗[O] A)
        (Algebra.algebraMapSubmonoid A (nonZeroDivisors O)))) ?_
    refine (Set.range_comp _ _).trans
      (.trans (congrArg (Set.image j) ?_) Set.image_preimage_eq_range_inter)
    refine (PrimeSpectrum.localization_comap_range _
      (Algebra.algebraMapSubmonoid A (nonZeroDivisors O))).trans ?_
    ext p
    change _ ↔ (j ≫ f) p = _
    rw [hj, hgen]
    change Disjoint _ _ ↔ PrimeSpectrum.comap (algebraMap O A) p = _
    rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal, eq_bot_iff, Set.disjoint_left]
    constructor
    · intro h a ha
      by_contra h0
      exact h ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ ha
    · rintro h _ ⟨a, ha, rfl⟩ hp
      exact nonZeroDivisors.ne_zero ha (h hp)

variable [IsDiscreteValuationRing O]

omit [IsIntegral Y] [LocallyOfFiniteType f] [Flat f] in

theorem mem_minimalPrimes_of_mem_irreducibleComponents {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S)
    {A : Type u} [CommRing A] [Algebra O A] {j : Spec (.of A) ⟶ Y} [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)))
    {q : PrimeSpectrum A} (hq : IsGenericPoint (j q) (i '' Z)) :
    q.asIdeal ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes := by
  have key (p : PrimeSpectrum A) :
      j p ∈ Set.range i ↔ (maximalIdeal O).map (algebraMap O A) ≤ p.asIdeal := by
    rw [hr]
    change (j ≫ f) p = _ ↔ _
    rw [hj, Ideal.map_le_iff_le_comap]
    change PrimeSpectrum.comap (algebraMap O A) p = _ ↔ _
    rw [PrimeSpectrum.ext_iff]
    exact ⟨fun h ↦ h.ge, fun h ↦ ((maximalIdeal.isMaximal O).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) h).symm⟩
  refine ⟨⟨q.2, (key q).mp (Set.image_subset_range _ _ hq.mem)⟩, fun p hp hpq ↦ ?_⟩
  obtain ⟨s, hs⟩ := (key ⟨p, hp.1⟩).mpr hp.2
  have h₁ : j (⟨p, hp.1⟩ : PrimeSpectrum A) ⤳ j q :=
    ((PrimeSpectrum.le_iff_specializes ⟨p, hp.1⟩ q).mp hpq).map j.continuous
  have h₂ : Z ⊆ closure {s} := fun z hz ↦ by
    rw [← specializes_iff_mem_closure, ← hi.isInducing.specializes_iff, hs]
    exact h₁.trans (hq.specializes ⟨z, hz, rfl⟩)
  have h₃ : s ∈ Z := hZ.2 isIrreducible_singleton.closure h₂ (subset_closure rfl)
  have h₄ : j q ⤳ j (⟨p, hp.1⟩ : PrimeSpectrum A) := hq.specializes ⟨s, h₃, hs⟩
  exact (PrimeSpectrum.le_iff_specializes q ⟨p, hp.1⟩).mpr
    (j.isOpenEmbedding.isInducing.specializes_iff.mp h₄)

omit [IsIntegral Y] [LocallyOfFiniteType f] [Flat f] in

theorem isClosed_image_of_mem_irreducibleComponents {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) : IsClosed (i '' Z) := by
  have : IsClosedEmbedding i := ⟨hi, hr ▸ (isClosed_singleton_closedPoint O).preimage f.continuous⟩
  exact this.isClosedMap _ (isClosed_of_mem_irreducibleComponents Z hZ)

theorem topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq
    {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) {d : ℕ}
    (hd : letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
      Algebra.trdeg O Y.functionField = d) :
    topologicalKrullDim Z = d := by
  have hirr : IsIrreducible (i '' Z) := hZ.1.image i hi.continuous.continuousOn
  have hη := hirr.isGenericPoint_genericPoint
    (isClosed_image_of_mem_irreducibleComponents f hi hr hZ)
  rw [← topologicalKrullDim_eq_of_isEmbedding (hi.comp (IsEmbedding.subtypeVal (p := (· ∈ Z))))
    (Z := i '' Z) (by rw [Set.range_comp, Subtype.range_coe])]
  refine topologicalKrullDim_eq_of_forall_exists_isOpen hirr.nonempty fun x hxZ ↦ ?_
  obtain ⟨A, _, _, _, _, _, j, _, hx, hj, hA⟩ := exists_affine_chart_trdeg_eq f x
  refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
  obtain ⟨q, hq⟩ := (hη.specializes hxZ).mem_open j.isOpenEmbedding.isOpen_range hx
  rw [← hq] at hη
  have hmin := mem_minimalPrimes_of_mem_irreducibleComponents f hi hr hZ hj hη
  rw [← ringKrullDim_quotient_eq_of_mem_minimalPrimes O hmin (hA.trans hd),
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine topologicalKrullDim_eq_of_isEmbedding (j.isOpenEmbedding.isEmbedding.comp
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk q.asIdeal)
      Ideal.Quotient.mk_surjective).isEmbedding) ?_
  refine (Set.range_comp _ _).trans
    (.trans (congrArg (Set.image j) ?_) Set.image_preimage_eq_range_inter)
  refine (range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).trans ?_
  rw [Ideal.mk_ker, ← hη.def, ← Set.image_singleton]
  exact (PrimeSpectrum.closure_singleton q).symm.trans
    (j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image _)

theorem ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents
    {S : Type*} [TopologicalSpace S]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) {z : S} (hz : IsGenericPoint z Z) :
    ringKrullDim (Y.presheaf.stalk (i z)) = 1 := by
  have hη : IsGenericPoint (i z) (i '' Z) := by
    have := hz.image hi.continuous
    rwa [(isClosed_image_of_mem_irreducibleComponents f hi hr hZ).closure_eq] at this
  obtain ⟨A, _, _, _, _, _, j, _, ⟨q, hq⟩, hj, -⟩ := exists_affine_chart_trdeg_eq f (i z)
  rw [← hq] at hη ⊢
  have hmin := mem_minimalPrimes_of_mem_irreducibleComponents f hi hr hZ hj hη
  rw [ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap q)).commRingCatIsoToRingEquiv,
    ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of A) q).commRingCatIsoToRingEquiv]
  have := q.isPrime
  refine (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal _).trans ?_
  rw [height_eq_one_of_mem_minimalPrimes_map_maximalIdeal O hmin]
  rfl

theorem exists_topologicalKrullDim_fibres_eq_of_isEmbedding
    {S G : Type*} [TopologicalSpace S] [TopologicalSpace G]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {i' : G → Y} (hi' : IsEmbedding i')
    (hr' : Set.range i' = f ⁻¹' {genericPoint (Spec (.of O))}) :
    ∃ d : ℕ, topologicalKrullDim G = d ∧
      ∀ Z ∈ irreducibleComponents S, topologicalKrullDim Z = d := by
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint Y)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  rw [hA] at hd
  exact ⟨d, (topologicalKrullDim_eq_of_isEmbedding hi' hr').symm.trans
    (topologicalKrullDim_preimage_genericPoint_eq f hd),
    fun Z hZ ↦ topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq f hi hr hZ hd⟩

theorem topologicalKrullDim_component_fiber_eq {Z : Set (f.fiber (closedPoint O))}
    (hZ : Z ∈ irreducibleComponents (f.fiber (closedPoint O))) :
    topologicalKrullDim Z = topologicalKrullDim (f.fiber (genericPoint (Spec (.of O)))) := by
  obtain ⟨d, h₁, h₂⟩ := exists_topologicalKrullDim_fibres_eq_of_isEmbedding f
    (f.fiberι _).isEmbedding (f.range_fiberι _) (f.fiberι _).isEmbedding (f.range_fiberι _)
  rw [h₁, h₂ Z hZ]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsIntegral Y] [LocallyOfFiniteType f] [Flat f] in

theorem isEmbedding_and_range_eq_of_isPullback {T P : Scheme.{u}} {g : T ⟶ Spec (.of O)}
    [IsPreimmersion g] {i : P ⟶ Y} {p : P ⟶ T} (h : IsPullback i p f g) :
    IsEmbedding i ∧ Set.range i = f ⁻¹' Set.range g := by
  have : IsPreimmersion i := MorphismProperty.of_isPullback h.flip inferInstance
  refine ⟨i.isEmbedding, ?_⟩
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

theorem exists_topologicalKrullDim_fibres_eq_of_isPullback
    (K k : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    {Y₀ Y₁ : Scheme.{u}} {i₀ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Spec (.of k)} {i₁ : Y₁ ⟶ Y}
    {p₁ : Y₁ ⟶ Spec (.of K)}
    (h₀ : IsPullback i₀ p₀ f (Spec.map (CommRingCat.ofHom (algebraMap O k))))
    (h₁ : IsPullback i₁ p₁ f (Spec.map (CommRingCat.ofHom (algebraMap O K)))) :
    ∃ d : ℕ, topologicalKrullDim Y₁ = d ∧ ∀ Z ∈ irreducibleComponents Y₀,
      topologicalKrullDim Z = d ∧
        ∀ z, IsGenericPoint z Z → ringKrullDim (Y.presheaf.stalk (i₀ z)) = 1 := by
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap O k)) hk
  have := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)
  obtain ⟨e₀, r₀⟩ := isEmbedding_and_range_eq_of_isPullback f h₀
  obtain ⟨e₁, r₁⟩ := isEmbedding_and_range_eq_of_isPullback f h₁
  have hr₀ : Set.range (Spec.map (CommRingCat.ofHom (algebraMap O k))) = {closedPoint O} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap O k) x.asIdeal = maximalIdeal O
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
  have hr₁ : Set.range (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
      {genericPoint (Spec (.of O))} := by
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨Set.range_nonempty _, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap O K) x.asIdeal = ⊥
    have := x.isPrime
    rw [Ideal.eq_bot_of_prime x.asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  rw [hr₀] at r₀
  rw [hr₁] at r₁
  obtain ⟨d, hd₁, hd₀⟩ := exists_topologicalKrullDim_fibres_eq_of_isEmbedding f e₀ r₀ e₁ r₁
  exact ⟨d, hd₁, fun Z hZ ↦ ⟨hd₀ Z hZ, fun z hz ↦
    ringKrullDim_stalk_eq_one_of_mem_irreducibleComponents f e₀ r₀ hZ hz⟩⟩

end Fibres

example (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) : (Ideal.span {algebraMap O (Polynomial O) ϖ}).height = 1 := by
  have : (Ideal.span {algebraMap O (Polynomial O) ϖ}).IsPrime :=
    (Ideal.span_singleton_prime (by simpa using hϖ.ne_zero)).mpr
      (Polynomial.prime_C_iff.mpr hϖ.prime)
  exact (height_eq_one_and_ringKrullDim_eq_of_flat_canonical O (Polynomial O) hϖ _
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)).1

end GlobalTheory
