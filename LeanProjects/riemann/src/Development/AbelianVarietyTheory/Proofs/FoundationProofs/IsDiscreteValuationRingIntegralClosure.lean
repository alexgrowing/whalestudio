import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.FourierCoeffIntSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

noncomputable section

open IsLocalRing MvPowerSeries

namespace GlobalTheory.FormalIsogeny

section Nakayama

theorem finite_of_finite_quotient_smul_top {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) [IsPrecomplete I A] [IsHausdorff I M]
    [Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))] : Module.Finite A M := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := M ⧸ (I • ⊤ : Submodule A M))
  choose m hm using fun i => Submodule.Quotient.mk_surjective _ (g i)
  have : IsPrecomplete I (Fin n → A) := by
    refine ⟨fun u hu => ?_⟩
    have h1 : ∀ i, ∃ L : A, ∀ k, u k i ≡ L [SMOD (I ^ k • ⊤ : Submodule A A)] := fun i =>
      IsPrecomplete.prec' (fun k => u k i) fun {a b} hab => by
        have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := A) (φ := fun _ => A) i)
          (SModEq.sub_mem.1 (hu hab))
        rw [Submodule.map_smul''] at this
        exact SModEq.sub_mem.2 (Submodule.smul_mono le_rfl le_top this)
    choose L hL using h1
    refine ⟨L, fun k => SModEq.sub_mem.2 ?_⟩
    rw [← Finset.univ_sum_single (u k - L)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h2 : u k i - L i ∈ I ^ k := by simpa using SModEq.sub_mem.1 (hL i k)
    have h3 : (Pi.single i ((u k - L) i) : Fin n → A) = (u k i - L i) • Pi.single i 1 := by
      rw [← Pi.single_smul']; simp
    rw [h3]
    exact Submodule.smul_mem_smul h2 trivial
  refine Module.Finite.of_surjective (Fintype.linearCombination A m)
    (surjective_of_mkQ_comp_surjective (I := I) ?_)
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, by simp [hm]⟩

theorem finite_of_finite_quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [IsPrecomplete I A] [IsHausdorff (I.map (algebraMap A B)) B]
    [Module.Finite A (B ⧸ I.map (algebraMap A B))] : Module.Finite A B := by
  have : IsHausdorff I B := IsHausdorff.map_algebraMap_iff.1 ‹_›
  have : Module.Finite A (B ⧸ (I • ⊤ : Submodule A B)) := by
    rw [Ideal.smul_top_eq_map]
    exact .equiv (Submodule.Quotient.restrictScalarsEquiv A (I.map (algebraMap A B))).symm
  exact finite_of_finite_quotient_smul_top I

theorem isPrecomplete_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by
  refine ⟨fun u hu => ?_⟩
  have he' : ∀ n, I ^ ((e + 1) * n) ≤ J ^ n := fun n => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right e.le_succ).trans he) n
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun n => u ((e + 1) * n)) fun {m n} hmn =>
    (hu (Nat.mul_le_mul_left _ hmn)).mono (Submodule.smul_mono_left (he' m))
  exact ⟨L, fun n => (hu (Nat.le_mul_of_pos_left n e.succ_pos)).trans
    ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJ n)))⟩

theorem isAdicComplete_maximalIdeal_of_finite (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by
  have := IsNoetherianRing.of_finite R S
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := R) S
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal S ^ e ≤ (maximalIdeal R).map (algebraMap R S) := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg (fun b hb => ?_) (IsNoetherian.noetherian _)
    obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := R) S b
      fun n hn => eq_maximalIdeal hn ▸ hb
    exact ⟨N, hN⟩
  have := isPrecomplete_of_pow_le
    (ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) S _ inferInstance) he
  exact ⟨⟩

end Nakayama

section IntegralClosure

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]

include K

theorem finite_integralClosure : Module.Finite R (integralClosure R L) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful R K L
  have hinj := FaithfulSMul.algebraMap_injective R L
  set B := integralClosure R L
  have hBn : IsNoetherianRing B := (krullAkizuki K B).1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : (maximalIdeal R).map (algebraMap R B) = Ideal.span {algebraMap R B π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have : IsHausdorff ((maximalIdeal R).map (algebraMap R B)) B := by
    refine IsHausdorff.of_isDomain _ ?_
    obtain ⟨n, hn⟩ := Ideal.exists_maximal B
    refine ne_top_of_le_ne_top hn.ne_top (Ideal.map_le_iff_le_comap.2 ?_)
    exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)).ge
  have halg : Algebra.IsAlgebraic R L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := K) (C := L)).mpr inferInstance
  obtain ⟨s, hsT, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := K) (B : Set L)).mp
    (IsNoetherian.noetherian _)
  let C := Algebra.adjoin R (s : Set L)
  have hCB : C ≤ B := Algebra.adjoin_le hsT
  have hCf : Module.Finite R C :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet fun x hx => hsT hx
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  have hCd : Ring.DimensionLEOne C := Ring.DimensionLEOne.of_isIntegral R C
  letI : Algebra C B := (Subalgebra.inclusion hCB).toAlgebra
  have : IsScalarTower R C B := .of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Subalgebra.inclusion_injective hCB)
  have hfin : Module.Finite C (B ⧸ Ideal.span {algebraMap C B (algebraMap R C π)}) := by
    refine finite_quotient_span_of_birational (fun x => ?_) fun h => ?_
    · have h1 : (x : L) ∈ Submodule.span K (s : Set L) := hs ▸ Submodule.subset_span x.2
      obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ _ h1
      refine ⟨algebraMap R C d, fun h => ?_, ⟨_, Algebra.span_le_adjoin R _ hd⟩, Subtype.ext ?_⟩
      · have h3 : algebraMap R L d = 0 := congrArg Subtype.val h
        exact nonZeroDivisors.coe_ne_zero d (hinj (h3.trans (map_zero _).symm))
      · change algebraMap R L d * x = (d : R) • (x : L)
        rw [Algebra.smul_def]
    · have h3 : algebraMap R L π = 0 := congrArg Subtype.val h
      exact hπ.ne_zero (hinj (h3.trans (map_zero _).symm))
  have : Module.Finite R (B ⧸ (maximalIdeal R).map (algebraMap R B)) := by
    rw [hm, IsScalarTower.algebraMap_apply R C B]
    exact .trans C _
  exact finite_of_finite_quotient_map (maximalIdeal R)

theorem isDiscreteValuationRing_integralClosure : IsDiscreteValuationRing (integralClosure R L) :=
  have := finite_integralClosure R K L
  ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr R K L

end IntegralClosure

section PowerSeries

variable {R : Type*} [CommRing R] {σ τ : Type*}

theorem mem_maximalIdeal_iff_constantCoeff [IsLocalRing R] {g : MvPowerSeries σ R} :
    g ∈ maximalIdeal (MvPowerSeries σ R) ↔ constantCoeff g ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

theorem mem_map_C_of_coeff_mem {I : Ideal R} (hI : I.FG) {g : MvPowerSeries σ R}
    (hg : ∀ d, coeff d g ∈ I) : g ∈ I.map (C : R →+* MvPowerSeries σ R) := by
  obtain ⟨n, s, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  choose c hc using fun d => (Submodule.mem_span_range_iff_exists_fun R).1 (hg d)
  have : g = ∑ i, (show MvPowerSeries σ R from fun d => c d i) * C (s i) := by
    ext d
    rw [← hc d, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [coeff_mul_C]; rfl
  rw [this]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem _ (Submodule.subset_span ⟨i, rfl⟩))

theorem map_surjective_of_surjective {S : Type*} [CommRing S] {φ : R →+* S}
    (hφ : Function.Surjective φ) :
    Function.Surjective (MvPowerSeries.map φ : MvPowerSeries σ R →+* MvPowerSeries σ S) := by
  intro g
  choose c hc using fun d => hφ (coeff d g)
  exact ⟨c, by ext d; exact hc d⟩

theorem ringKrullDim_powerSeries (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim (PowerSeries R) = ringKrullDim R + 1 := by
  refine le_antisymm ?_ ringKrullDim_succ_le_ringKrullDim_powerseries
  have hX : (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have h := ringKrullDim_le_ringKrullDim_quotient_add_card
    ({PowerSeries.X} : Finset (PowerSeries R)) (by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      simpa using hX)
  have hker : Ideal.span (({PowerSeries.X} : Finset (PowerSeries R)) : Set (PowerSeries R)) =
      RingHom.ker (PowerSeries.constantCoeff (R := R)) := by
    ext g
    rw [Finset.coe_singleton, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, RingHom.mem_ker]
  have e := (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective
    (f := PowerSeries.constantCoeff (R := R)) fun r => ⟨PowerSeries.C r, PowerSeries.constantCoeff_C r⟩)
  rw [ringKrullDim_eq_of_ringEquiv e] at h
  simpa using h

theorem isRegularLocalRing_powerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (PowerSeries R) := by
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  have hX : (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hm : (maximalIdeal (PowerSeries R)).map PowerSeries.constantCoeff = maximalIdeal R :=
    map_maximalIdeal_of_surjective _ fun r => ⟨PowerSeries.C r, PowerSeries.constantCoeff_C r⟩
  have h := PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem hX
  rw [hm] at h
  rw [ringKrullDim_powerSeries, ← IsRegularLocalRing.spanFinrank_maximalIdeal]
  exact_mod_cast h

theorem isRegularLocalRing_mvPowerSeries (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (σ : Type*) [Finite σ] : IsRegularLocalRing (MvPowerSeries σ R) := by
  have : ∀ n, IsRegularLocalRing (MvPowerSeries (Fin n) R) := fun n => by
    induction n with
    | zero => exact IsRegularLocalRing.of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
    | succ n ih =>
      have := isRegularLocalRing_powerSeries (MvPowerSeries (Fin n) R)
      exact IsRegularLocalRing.of_ringEquiv (finSuccEquiv R n).toRingEquiv.symm
  have := this (Nat.card σ)
  exact IsRegularLocalRing.of_ringEquiv (renameEquiv R (Finite.equivFin σ)).toRingEquiv.symm

theorem ringKrullDim_mvPowerSeries (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (σ : Type*) [Finite σ] : ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + Nat.card σ := by
  rw [ringKrullDim_eq_of_ringEquiv (renameEquiv R (Finite.equivFin σ)).toRingEquiv]
  induction Nat.card σ with
  | zero => simpa using ringKrullDim_eq_of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv
  | succ n ih =>
    rw [ringKrullDim_eq_of_ringEquiv (finSuccEquiv R n).toRingEquiv, ringKrullDim_powerSeries, ih,
      Nat.cast_add_one, add_assoc]

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]

theorem finite_quotient_of_residue (J : Ideal (MvPowerSeries σ R))
    (h : Module.Finite (ResidueField R)
      (MvPowerSeries σ (ResidueField R) ⧸ J.map (MvPowerSeries.map (residue R)))) :
    Module.Finite R (MvPowerSeries σ R ⧸ J) := by
  have h1 : IsHausdorff (maximalIdeal R) (MvPowerSeries σ R ⧸ J) := by
    refine IsHausdorff.of_map (J := maximalIdeal (MvPowerSeries σ R)) ?_
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact mem_maximalIdeal_iff_constantCoeff.2 hr
  have h2 := (IsHausdorff.map_algebraMap_iff (S := MvPowerSeries σ R ⧸ J)).2 h1
  have h3 : Module.Finite R
      (MvPowerSeries σ (ResidueField R) ⧸ J.map (MvPowerSeries.map (residue R))) :=
    .trans (ResidueField R) _
  have hsurj := map_surjective_of_surjective (σ := σ) (residue_surjective (R := R))
  let p : MvPowerSeries σ R →ₐ[R]
      MvPowerSeries σ (ResidueField R) ⧸ J.map (MvPowerSeries.map (residue R)) :=
    (Ideal.Quotient.mkₐ R _).comp
      { MvPowerSeries.map (residue R) with
        commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }
  have hp : Function.Surjective p := Ideal.Quotient.mk_surjective.comp hsurj
  let q : MvPowerSeries σ R →ₐ[R] (MvPowerSeries σ R ⧸ J) ⧸
      (maximalIdeal R).map (algebraMap R (MvPowerSeries σ R ⧸ J)) :=
    (Ideal.Quotient.mkₐ R _).comp (Ideal.Quotient.mkₐ R _)
  have hq : Function.Surjective q :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hpq : ∀ g ∈ RingHom.ker p, q g = 0 := by
    intro g hg
    have h4 : MvPowerSeries.map (residue R) g ∈ J.map (MvPowerSeries.map (residue R)) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hg
    obtain ⟨u, hu, hug⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 h4
    have h5 : g - u ∈ (maximalIdeal R).map (C : R →+* MvPowerSeries σ R) :=
      mem_map_C_of_coeff_mem (IsNoetherian.noetherian _) fun d => by
        rw [← residue_eq_zero_iff, ← coeff_map, map_sub, hug, sub_self, map_zero]
    have h6 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) h5
    rw [Ideal.map_map, map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hu, sub_zero] at h6
    exact Ideal.Quotient.eq_zero_iff_mem.2 h6
  have h7 : Module.Finite R (MvPowerSeries σ R ⧸ RingHom.ker p) :=
    .equiv (Ideal.quotientKerAlgEquivOfSurjective hp).symm.toLinearEquiv
  have h8 : Module.Finite R ((MvPowerSeries σ R ⧸ J) ⧸
      (maximalIdeal R).map (algebraMap R (MvPowerSeries σ R ⧸ J))) :=
    Module.Finite.of_surjective (Ideal.Quotient.liftₐ _ q hpq).toLinearMap
      (Ideal.Quotient.lift_surjective_of_surjective _ hpq hq)
  exact finite_of_finite_quotient_map (maximalIdeal R)

def FiniteReduction {R : Type*} [CommRing R] [IsLocalRing R] {σ τ : Type*}
    (f : τ → MvPowerSeries σ R) : Prop :=
  Module.Finite (ResidueField R) (MvPowerSeries σ (ResidueField R) ⧸
    Ideal.span (Set.range fun j => MvPowerSeries.map (residue R) (f j)))

theorem FiniteReduction.finite_quotient {f : τ → MvPowerSeries σ R} (h : FiniteReduction f) :
    Module.Finite R (MvPowerSeries σ R ⧸ Ideal.span (Set.range f)) := by
  refine finite_quotient_of_residue _ ?_
  rw [Ideal.map_span, ← Set.range_comp]
  exact h

variable [Finite τ]

theorem finite_of_finiteReduction (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) (h : FiniteReduction fun j => φ (X j)) :
    φ.toRingHom.Finite := by
  have h1 := h.finite_quotient
  have key : ∀ (A : Type _) [CommRing A] [Algebra R A] [Algebra A (MvPowerSeries σ R)]
      [IsScalarTower R A (MvPowerSeries σ R)] (I : Ideal A) [IsPrecomplete I A],
      I.map (algebraMap A (MvPowerSeries σ R)) = Ideal.span (Set.range fun j => φ (X j)) →
      Module.Finite A (MvPowerSeries σ R) := by
    intro A _ _ _ _ I _ hI
    have : IsHausdorff (I.map (algebraMap A (MvPowerSeries σ R))) (MvPowerSeries σ R) := by
      refine IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top ?_)
      rw [hI, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact mem_maximalIdeal_iff_constantCoeff.2 (h0 j)
    have : Module.Finite A (MvPowerSeries σ R ⧸ I.map (algebraMap A (MvPowerSeries σ R))) := by
      rw [hI]
      exact .of_restrictScalars_finite R _ _
    exact finite_of_finite_quotient_map I
  refine @key (MvPowerSeries τ R) _ _ φ.toRingHom.toAlgebra
    (@IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ _ φ.toRingHom.toAlgebra _ fun r => (φ.commutes r).symm)
    (Ideal.span (Set.range X)) _ ?_
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ] in

theorem isLocalHom_of_constantCoeff_mem (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) : IsLocalHom φ.toRingHom := by
  refine ((IsLocalRing.local_hom_TFAE _).out 0 3).2 fun g hg => ?_
  have h1 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal _)
    (fun j => mem_maximalIdeal_iff_constantCoeff.2 (h0 j)) g
  have h2 : algebraMap R (MvPowerSeries σ R) (constantCoeff g) ∈ maximalIdeal _ := by
    exact mem_maximalIdeal_iff_constantCoeff.2
      ((mem_maximalIdeal_iff_constantCoeff (g := g)).1 hg)
  simpa using add_mem h1 h2

end PowerSeries

section Criterion

variable {R : Type*} [CommRing R] {σ τ : Type*} [Finite σ]

theorem finite_quotient_of_pow_le {J : Ideal (MvPowerSeries σ R)} {N : ℕ}
    (h : Ideal.span (Set.range X) ^ N ≤ J) : Module.Finite R (MvPowerSeries σ R ⧸ J) := by
  refine Module.Finite.of_surjective (((Ideal.Quotient.mkₐ R J).comp
    (MvPolynomial.coeToMvPowerSeries.algHom R)).toLinearMap ∘ₗ
      (MvPolynomial.restrictTotalDegree σ R N).subtype) fun y => ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨⟨truncTotal (N + 1) g, (MvPolynomial.mem_restrictTotalDegree _ _ _).2
    (Nat.le_of_lt_succ (totalDegree_truncTotal_lt _ N.succ_ne_zero))⟩, ?_⟩
  refine Ideal.Quotient.eq.2 (h ?_)
  rw [← germIdeal_eq_span, mem_germIdeal_pow_iff_le_order]
  refine nat_le_order fun d hd => ?_
  simp [coeff_truncTotal _ (Nat.lt_succ_of_lt hd)]

theorem exists_pow_le_of_finite_quotient {k : Type*} [Field k] {J : Ideal (MvPowerSeries σ k)}
    (h : Module.Finite k (MvPowerSeries σ k ⧸ J)) : ∃ N, Ideal.span (Set.range X) ^ N ≤ J := by
  have : IsArtinianRing (MvPowerSeries σ k ⧸ J) := IsArtinianRing.of_finite k _
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := MvPowerSeries σ k ⧸ J)
  have h1 : (Ideal.span (Set.range X)).map (Ideal.Quotient.mk J) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Ideal.mem_jacobson_bot.2 fun y => ?_
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : IsUnit (X i * g + 1 : MvPowerSeries σ k) := by simp [isUnit_iff_constantCoeff]
    simpa using this.map (Ideal.Quotient.mk J)
  refine ⟨N, ?_⟩
  have h2 := Ideal.pow_right_mono h1 N
  rwa [hN, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_le_iff_le_comap,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h2

variable [IsLocalRing R]

theorem finiteReduction_iff {f : τ → MvPowerSeries σ R} : FiniteReduction f ↔
    ∃ N, Ideal.span (Set.range X) ^ N ≤
      Ideal.span (Set.range fun j => MvPowerSeries.map (residue R) (f j)) :=
  ⟨exists_pow_le_of_finite_quotient, fun ⟨_, h⟩ => finite_quotient_of_pow_le h⟩

theorem FiniteReduction.map {S : Type*} [CommRing S] [IsLocalRing S] (ρ : R →+* S) [IsLocalHom ρ]
    {f : τ → MvPowerSeries σ R} (h : FiniteReduction f) :
    FiniteReduction fun j => MvPowerSeries.map ρ (f j) := by
  obtain ⟨N, hN⟩ := finiteReduction_iff.1 h
  refine finiteReduction_iff.2 ⟨N, ?_⟩
  have := Ideal.map_mono (f := MvPowerSeries.map (σ := σ) (ResidueField.map ρ)) hN
  rw [Ideal.map_pow, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp] at this
  have e1 : (MvPowerSeries.map (σ := σ) (ResidueField.map ρ)) ∘ X = X := by
    ext1 i
    simp
  have e2 : ((MvPowerSeries.map (ResidueField.map ρ)) ∘
      fun j => MvPowerSeries.map (residue R) (f j)) =
      fun j => MvPowerSeries.map (residue S) (MvPowerSeries.map ρ (f j)) := by
    ext j d
    simp only [Function.comp_apply, coeff_map, ResidueField.map_residue]
  rwa [e1, e2] at this

end Criterion

section Free

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {σ τ : Type*} [Finite σ] [Finite τ]

theorem flat_injective_basis_of_finite {A B : Type*} [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsRegularLocalRing B] (ψ : A →+* B) [IsLocalHom ψ] (hψ : ψ.Finite)
    (hd : ringKrullDim A ≤ ringKrullDim B) :
    ψ.Flat ∧ Function.Injective ψ ∧ @Module.Free A B _ _ ψ.toAlgebra.toModule ∧
      ∃ (n : ℕ) (e : Fin n → B), ∀ g : B, ∃! c : Fin n → A, g = ∑ i, ψ (c i) * e i := by
  letI := ψ.toAlgebra
  have : Module.Finite A B := hψ
  have : IsLocalHom (algebraMap A B) := ‹_›
  have hf : Module.Flat A B := flat_of_isCM_of_quasiFinite (isCM_of_isRegularLocalRing B) hd
  have hfr : Module.Free A B := Module.free_of_flat_of_isLocalRing
  refine ⟨hf, FaithfulSMul.algebraMap_injective A B, hfr, _, Module.finBasis A B, fun g => ?_⟩
  refine ⟨(Module.finBasis A B).equivFun g, ?_, fun c hc => ?_⟩
  · exact ((Module.finBasis A B).sum_equivFun g).symm
  · rw [eq_comm, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, hc]
    rfl

theorem flat_injective_basis_of_finiteReduction (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) (h : FiniteReduction fun j => φ (X j))
    (hc : Nat.card τ ≤ Nat.card σ) :
    φ.toRingHom.Flat ∧ Function.Injective φ ∧
      @Module.Free (MvPowerSeries τ R) (MvPowerSeries σ R) _ _ φ.toRingHom.toAlgebra.toModule ∧
      ∃ (n : ℕ) (e : Fin n → MvPowerSeries σ R),
        ∀ g, ∃! c : Fin n → MvPowerSeries τ R, g = ∑ i, φ (c i) * e i := by
  have := isRegularLocalRing_mvPowerSeries R σ
  have := isRegularLocalRing_mvPowerSeries R τ
  have := isLocalHom_of_constantCoeff_mem φ h0
  refine flat_injective_basis_of_finite φ.toRingHom (finite_of_finiteReduction φ h0 h) ?_
  rw [ringKrullDim_mvPowerSeries, ringKrullDim_mvPowerSeries]
  gcongr

end Free

section Solve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]

variable {R} [IsAdicComplete (maximalIdeal R) R] {σ τ : Type*} [Finite σ] [Finite τ]

end Solve

section FormalGroup

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

variable {R : Type} [CommRing R] {d : ℕ}

theorem constantCoeff_mulN (G : FGLaw R d) (k : ℕ) (i : Fin d) :
    constantCoeff (mulN G k i) = 0 := by
  induction k generalizing i with
  | zero => simp [mulN]
  | succ k ih =>
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![mulN G k, pt R d 0] : Fin 2 → Pt R 1 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt, ih]
    exact constantCoeff_subst_eq_zero (hasSubst_ev _ h) (fun p => h p.1 p.2) (G.const i)

theorem constantCoeff_vec_mulN (G : FGLaw R d) (k : ℕ) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![mulN G k] : Fin 1 → Pt R 1 d) j i) = 0 := by
  simp [constantCoeff_mulN]

def mulNHom (G : FGLaw R d) (k : ℕ) : PS R 1 d →ₐ[R] PS R 1 d :=
  substAlgHom (hasSubst_ev ![mulN G k] (constantCoeff_vec_mulN G k))

def mulLaw (R : Type) [CommRing R] (d : ℕ) : FGLaw R d where
  F := fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i) + X ((0 : Fin 2), i) * X ((1 : Fin 2), i)
  const := fun i => by simp
  unit := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    simp only [ev_add _ h, ev_mul _ h, ev_X _ h]
    simp [pt]
  comm := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    simp only [ev_add _ h, ev_mul _ h, ev_X _ h]
    simp [pt, add_comm, mul_comm]
  assoc := fun i => by
    have key : ∀ a b : Pt R 3 d, (∀ l, constantCoeff (a l) = 0) → (∀ l, constantCoeff (b l) = 0) →
        ∀ l, ev ![a, b] (X ((0 : Fin 2), l) + X ((1 : Fin 2), l) +
          X ((0 : Fin 2), l) * X ((1 : Fin 2), l) : PS R 2 d) = a l + b l + a l * b l := by
      intro a b ha hb l
      have h : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R 3 d) j l) = 0 := by
        intro j l; fin_cases j <;> simp [ha, hb]
      simp only [ev_add _ h, ev_mul _ h, ev_X _ h]
      simp
    have hp : ∀ (j : Fin 3) (l : Fin d), constantCoeff (pt R d j l) = 0 := by simp [pt]
    rw [funext (key _ _ (hp 0) (hp 1)), funext (key _ _ (hp 1) (hp 2)),
      key _ _ (by simp [hp]) (hp 2), key _ _ (hp 0) (by simp [hp])]
    ring

end FormalGroup

end GlobalTheory.FormalIsogeny
