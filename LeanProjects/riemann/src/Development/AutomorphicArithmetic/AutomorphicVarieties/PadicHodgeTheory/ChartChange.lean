import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanX
open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing MvPowerSeries

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : ∃ g : σ → MvPowerSeries σ O, f = ∑ i, MvPowerSeries.X i * g i :=
  _root_.UpperTheory.Reformulated.B.MemSpanMonomial.mem_span_X f hf

private theorem mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem lin_part {E : Type} [Field E] {n : ℕ} (f : MvPowerSeries (Fin n) E)
    (hf : constantCoeff f = 0) :
    f - ∑ j, coeff (Finsupp.single j 1) f • (X j : MvPowerSeries (Fin n) E) ∈ maximalIdeal _ ^ 2 := by
  obtain ⟨g, hg⟩ := mem_span_X f hf
  have hc : ∀ j, coeff (Finsupp.single j 1) f = constantCoeff (g j) := by
    intro j
    rw [hg, map_sum, Finset.sum_eq_single j]
    · rw [MvPowerSeries.X, coeff_monomial_mul, if_pos le_rfl, one_mul, tsub_self,
        coeff_zero_eq_constantCoeff_apply]
    · intro i _ hij
      rw [MvPowerSeries.X, coeff_monomial_mul, if_neg]
      intro h
      have := h i
      simp [Finsupp.single_apply, hij.symm] at this
    · simp
  simp only [hc]
  rw [hg, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [smul_eq_C_mul, mul_comm (C _), ← mul_sub, pow_two]
  exact Ideal.mul_mem_mul ((mem_max _).2 (by simp)) ((mem_max _).2 (by simp))

private theorem inj_of_surj {A : Type} [CommRing A] [IsNoetherianRing A] (s : A →+* A)
    (hs : Function.Surjective s) : Function.Injective s := by
  let K : ℕ →o Ideal A := ⟨fun k => RingHom.ker (s ^ k), monotone_nat_of_le_succ fun k a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ha, map_zero]⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstance : IsNoetherian A A) K
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hsN : Function.Surjective (s ^ N) := by
    rw [RingHom.coe_pow]; exact hs.iterate N
  obtain ⟨b, rfl⟩ := hsN a
  have h1 : b ∈ K (N + 1) := by
    show (s ^ (N + 1)) b = 0
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ha]
  rw [← hN (N + 1) (Nat.le_succ N)] at h1
  exact h1

private theorem exists_equiv {E : Type} [Field E] {n : ℕ} (y : Fin n → MvPowerSeries (Fin n) E)
    (hy : ∀ i, constantCoeff (y i) = 0)
    (hsp : Submodule.span E (Set.range fun i j : Fin n => coeff (Finsupp.single j 1) (y i)) = ⊤) :
    ∃ s : MvPowerSeries (Fin n) E ≃ₐ[E] MvPowerSeries (Fin n) E, ∀ i, s (X i) = y i := by
  haveI : IsAdicComplete (maximalIdeal E) E := by
    rw [maximalIdeal_eq_bot]; infer_instance
  haveI := co_mvps E E (Fin n)
  obtain ⟨s, ⟨-, hs⟩, -⟩ := co_ev E E (MvPowerSeries (Fin n) E) (Fin n) (Algebra.ofId E _) y
    fun i => (mem_max _).2 (hy i)
  have hsurj : Function.Surjective s := by
    refine co_surj E _ _ s fun f hf => ?_
    set J := (maximalIdeal (MvPowerSeries (Fin n) E)).map s ⊔ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2
    have hT : ∀ v : Fin n → E, ∑ j, v j • (X j : MvPowerSeries (Fin n) E) ∈ J := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range fun i j : Fin n => coeff (Finsupp.single j 1) (y i)) := by
        rw [hsp]; trivial
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        have h1 : y i ∈ J := Ideal.mem_sup_left (by
          rw [← hs]; exact Ideal.mem_map_of_mem s ((mem_max _).2 (by simp)))
        have h2 := Ideal.mem_sup_right (S := (maximalIdeal (MvPowerSeries (Fin n) E)).map s) (lin_part (y i) (hy i))
        simpa using J.sub_mem h1 h2
      | zero => simp
      | add a b _ _ ha hb =>
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        exact J.add_mem ha hb
      | smul c a _ ha =>
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
        rw [smul_eq_C_mul]
        exact J.mul_mem_left _ ha
    have h2 := Ideal.mem_sup_right (S := (maximalIdeal (MvPowerSeries (Fin n) E)).map s)
      (lin_part f ((mem_max _).1 hf))
    simpa using J.add_mem h2 (hT fun j => coeff (Finsupp.single j 1) f)
  exact ⟨AlgEquiv.ofBijective s ⟨inj_of_surj s.toRingHom hsurj, hsurj⟩, hs⟩

private theorem const_equiv {E σ : Type} [Field E] (s : MvPowerSeries σ E ≃ₐ[E] MvPowerSeries σ E)
    (f : MvPowerSeries σ E) : constantCoeff (s f) = constantCoeff f := by
  have h1 : f - algebraMap E _ (constantCoeff f) ∈ maximalIdeal _ :=
    (mem_max _).2 (by simp [MvPowerSeries.algebraMap_apply])
  have h2 : s (f - algebraMap E _ (constantCoeff f)) ∈ maximalIdeal _ := fun h => h1 (by
    simpa using h.map s.symm)
  rw [mem_max, map_sub, AlgEquiv.commutes] at h2
  simpa [MvPowerSeries.algebraMap_apply, sub_eq_zero] using h2

private theorem pow_equiv {E σ : Type} [Field E] (s : MvPowerSeries σ E ≃ₐ[E] MvPowerSeries σ E) (N : ℕ)
    {f : MvPowerSeries σ E} (hf : f ∈ maximalIdeal _ ^ N) : s f ∈ maximalIdeal _ ^ N := by
  have h : maximalIdeal (MvPowerSeries σ E) ≤ (maximalIdeal _).comap s := fun a ha => by
    rw [Ideal.mem_comap, mem_max, const_equiv]; exact (mem_max _).1 ha
  exact ((Ideal.pow_right_mono h N).trans (Ideal.le_comap_pow _ N)) hf

theorem UpperTheory.V.Loc.chartChange :
    ∀ {O R E : Type} [CommRing O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (z : Fin n → R), UpperTheory.V.Loc.IsCompl I x φ → (∀ i, x (z i) = 0) → Submodule.span E (Set.range fun i j : Fin n => MvPowerSeries.coeff (Finsupp.single j 1) (φ (z i))) = ⊤ → ∃ φ' : R →ₐ[O] MvPowerSeries (Fin n) E, UpperTheory.V.Loc.IsCompl I x φ' ∧ ∀ i, φ' (z i) = MvPowerSeries.X i := by
  intro O R E _ _ _ _ _ n I x φ z h hz hsp
  obtain ⟨s, hs⟩ := exists_equiv (fun i => φ (z i)) (fun i => by rw [h.const, hz, map_zero]) hsp
  let φ' : R →ₐ[O] MvPowerSeries (Fin n) E := ((s.symm.restrictScalars O).toAlgHom).comp φ
  have hφ : ∀ a, φ' a = s.symm (φ a) := fun _ => rfl
  refine ⟨φ', ⟨?_, fun a => ?_, fun N f => ?_, fun N a ha => ?_⟩, fun i => ?_⟩
  · rw [← h.ker]
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker, hφ, map_eq_zero_iff _ s.symm.injective]
  · rw [hφ, const_equiv, h.const]
  · obtain ⟨a, c, hc, hm⟩ := h.dense N (s f)
    refine ⟨a, c, hc, ?_⟩
    have h1 := pow_equiv s.symm N hm
    have h2 : s.symm (c • s f) = c • f := by
      rw [← algebraMap_smul E c, map_smul, AlgEquiv.symm_apply_apply, algebraMap_smul]
    rwa [map_sub, h2] at h1
  · refine h.inj N a ?_
    have h1 := pow_equiv s N ha
    rwa [hφ, AlgEquiv.apply_symm_apply] at h1
  · rw [hφ, ← hs, AlgEquiv.symm_apply_apply]
