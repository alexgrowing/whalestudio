import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.SecondCountableOfOpenSubgroups

noncomputable section

namespace PI.IwaMeasEx.AfT

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct
open Formalism.MainNotions.S

section Fin

variable (F : Type) [Field F] [NumberField F]

theorem natCast_apply (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (N : Af F) v = (N : v.adicCompletion F) := by
  rw [← map_natCast (algebraMap F (Af F)) N, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap F (v.adicCompletion F)) N

theorem natCast_mul_apply (N : ℕ) (z : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : Af F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply]
  rfl

theorem norm_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e : (c : v.adicCompletion F) = (((algebraMap (𝓞 F) F (c : 𝓞 F)) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    rw [show (((c : F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (c : F) from rfl,
      map_natCast]
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hval

theorem mem_int_of_norm_le_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (h : ‖x‖ ≤ 1) :
    x ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((Valued.toNormedField.norm_le_one_iff).1 h)

theorem norm_le_one_of_mem_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h)

theorem exists_nat_mul_intAd (x : Af F) : ∃ N : ℕ, 1 ≤ N ∧ (N : Af F) * x ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ x v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 x.2
  set S := hfin.toFinset with hS
  set c : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ S, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one F v c (Finset.dvd_prod_of_mem _ hv)
  have hev : ∀ v ∈ S, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k * ‖x v‖ < 1 := by
    intro v hv
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).mul_const ‖x v‖
    rw [zero_mul] at ht
    exact ht.eventually (Iio_mem_nhds one_pos)
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finset S).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun v => ?_⟩
  show ((((c ^ k : ℕ)) : Af F) * x) v ∈ v.adicCompletionIntegers F
  rw [natCast_mul_apply]
  by_cases hv : v ∈ S
  · apply mem_int_of_norm_le_one
    rw [norm_mul, Nat.cast_pow, norm_pow]
    exact (hk v hv).le
  · have hxv : x v ∈ v.adicCompletionIntegers F := by
      rw [hS, Set.Finite.mem_toFinset] at hv
      simpa using hv
    exact mul_mem (natCast_mem _ _) hxv

theorem eq_zero_of_forall_mem (x : Af F)
    (h : ∀ N : ℕ, 1 ≤ N → ∃ z ∈ Formalism.UG.intAd F, x = (N : Af F) * z) : x = 0 := by
  ext v
  suffices key : x v = 0 by rw [key]; rfl
  set p : ℕ := Ideal.absNorm v.asIdeal
  have hp1 : 1 ≤ p := (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hp : ‖(p : v.adicCompletion F)‖ < 1 := norm_natCast_lt_one F v p dvd_rfl
  have hle : ∀ k : ℕ, ‖x v‖ ≤ ‖(p : v.adicCompletion F)‖ ^ k := by
    intro k
    obtain ⟨z, hz, hxz⟩ := h (p ^ k) (Nat.one_le_pow _ _ hp1)
    have e : x v = ((p ^ k : ℕ) : v.adicCompletion F) * z v := by
      rw [hxz, natCast_mul_apply]
    rw [e, norm_mul, Nat.cast_pow, norm_pow]
    calc ‖(p : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(p : v.adicCompletion F)‖ ^ k * 1 :=
          mul_le_mul_of_nonneg_left (norm_le_one_of_mem_int F v _ (hz v)) (pow_nonneg (norm_nonneg _) _)
      _ = _ := mul_one _
  have h0 : ‖x v‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp) hle
  exact norm_le_zero_iff.1 h0

end Fin

theorem exists_nat_den {E : Type} [Field E] [NumberField E] (s : Finset E) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ x ∈ s, (d : E) * x ∈ Formalism.UG.intOE E := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun x hx => ?_⟩
  have hi : IsIntegral ℤ ((y.natAbs : E) * x) := by
    have hyx := h x hx
    rw [zsmul_eq_mul] at hyx
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice y with h' | h'
    · rw [h']; exact hyx
    · rw [h', Int.cast_neg, neg_mul]; exact hyx.neg
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hi
  exact ⟨a, ha⟩

variable (I : AutInst)

abbrev AEf : Type := I.E ⊗[I.F] Af I.F

theorem inclE_mem_IntAf {x : I.E} (hx : x ∈ Formalism.UG.intOE I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) x ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem includeRight_mem_IntAf {a : Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) :
    (Algebra.TensorProduct.includeRight a : AEf I) ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem tmul_eq (e : I.E) (a : Af I.F) :
    (e ⊗ₜ[I.F] a : AEf I) = Formalism.UG.inclE (F := I.F) (Af I.F) e * Algebra.TensorProduct.includeRight a := by
  simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]

theorem natCast_mul_mem {N : ℕ} {y : AEf I} (hy : y ∈ IntAf I.F I.E) : (N : AEf I) * y ∈ IntAf I.F I.E :=
  mul_mem (natCast_mem _ N) hy

theorem exists_nat_mul_mem (t : AEf I) : ∃ N : ℕ, 1 ≤ N ∧ (N : AEf I) * t ∈ IntAf I.F I.E := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, le_rfl, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨d, hd, hde⟩ := exists_nat_den (E := I.E) {e}
    obtain ⟨M, hM, hMa⟩ := exists_nat_mul_intAd I.F a
    refine ⟨d * M, Nat.mul_pos hd hM, ?_⟩
    have h1 := inclE_mem_IntAf I (hde e (Finset.mem_singleton_self e))
    have h2 := includeRight_mem_IntAf I hMa
    rw [map_mul, map_natCast] at h1
    rw [map_mul, map_natCast] at h2
    rw [tmul_eq]
    have e' : ((d * M : ℕ) : AEf I) * (Formalism.UG.inclE (F := I.F) (Af I.F) e * Algebra.TensorProduct.includeRight a) =
        ((d : AEf I) * Formalism.UG.inclE (F := I.F) (Af I.F) e) * ((M : AEf I) * Algebra.TensorProduct.includeRight a) := by
      push_cast; ring
    rw [e']
    exact mul_mem h1 h2
  | add s t hs ht =>
    obtain ⟨N1, h1, hs⟩ := hs
    obtain ⟨N2, h2, ht⟩ := ht
    refine ⟨N1 * N2, Nat.mul_pos h1 h2, ?_⟩
    have e' : ((N1 * N2 : ℕ) : AEf I) * (s + t) = (N2 : AEf I) * ((N1 : AEf I) * s) + (N1 : AEf I) * ((N2 : AEf I) * t) := by
      push_cast; ring
    rw [e']
    exact add_mem (natCast_mul_mem I hs) (natCast_mul_mem I ht)

def bsub (N : ℕ) : AddSubgroup (AEf I) :=
  (IntAf I.F I.E).toAddSubgroup.map (AddMonoidHom.mulLeft (N : AEf I))

theorem mem_bsub {N : ℕ} {x : AEf I} : x ∈ bsub I N ↔ ∃ z ∈ IntAf I.F I.E, (N : AEf I) * z = x := by
  simp [bsub]

theorem bsub_mul_le {N M : ℕ} (h : M ∣ N) : bsub I N ≤ bsub I M := by
  intro x hx
  obtain ⟨k, rfl⟩ := h
  obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hx
  refine (mem_bsub I).2 ⟨(k : AEf I) * z, natCast_mul_mem I hz, ?_⟩
  push_cast; ring

def bas (k : ℕ) : AddSubgroup (AEf I) := bsub I (k + 1)

theorem ringSubgroupsBasis_bas : RingSubgroupsBasis (bas I) := by
  refine RingSubgroupsBasis.of_comm (bas I) ?_ ?_ ?_
  · intro i j
    refine ⟨(i + 1) * (j + 1) - 1, le_inf ?_ ?_⟩
    · apply bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]
      exact dvd_mul_right _ _
    · apply bsub_mul_le; rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]
      exact dvd_mul_left _ _
  · intro i
    refine ⟨i, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hx
    obtain ⟨w, hw, rfl⟩ := (mem_bsub I).1 hy
    refine (mem_bsub I).2 ⟨z * (((i + 1 : ℕ) : AEf I) * w), mul_mem hz (natCast_mul_mem I hw), ?_⟩
    ring
  · intro x i
    obtain ⟨N, hN, hx⟩ := exists_nat_mul_mem I x
    refine ⟨(i + 1) * N - 1, ?_⟩
    intro y hy
    have hpos : 1 ≤ (i + 1) * N := Nat.mul_pos (Nat.succ_pos i) hN
    change y ∈ bsub I ((i + 1) * N - 1 + 1) at hy
    rw [Nat.sub_add_cancel hpos] at hy
    obtain ⟨z, hz, rfl⟩ := (mem_bsub I).1 hy
    show x * (((i + 1) * N : ℕ) * z) ∈ bsub I (i + 1)
    refine (mem_bsub I).2 ⟨((N : AEf I) * x) * z, mul_mem hx hz, ?_⟩
    push_cast; ring

@[instance_reducible] def tAf : TopologicalSpace (AEf I) := (ringSubgroupsBasis_bas I).topology

theorem hasBasis_nhds_zero_tAf :
    HasBasis (@nhds (AEf I) (tAf I) 0) (fun _ => True) fun k => (bas I k : Set (AEf I)) :=
  (ringSubgroupsBasis_bas I).hasBasis_nhds_zero

theorem hasBasis_nhds_tAf (a : AEf I) :
    HasBasis (@nhds (AEf I) (tAf I) a) (fun _ => True) fun k => {b | b - a ∈ bas I k} :=
  (ringSubgroupsBasis_bas I).hasBasis_nhds a

theorem isTopologicalRing_tAf : @IsTopologicalRing (AEf I) (tAf I) _ :=
  RingFilterBasis.isTopologicalRing _

section T2

variable {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E)

def crd (j : ι) : AEf I →ₗ[I.F] Af I.F :=
  (TensorProduct.lid I.F (Af I.F)).toLinearMap ∘ₗ (b.coord j).rTensor (Af I.F)

theorem crd_tmul (j : ι) (x : I.E) (a : Af I.F) : crd I b j (x ⊗ₜ[I.F] a) = b.repr x j • a := by
  simp [crd, Module.Basis.coord_apply]

theorem sum_crd (t : AEf I) : t = ∑ j, b j ⊗ₜ[I.F] crd I b j t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [crd_tmul, TensorProduct.tmul_smul]
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul']
  | add s t hs ht =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hs, ← ht]

theorem exists_denom : ∃ D : ℕ, 1 ≤ D ∧ ∀ o : 𝓞 I.E, ∀ j : ι,
    ∃ r : 𝓞 I.F, (D : I.F) * b.repr (o : I.E) j = algebraMap (𝓞 I.F) I.F r := by
  classical
  set eb := NumberField.RingOfIntegers.basis I.E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (_ × ι)).image (fun p => b.repr ((eb p.1 : 𝓞 I.E) : I.E) p.2))
  refine ⟨y.natAbs, Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hy0), ?_⟩
  have hint : ∀ c : I.F, IsIntegral ℤ (y • c) → IsIntegral ℤ ((y.natAbs : I.F) * c) := by
    intro c hc
    rcases Int.natAbs_eq y with h | h
    · have : ((y.natAbs : ℤ) : I.F) * c = y • c := by rw [← h, zsmul_eq_mul]
      rw [← Int.cast_natCast, this]
      exact hc
    · have : ((y.natAbs : ℤ) : I.F) * c = -(y • c) := by
        rw [zsmul_eq_mul]
        conv_rhs => rw [h]
        push_cast
        ring
      rw [← Int.cast_natCast, this]
      exact hc.neg
  have gen : ∀ i j, ∃ r : 𝓞 I.F,
      (y.natAbs : I.F) * b.repr ((eb i : 𝓞 I.E) : I.E) j = algebraMap (𝓞 I.F) I.F r := by
    intro i j
    have hm := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    exact ⟨⟨_, hint _ hm⟩, rfl⟩
  intro o
  have ho : o ∈ Submodule.span ℤ (Set.range eb) := by rw [eb.span_eq]; exact Submodule.mem_top
  induction ho using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact gen i
  | zero =>
    intro j
    exact ⟨0, by simp⟩
  | add x y' _ _ hx hy' =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    obtain ⟨r', hr'⟩ := hy' j
    refine ⟨r + r', ?_⟩
    rw [map_add, ← hr, ← hr']
    push_cast
    rw [map_add, Finsupp.add_apply, mul_add]
  | smul a x _ hx =>
    intro j
    obtain ⟨r, hr⟩ := hx j
    refine ⟨a • r, ?_⟩
    rw [map_zsmul, ← hr]
    have e : ((a • x : 𝓞 I.E) : I.E) = a • (x : I.E) := by push_cast; rfl
    rw [e, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, zsmul_eq_mul]
    ring

end T2

def sumsInt : AddSubgroup (AEf I) :=
  AddSubgroup.closure {x | ∃ o ∈ Formalism.UG.intOE I.E, ∃ a ∈ Formalism.UG.intAd I.F, x = o ⊗ₜ[I.F] a}

theorem sumsInt_mul {x y : AEf I} (hx : x ∈ sumsInt I) (hy : y ∈ sumsInt I) : x * y ∈ sumsInt I := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨o, ho, a, ha, rfl⟩ := hx
      obtain ⟨o', ho', a', ha', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, mul_mem ho ho', _, mul_mem ha ha', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | neg y _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | neg x _ h => rw [neg_mul]; exact neg_mem h

theorem IntAf_le_sumsInt {x : AEf I} (hx : x ∈ IntAf I.F I.E) : x ∈ sumsInt I := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨o, rfl⟩ | ⟨a, rfl⟩
    · exact AddSubgroup.subset_closure ⟨o, o.2, 1, one_mem _, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, one_mem _, a, a.2, rfl⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, rfl⟩
  | add x y _ _ h h' => exact add_mem h h'
  | neg x _ h => exact neg_mem h
  | mul x y _ _ h h' => exact sumsInt_mul I h h'

theorem algebraMap_mem_intAd (r : 𝓞 I.F) :
    algebraMap I.F (Af I.F) (algebraMap (𝓞 I.F) I.F r) ∈ Formalism.UG.intAd I.F := by
  intro v
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 I.F) I.F v r

theorem crd_mem {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E) {D : ℕ} (hD : ∀ o : 𝓞 I.E, ∀ j : ι,
    ∃ r : 𝓞 I.F, (D : I.F) * b.repr (o : I.E) j = algebraMap (𝓞 I.F) I.F r)
    {x : AEf I} (hx : x ∈ sumsInt I) (j : ι) :
    (D : Af I.F) * crd I b j x ∈ Formalism.UG.intAd I.F := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨o, ⟨o', rfl⟩, a, ha, rfl⟩ := hx
    obtain ⟨r, hr⟩ := hD o' j
    rw [crd_tmul, Algebra.smul_def, ← mul_assoc, ← map_natCast (algebraMap I.F _) D, ← map_mul]
    have e : (algebraMap (𝓞 I.E) I.E o') = (o' : I.E) := rfl
    rw [e, hr]
    exact mul_mem (algebraMap_mem_intAd I r) ha
  | zero => rw [map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ h h' => rw [map_add, mul_add]; exact add_mem h h'
  | neg x _ h => rw [map_neg, mul_neg]; exact neg_mem h

theorem eq_zero_of_forall_bsub (t : AEf I) (h : ∀ N : ℕ, 1 ≤ N → t ∈ bsub I N) : t = 0 := by
  classical
  let b := Module.finBasis I.F I.E
  obtain ⟨D, hD1, hD⟩ := exists_denom I b
  have hc : ∀ j, crd I b j t = 0 := by
    intro j
    apply eq_zero_of_forall_mem I.F
    intro N hN
    obtain ⟨s, hs, hst⟩ := (mem_bsub I).1 (h (N * D) (Nat.mul_pos hN hD1))
    refine ⟨(D : Af I.F) * crd I b j s, crd_mem I b hD (IntAf_le_sumsInt I hs) j, ?_⟩
    rw [← hst, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    push_cast
    ring
  rw [sum_crd I b t]
  simp [hc]

theorem t2Space_finite_adeles_ext : @T2Space (AEf I) (tAf I) := by
  letI := tAf I
  haveI := isTopologicalRing_tAf I
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  by_contra hcon
  push_neg at hcon
  apply hx
  apply eq_zero_of_forall_bsub I x
  intro N hN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  exact hcon _ ((hasBasis_nhds_zero_tAf I).mem_of_mem trivial)

theorem isUnit_natCast (c : ℕ) (hc : 1 ≤ c) : IsUnit (c : AEf I) := by
  have h0 : (c : I.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have := h0.isUnit.map (algebraMap I.F (AEf I))
  rwa [map_natCast] at this

end PI.IwaMeasEx.AfT
