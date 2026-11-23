import Mathlib
import Formalism.PeriodIntegrals.LocGlobIncl

open NumberField IsDedekindDomain

noncomputable section

namespace PI.LocGlobInclWork

variable {K : Type} [Field K] [NumberField K]

theorem mem_localization_iff {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem self_le_locP {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (p : Ideal (𝓞 K)) [p.IsPrime]
    (L : Submodule (𝓞 K) W) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L :=
  fun x hx => (mem_localization_iff p L x).mpr ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hx⟩

theorem maximal_ne_bot (m : Ideal (𝓞 K)) (hm : m.IsMaximal) : m ≠ ⊥ := by
  haveI := hm
  exact (Ideal.bot_lt_of_maximal m (NumberField.RingOfIntegers.not_isField K)).ne'

theorem mem_of_local {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (N : Submodule (𝓞 K) W) (x : W)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 K) W x) ≠ ⊤ := by
    intro htop
    apply hx
    have h1 : (1 : 𝓞 K) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 K) W x) := by
      rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, maximal_ne_bot m hm⟩
  apply hs
  apply hle
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  exact hsx

theorem coe_pow_toNat_le (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    ((v.asIdeal ^ k.toNat : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ k := by
  rw [FractionalIdeal.coeIdeal_pow]
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp
  · push_neg at hk
    obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hk.le
    have h0 : (-(n : ℤ)).toNat = 0 := Int.toNat_of_nonpos hk.le
    rw [h0, pow_zero, zpow_neg, zpow_natCast]
    have h1 : (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n ≤ 1 := by
      rw [← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
    have h2 : (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n ≠ 0 :=
      pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1⁻¹ := inv_one.symm
      _ ≤ ((v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n)⁻¹ := FractionalIdeal.inv_anti_mono h2 one_ne_zero h1

theorem coe_prod_le (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    ((∏ v ∈ S, v.asIdeal ^ (n v).toNat : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv, FractionalIdeal.coeIdeal_mul]
    rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
    have h1 := FractionalIdeal.coe_le_coe.mpr (coe_pow_toNat_le v (n v))
    have h2 := FractionalIdeal.coe_le_coe.mpr ih
    first
      | exact mul_le_mul' h1 h2
      | exact Submodule.mul_le_mul' h1 h2
      | exact Submodule.mul_le_mul_of_le_of_le h1 h2

theorem exists_unit_at (w : HeightOneSpectrum (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hw : w ∉ S) (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧
      algebraMap (𝓞 K) K t ∈ ∏ v ∈ S, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n v := by
  classical
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hP : ¬ (∏ v ∈ S, v.asIdeal ^ (n v).toNat) ≤ w.asIdeal := by
    intro hle
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      rw [Finset.prod_empty, Ideal.one_eq_top] at hle
      exact w.isPrime.ne_top (top_le_iff.mp hle)
    · obtain ⟨v, hv, hvle⟩ := (Ideal.IsPrime.prod_le w.isPrime).mp hle
      have h1 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le hvle
      have h2 : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top h1
      have h3 : v = w := IsDedekindDomain.HeightOneSpectrum.ext h2
      exact hw (h3 ▸ hv)
  obtain ⟨t, htP, htw⟩ := SetLike.not_le_iff_exists.mp hP
  refine ⟨t, htw, ?_⟩
  exact coe_prod_le S n ((FractionalIdeal.mem_coeIdeal _).mpr ⟨t, htP, rfl⟩)

variable [StarRing K] {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
  [IsScalarTower (𝓞 K) K W]

theorem smul_mem_idealSmul (I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (B : Submodule (𝓞 K) W) (t : 𝓞 K) (ht : algebraMap (𝓞 K) K t ∈ J) {y : W}
    (hy : y ∈ Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) B) :
    t • y ∈ Formalism.HermitianLatticesTheory.idealSmul ((I * J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
      Submodule (𝓞 K) K) B := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, b, hb, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨c * algebraMap (𝓞 K) K t, FractionalIdeal.mul_mem_mul hc ht, b, hb, ?_⟩
    rw [← smul_assoc, Algebra.smul_def, mul_comm]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy

theorem main : PI.LocGlobIncl := by
  intro K W _ _ _ _ _ _ _ M B T a hT hnT x hx
  classical
  unfold Formalism.AtG.denIdeal
  apply mem_of_local
  intro w
  haveI : w.asIdeal.IsPrime := w.isPrime
  by_cases hw : w ∈ T
  · obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w.asIdeal _ x).mp (hT w hw ((self_le_locP w.asIdeal M) hx))
    obtain ⟨t, ht, htJ⟩ := exists_unit_at w (T.erase w) (by simp) (fun v => -(a v))
    have htJ' : algebraMap (𝓞 K) K t ∈
        ∏ v ∈ T.erase w, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) := htJ
    refine ⟨t * s, fun hmem => (w.isPrime.mem_or_mem hmem).elim ht hs, ?_⟩
    rw [mul_smul]
    have e : (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a w)) *
        ∏ v ∈ T.erase w, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) =
        ∏ v ∈ T, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) :=
      Finset.mul_prod_erase T (fun v => (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v))) hw
    have hm := smul_mem_idealSmul _ _ B t htJ' hsx
    rw [e] at hm
    exact hm
  · obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w.asIdeal _ x).mp (hnT w hw ((self_le_locP w.asIdeal M) hx))
    obtain ⟨t, ht, htJ⟩ := exists_unit_at w T hw (fun v => -(a v))
    have htJ' : algebraMap (𝓞 K) K t ∈
        ∏ v ∈ T, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a v)) := htJ
    refine ⟨t * s, fun hmem => (w.isPrime.mem_or_mem hmem).elim ht hs, ?_⟩
    rw [mul_smul]
    have hB : s • x ∈ Formalism.HermitianLatticesTheory.idealSmul
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) B := by
      apply Submodule.subset_span
      refine ⟨1, ?_, s • x, hsx, (one_smul K _).symm⟩
      rw [FractionalIdeal.coe_one]
      exact Submodule.one_le.mp le_rfl
    have hm := smul_mem_idealSmul 1 _ B t htJ' hB
    rw [one_mul] at hm
    exact hm

end PI.LocGlobInclWork
