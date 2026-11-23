import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnitsStatement

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.ConjSize

private theorem exists_pow_eq_span {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    ∃ (h : ℕ) (a : 𝓞 L), 0 < h ∧ a ≠ 0 ∧ v.asIdeal ^ h = Ideal.span {a} := by
  classical
  have hI : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 L)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have hpow : v.asIdeal ^ Fintype.card (ClassGroup (𝓞 L)) ∈ nonZeroDivisors (Ideal (𝓞 L)) :=
    pow_mem hI _
  have hone : ClassGroup.mk0 ⟨_, hpow⟩ = 1 := by
    have h1 := pow_card_eq_one (x := ClassGroup.mk0 ⟨v.asIdeal, hI⟩)
    rw [← map_pow] at h1
    convert h1
    simp
  obtain ⟨a, ha⟩ := ((ClassGroup.mk0_eq_one_iff hpow).1 hone).principal
  refine ⟨_, a, Fintype.card_pos, ?_, ha⟩
  rintro rfl
  apply nonZeroDivisors.ne_zero hpow
  rw [ha]
  simp

private theorem exists_global {L : Type} [Field L] [NumberField L] (χ : HChar L) (w : HeightOneSpectrum (𝓞 L)) :
    ∃ (k : Lˣ) (N : ℕ), 0 < N ∧ Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) ≠ 1 ∧
      (χ.inf k * χ.locK w k) ^ N = 1 := by
  classical
  obtain ⟨h, a, hh, ha0, hspan⟩ := exists_pow_eq_span w
  have haw : a ∈ w.asIdeal := by
    have hmem : a ∈ w.asIdeal ^ h := by
      rw [hspan]
      exact Ideal.mem_span_singleton_self a
    exact Ideal.pow_le_self hh.ne' hmem
  have hav : ∀ v : HeightOneSpectrum (𝓞 L), v ≠ w → a ∉ v.asIdeal := by
    intro v hvw hva
    apply hvw
    have hle : w.asIdeal ^ h ≤ v.asIdeal := by
      rw [hspan, Ideal.span_le, Set.singleton_subset_iff]
      exact hva
    have hwv := v.isPrime.le_of_pow_le hle
    exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv)).symm
  set k := GlobalTheory.Mem.ValAlg.uOf a ha0 with hk
  set S := (GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ).1.toFinset ∪ {w} with hS
  have hwS : w ∈ S := by simp [hS]
  choose Nf hNf hNa using fun v => GlobalTheory.Mem.ValAlg.locK_pow χ v
  refine ⟨k, ∏ v ∈ S.erase w, Nf v, Finset.prod_pos (fun v _ => hNf v), ?_, ?_⟩
  · have hval : Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        w.intValuation a := by
      change Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L a)) = _
      rw [← IsScalarTower.algebraMap_apply (𝓞 L) L]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation w a).trans
        (HeightOneSpectrum.valuation_of_algebraMap w a)
    rw [hval]
    exact ((HeightOneSpectrum.intValuation_lt_one_iff_mem w a).2 haw).ne
  · have hrule := GlobalTheory.HeckeProduct.hchar_productRule L χ S (by
      intro v hv
      by_contra hc
      exact hv (by simp [hS, hc])) k
    have hfin : ∏ᶠ (v) (_ : v ∉ S), χ.val v ^ ordF v k = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro v
      rw [finprod_eq_if]
      split_ifs with hv
      · rfl
      · have hvw : v ≠ w := fun e => hv (by simp [hS, e])
        have h0 : ordF v k = 0 := by
          simp [Formalism.L2.Host.ordF, hk, GlobalTheory.Mem.ValAlg.uOf, HeightOneSpectrum.valuation_of_algebraMap,
            HeightOneSpectrum.intValuation_eq_one_iff.2 (hav v hvw)]
        rw [h0, zpow_zero]
    rw [hfin, mul_one, ← Finset.mul_prod_erase S (fun v => χ.locK v k) hwS, ← mul_assoc] at hrule
    have hrest : (∏ v ∈ S.erase w, χ.locK v k) ^ (∏ v ∈ S.erase w, Nf v) = 1 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro v hv
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nf hv
      rw [hc, pow_mul, hNa v a ha0 (hav v (Finset.ne_of_mem_erase hv)), one_pow]
    have hpow := congrArg (fun z => z ^ (∏ v ∈ S.erase w, Nf v)) hrule
    rw [mul_pow, hrest, mul_one, one_pow] at hpow
    exact hpow

private theorem exists_pow_inf {L : Type} [Field L] [NumberField L] (χ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (x : (w.adicCompletion L)ˣ) : ∃ (b : Lˣ) (M : ℕ), 0 < M ∧ χ.loc w x ^ M * χ.inf b = 1 := by
  obtain ⟨k, N, hN, hk1, hkN⟩ := exists_global χ w
  set y := atFin w k with hy
  have hx0 : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  have hy0 : Valued.v (y : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  obtain ⟨p, hp⟩ : ∃ p : ℤ, Valued.v (x : w.adicCompletion L) = WithZero.exp p :=
    ⟨_, (WithZero.exp_log hx0).symm⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, Valued.v (y : w.adicCompletion L) = WithZero.exp q :=
    ⟨_, (WithZero.exp_log hy0).symm⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hk1 (by rw [hq, WithZero.exp_zero])
  have hunit : IsUnitAt w (x ^ q * y ^ (-p)) := by
    show Valued.v ((x ^ q * y ^ (-p) : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀,
      map_zpow₀, hp, hq, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      WithZero.exp_eq_one, smul_eq_mul, smul_eq_mul]
    ring
  obtain ⟨m, hm, hmx⟩ := GlobalTheory.T.heckeChar_loc_pow_eq_one_on_localUnits L χ w _ hunit
  have hinf : (χ.locK w k) ^ N = (χ.inf k ^ N)⁻¹ := by
    rw [mul_pow] at hkN
    exact eq_inv_of_mul_eq_one_right hkN
  have key : (χ.loc w x) ^ (q * m * N) * χ.inf (k ^ (p * m * N)) = 1 := by
    rw [map_mul, map_zpow, map_zpow] at hmx
    have hly : χ.loc w y = χ.locK w k := rfl
    rw [hly] at hmx
    rw [map_zpow]
    have hY : (χ.locK w k) ^ (-(p * m * N)) = (χ.inf k) ^ (p * m * N) := by
      rw [show -(p * (m : ℤ) * N) = (N : ℤ) * (-(p * m)) by ring, zpow_mul, zpow_natCast, hinf,
        inv_zpow', neg_neg, ← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [← hY]
    have hmN := congrArg (fun z => z ^ N) hmx
    simp only [one_pow] at hmN
    rw [← hmN, ← pow_mul, ← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul]
    congr 2 <;> push_cast <;> ring
  have hQ : q * m * N ≠ 0 := by positivity
  rcases Int.natAbs_eq (q * m * N) with h | h
  · refine ⟨k ^ (p * m * N), (q * m * N).natAbs, Int.natAbs_pos.2 hQ, ?_⟩
    rw [← zpow_natCast, ← h]
    exact key
  · refine ⟨(k ^ (p * m * N))⁻¹, (q * m * N).natAbs, Int.natAbs_pos.2 hQ, ?_⟩
    rw [h, zpow_neg, zpow_natCast] at key
    rw [map_inv, ← inv_mul_eq_one.1 key, mul_inv_cancel]

private theorem exists_qbar_embedding_lift {K : Type} [Field K] [NumberField K] (ι τ : K →+* ℂ) (y : K) :
    ∃ ψ : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ, ∃ hy : ι y ∈ Formalism.MainNotions.TaylorLogMetric.Qbar, ψ ⟨ι y, hy⟩ = τ y := by
  have hjmem : ∀ t : K, ι t ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun t =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) t).algHom ι.toRatAlgHom)
  haveI hQ : Algebra.IsAlgebraic ℚ Formalism.MainNotions.TaylorLogMetric.Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  let j : K →+* Formalism.MainNotions.TaylorLogMetric.Qbar := ι.codRestrict Formalism.MainNotions.TaylorLogMetric.Qbar hjmem
  letI : Algebra K Formalism.MainNotions.TaylorLogMetric.Qbar := j.toAlgebra
  letI : Algebra K ℂ := τ.toAlgebra
  haveI : IsScalarTower ℚ K Formalism.MainNotions.TaylorLogMetric.Qbar := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun f : ℚ →+* Formalism.MainNotions.TaylorLogMetric.Qbar => f r)
      (Subsingleton.elim (algebraMap ℚ Formalism.MainNotions.TaylorLogMetric.Qbar)
        ((algebraMap K Formalism.MainNotions.TaylorLogMetric.Qbar).comp (algebraMap ℚ K)))
  haveI : Algebra.IsAlgebraic K Formalism.MainNotions.TaylorLogMetric.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  refine ⟨(IsAlgClosed.lift : Formalism.MainNotions.TaylorLogMetric.Qbar →ₐ[K] ℂ).toRingHom, hjmem y, ?_⟩
  exact (IsAlgClosed.lift : Formalism.MainNotions.TaylorLogMetric.Qbar →ₐ[K] ℂ).commutes y

theorem UpperTheory.conjSize_heckeChar_local_of_mem_range_embedding :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → ∀ {K : Type} [Field K] [NumberField K] (ι τ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ), ((χ.loc w x : ℂˣ) : ℂ) ∈ Set.range ι → GlobalTheory.ConjSize.Un ι τ ((χ.loc w x : ℂˣ) : ℂ) := by
  intro L _ _ _ χ I _ φ n hχ K _ _ ι τ w x hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨b, M, hM, hb⟩ := exists_pow_inf χ w x
  have hz : ((χ.loc w x : ℂˣ) : ℂ) ^ M * ∏ i, ((φ i) (b : L) / (‖(φ i) (b : L)‖ : ℂ)) ^ n i = 1 := by
    rw [← hχ b]
    have h1 := congrArg (fun u : ℂˣ => (u : ℂ)) hb
    simpa using h1
  obtain ⟨hzQ, hψ⟩ := GlobalTheory.HeckeVal.root_value φ n b _ M hM hz
  obtain ⟨ψ, hyQ, hψy⟩ := exists_qbar_embedding_lift ι τ y
  refine ⟨y, hy, ?_⟩
  have heq : (⟨_, hzQ⟩ : Formalism.MainNotions.TaylorLogMetric.Qbar) = ⟨ι y, hyQ⟩ := Subtype.ext hy.symm
  rw [← hψy, ← heq]
  apply hψ ℂ ψ
  intro σ
  rw [← RingHom.comp_apply ψ σ, ← RingHom.comp_apply ψ σ, IsCMField.complexEmbedding_complexConj]
  simp
