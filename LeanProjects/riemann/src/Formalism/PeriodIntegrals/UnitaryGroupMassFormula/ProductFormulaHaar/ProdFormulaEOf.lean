import Mathlib
import Formalism.PeriodIntegrals.ProdFormulaE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.BasisEApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.DenEqOneOfForallPadicNormLeOne

noncomputable section

open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem modF_nonneg {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] (a : K) : 0 ≤ modF K a := by
  by_cases h : a = 0
  · rw [h, modF_zero]
  · exact (modF_pos h).le

theorem modK_eq (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p) (M : Model L.Fp L.Ep) (hM : M.OK)
    {x : E} (hx : x ≠ 0) :
    M.modK (L.ιE x) = FinitePlace.mk p (Algebra.norm F x) := by
  haveI := L.lf
  haveI := hM.borel
  haveI := hM.haar.haar
  haveI := L.free
  haveI := Base.finite L
  haveI := L.top
  unfold Model.modK
  rw [hH L.Fp L.Ep M.mu (L.ιE x) (Base.isUnit_ιE L hx) _, hM.haar.volR, mul_one,
    ENNReal.toReal_ofReal (modF_nonneg _), Base.norm_ιE L h2, hN F p L.Fp L.ιF L.dense L.val]

theorem clause1 (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)
    (M : ∀ p, Model (L p).Fp (L p).Ep) (hM : ∀ p, (M p).OK) (x : E) (hx : x ≠ 0) :
    (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
  have hz : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
  have he : (fun p => (M p).modK ((L p).ιE x)) =
      (fun w : FinitePlace F => w (Algebra.norm F x)) ∘ FinitePlace.equivHeightOneSpectrum.symm := by
    funext p
    rw [modK_eq hH hN h2 (L p) (M p) (hM p) hx]
    rfl
  rw [he]
  refine ⟨?_, ?_⟩
  · rw [Function.mulSupport_comp_eq_preimage]
    exact (FinitePlace.hasFiniteMulSupport hz).preimage
      (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)
  · rw [Function.comp_def, finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace F => w (Algebra.norm F x)),
      FinitePlace.prod_eq_inv_abs_norm hz, Algebra.norm_norm, Rat.cast_inv, Rat.cast_abs]

theorem fibFin (hR : St.ResCharIff) {q : ℕ} (hq : q.Prime) :
    {p : HeightOneSpectrum (𝓞 F) | resChar p = q}.Finite := by
  have hne : Ideal.span {(q : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  refine (Ideal.finite_factors hne).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  exact (hR F p q hq).1 hp

theorem transport {K : Type} [Field K] [TopologicalSpace K] {m : ℕ} (ℓ : ℕ) (h : m = ℓ)
    [Fact m.Prime] [Fact ℓ.Prime] [Algebra ℚ_[m] K] (hc : Continuous (algebraMap ℚ_[m] K))
    (hf : FiniteDimensional ℚ_[m] K) :
    ∃ A : Algebra ℚ_[ℓ] K, Continuous (@algebraMap ℚ_[ℓ] K _ _ A) ∧
      @FiniteDimensional ℚ_[ℓ] K _ _ A.toModule ∧
      ∀ (w : K) (a : ℚ), ‖@Algebra.trace ℚ_[ℓ] K _ _ A w - (a : ℚ_[ℓ])‖ =
        ‖Algebra.trace ℚ_[m] K w - (a : ℚ_[m])‖ := by
  subst h
  exact ⟨inferInstance, hc, hf, fun _ _ => rfl⟩

theorem transport_at (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (q : ℕ) [Fact q.Prime]
    (i : {p : HeightOneSpectrum (𝓞 F) // resChar p = q}) :
    ∃ A : Algebra ℚ_[q] (L i.1).Fp, Continuous (@algebraMap ℚ_[q] (L i.1).Fp _ _ A) ∧
      @FiniteDimensional ℚ_[q] (L i.1).Fp _ _ A.toModule ∧
      ∀ (w : (L i.1).Fp) (a : ℚ), ‖@Algebra.trace ℚ_[q] (L i.1).Fp _ _ A w - (a : ℚ_[q])‖ =
        (haveI := (L i.1).ellPrime
         ‖Algebra.trace ℚ_[resChar i.1] (L i.1).Fp w - (a : ℚ_[resChar i.1])‖) :=
  haveI := (L i.1).ellPrime
  transport q i.2 (L i.1).qlCont (L i.1).qlFin

def fam (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (q : ℕ) [Fact q.Prime] :
    Tr.LocFam F q {p : HeightOneSpectrum (𝓞 F) // resChar p = q} where
  P i := i.1
  K i := (L i.1).Fp
  fld _ := inferInstance
  vr _ := inferInstance
  top _ := inferInstance
  lf i := (L i.1).lf
  cz i := (L i.1).char0
  alg i := (transport_at L q i).choose
  cont i := (transport_at L q i).choose_spec.1
  fin i := (transport_at L q i).choose_spec.2.1
  ιF i := (L i.1).ιF
  dense i := (L i.1).dense
  val i := (L i.1).val

theorem fam_over (hR : St.ResCharIff) (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)
    (q : ℕ) [hq : Fact q.Prime] : (fam L q).Over := by
  refine ⟨Subtype.val_injective, fun p => ⟨?_, fun h => ⟨⟨p, (hR F p q hq.out).2 h⟩, rfl⟩⟩⟩
  rintro ⟨i, rfl⟩
  exact (hR F i.1 q hq.out).1 i.2

theorem clause2 (hT : Tr.TrSum) (hI : St.TrInt) (hR : St.ResCharIff) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (x : E) :
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (L p).psiE ((L p).ιE x) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by
  classical
  set z := Algebra.trace F E x with hzdef
  choose a ha hn he using fun p => Base.psiE_ιE (L p) h2 x
  have hfun : (fun p => (L p).psiE ((L p).ιE x)) =
      fun p => Complex.exp (2 * Real.pi * Complex.I * ((a p : ℚ) : ℂ)) := funext he
  rw [hfun]
  have hprime : ∀ p : HeightOneSpectrum (𝓞 F), (resChar p).Prime := fun p => (L p).ellPrime.out
  let fib : ℕ → Finset (HeightOneSpectrum (𝓞 F)) := fun q =>
    if hq : q.Prime then (fibFin hR hq).toFinset else ∅
  have hfib : ∀ p q, p ∈ fib q ↔ resChar p = q := by
    intro p q
    by_cases hq : q.Prime
    · simp only [fib, dif_pos hq, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    · simp only [fib, dif_neg hq, Finset.notMem_empty, false_iff]
      rintro rfl
      exact hq (hprime p)

  have hfin : {p | (a p).den ≠ 1}.Finite := by
    obtain ⟨d, hd0, hdint⟩ :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F |>.mpr (.of_finite ℚ z)).exists_integral_multiple
    have hne : Ideal.span {((d : ℤ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hd0
    refine (Ideal.finite_factors hne).subset fun p hp => ?_
    simp only [Set.mem_ofPred_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton]
    by_contra hdp
    apply hp
    haveI := (L p).ellPrime
    have hres : ((resChar p : ℕ) : 𝓞 F) ∈ p.asIdeal := (hR F p (resChar p) (hprime p)).1 rfl
    have hnd : ¬ ((resChar p : ℕ) : ℤ) ∣ d := by
      rintro ⟨k, hk⟩
      apply hdp
      rw [hk, Int.cast_mul]
      exact p.asIdeal.mul_mem_right _ (by exact_mod_cast hres)
    have hd1 : ‖(d : ℚ_[resChar p])‖ = 1 :=
      le_antisymm (Padic.norm_int_le_one d)
        (not_lt.1 fun h => hnd (Padic.norm_intCast_lt_one_iff.1 h))
    have hint : IsIntegral ℤ ((L p).ιF (d • z)) := hdint.map (L p).ιF.toIntAlgHom
    haveI := (L p).qlFin
    have hT1 := hI (resChar p) (L p).Fp ((L p).ιF (d • z)) hint
    have hsm : (L p).ιF (d • z) = algebraMap ℚ_[resChar p] (L p).Fp (d : ℚ_[resChar p]) *
        (L p).ιF z := by
      rw [zsmul_eq_mul, map_mul, map_intCast, map_intCast]
    rw [hsm, ← Algebra.smul_def, map_smul, smul_eq_mul, norm_mul, hd1,
      one_mul] at hT1
    obtain ⟨n, hn'⟩ := ha p
    exact Frac.den_eq_one_of_norm_le_one hn' hT1 (hn p)
  refine Frac.finprod_exp resChar hprime a ha fib hfib hfin _ fun q hq => ?_

  have hfs : Set.Finite {p : HeightOneSpectrum (𝓞 F) | resChar p = q} := fibFin hR hq.out
  haveI : Fintype {p : HeightOneSpectrum (𝓞 F) // resChar p = q} := hfs.fintype
  have hsum := hT F q _ (fam L q) (fam_over hR L q) z
  have htr : Algebra.trace ℚ F z = Algebra.trace ℚ E x := Algebra.trace_trace x
  rw [htr] at hsum
  have hsub : ∑ i ∈ fib q, (a i : ℚ_[q]) =
      ∑ i : {p : HeightOneSpectrum (𝓞 F) // resChar p = q}, (a i.1 : ℚ_[q]) :=
    Finset.sum_subtype _ (fun p => hfib p q) _
  rw [hsub, ← eq_ratCast (algebraMap ℚ ℚ_[q]), ← hsum]
  refine Frac.norm_sum_sub_sum_le_one _ _ _ fun i _ => ?_
  have h1 := (transport_at L q i).choose_spec.2.2 ((L i.1).ιF z) (a i.1)
  exact h1.trans_le (hn i.1)

theorem prodFormulaE_of (hH : St.HaarAlg) (hN : St.NormLoc) (hT : Tr.TrSum) (hI : St.TrInt)
    (hR : St.ResCharIff) : PI.ProdFormulaE.ProdFormulaE := by
  intro F E _ _ _ _ _ sig h2 L
  exact ⟨fun M hM x hx => clause1 hH hN h2 L M hM x hx, fun x => clause2 hT hI hR h2 L x⟩

end PI.ProdFormulaE.Top

end
