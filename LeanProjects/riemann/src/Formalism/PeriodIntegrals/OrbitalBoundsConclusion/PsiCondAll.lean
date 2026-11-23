import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

noncomputable section

open scoped TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.MainNotions.S

namespace PsiCondAllPf

section Fld

variable {F : Type} [Field F] [NumberField F]

theorem intAd_at {a : Af F} (h : a ∈ Formalism.UG.intAd F) (w : HeightOneSpectrum (𝓞 F)) :
    a w ∈ w.adicCompletionIntegers F := by
  have h' : ∀ w : HeightOneSpectrum (𝓞 F), a w ∈ w.adicCompletionIntegers F := h
  exact h' w

theorem exists_diff_not_mem (v : HeightOneSpectrum (𝓞 F)) (hun : Algebra.IsUnramifiedAt ℤ v.asIdeal) :
    ∃ d ∈ differentIdeal ℤ (𝓞 F), d ∉ v.asIdeal := by
  have h1 : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := (not_dvd_differentIdeal_iff).2 hun
  rw [Ideal.dvd_iff_le] at h1
  exact SetLike.not_le_iff_exists.1 h1

theorem mul_diff_int (y : F)
    (hy : ∀ z : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (y * algebraMap (𝓞 F) F z) = n)
    (d : 𝓞 F) (hd : d ∈ differentIdeal ℤ (𝓞 F)) :
    ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = y * algebraMap (𝓞 F) F d := by
  have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  have hyd : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := hy z
    exact ⟨n, by rw [Algebra.traceForm_apply, hn]; simp⟩
  have hdd : algebraMap (𝓞 F) F d ∈
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal ℤ ℚ F] at hdd
  have hm := FractionalIdeal.mul_mem_mul hyd hdd
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)] at hm
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  exact ⟨c, hc⟩

theorem unram_of (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal)
    (he : (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal = 1) : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
  have hmem : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 F) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq F hp]
    exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hmem.2
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(p : ℤ)}) (q := v.asIdeal)
    (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  exact (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ)).2 he

theorem approxF (a0 : Af F) : ∃ y : F, a0 - algebraMap F (Af F) y ∈ Formalism.UG.intAd F := by
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a0
  obtain ⟨β, y', hy', he⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma m hm
  refine ⟨(m : F)⁻¹ * algebraMap (𝓞 F) F β, ?_⟩
  have hmi : algebraMap F (Af F) ((m : F)⁻¹) * (m : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm.ne'), map_one]
  have hβ : algebraMap (𝓞 F) (Af F) β = algebraMap F (Af F) (algebraMap (𝓞 F) F β) := rfl
  have e : a0 - algebraMap F (Af F) ((m : F)⁻¹ * algebraMap (𝓞 F) F β) = y' := by
    rw [map_mul, ← hβ]
    linear_combination (algebraMap F (Af F) ((m : F)⁻¹)) * he - (a0 - y') * hmi
  rw [e]; exact hy'

end Fld

theorem approxE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (b : E ⊗[F] Af F) : ∃ x : E, b - Formalism.UG.inclE (F := F) (Af F) x ∈ IntAf F E := by
  obtain ⟨m, hm, hmb⟩ := PIW.AdelClassFin.dual_denominator F E b
  obtain ⟨a, r', hr', hr⟩ := PIW.AdelClassFin.dual_dense F E m hm _ hmb
  refine ⟨(m : E)⁻¹ * (a : E), ?_⟩
  have hmi : Formalism.UG.inclE (F := F) (Af F) ((m : E)⁻¹) * (m : E ⊗[F] Af F) = 1 := by
    rw [← map_natCast (Formalism.UG.inclE (F := F) (Af F)) m, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hm.ne'), map_one]
  have e : b - Formalism.UG.inclE (F := F) (Af F) ((m : E)⁻¹ * (a : E)) = r' := by
    rw [map_mul]
    linear_combination (Formalism.UG.inclE (F := F) (Af F) ((m : E)⁻¹)) * hr - (b - r') * hmi
  rw [e]; exact hr'

section Inst

variable (I : AutInst)

theorem tlin_eq (e : I.E) : Formalism.L2.SG.Pf.TypedLoc.tlin I e = PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed e :=
  (algebraMap I.F I.E).injective (by
    rw [Formalism.L2.SG.Pf.TypedLoc.tlin_spec, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply])

theorem tT_at (t : I.E ⊗[I.F] Af I.F) (w : HeightOneSpectrum (𝓞 I.F)) :
    (PI.ScPsiExists.UnitaryGroupMassFormula.tT (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed) t) w =
      Formalism.L2.SG.Pf.TypedLoc.trV I w (Formalism.UG.prV (E := I.E) w t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul e a =>
    have hp : Formalism.UG.prV (E := I.E) w (e ⊗ₜ[I.F] a) = e ⊗ₜ[I.F] (a w) := rfl
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.tT_tmul, hp, Formalism.L2.SG.Pf.TypedLoc.trV_tmul, Formalism.UG.P.afsplit_mul_apply,
      FiniteAdeleRing.algebraMap_apply, tlin_eq, Algebra.smul_def]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, Formalism.UG.P.afsplit_add_apply, hx, hy]

theorem tT_ew (ew : I.E ⊗[I.F] Af I.F) (v : HeightOneSpectrum (𝓞 I.F))
    (htr : Formalism.L2.SG.Pf.TypedLoc.trV I v (Formalism.UG.prV (E := I.E) v ew) = 1) (o : v.adicCompletion I.F) :
    PI.ScPsiExists.UnitaryGroupMassFormula.tT (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed)
      (ew * ((1 : I.E) ⊗ₜ[I.F] Formalism.UG.P.afsplitI v o)) = Formalism.UG.P.afsplitI v o := by
  ext w
  rw [tT_at, map_mul]
  have hp : Formalism.UG.prV (E := I.E) w ((1 : I.E) ⊗ₜ[I.F] Formalism.UG.P.afsplitI v o) =
      (1 : I.E) ⊗ₜ[I.F] (Formalism.UG.P.afsplitI v o w) := rfl
  rw [hp]
  by_cases h : w = v
  · subst h
    rw [Formalism.UG.P.afsplitI_self, mul_comm, Formalism.L2.SG.Pf.TypedLoc.trV_mul_tmul, htr, mul_one]
  · rw [Formalism.UG.P.afsplitI_ne v w h, TensorProduct.tmul_zero, mul_zero, map_zero]

theorem tT_incl (x : I.E) :
    PI.ScPsiExists.UnitaryGroupMassFormula.tT (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed) (Formalism.UG.inclE (F := I.F) (Af I.F) x) =
      algebraMap I.F (Af I.F) (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
  simp [Formalism.UG.inclE, PI.ScPsiExists.UnitaryGroupMassFormula.tT_tmul]

theorem trace_of_psi (x : I.E) (h : Formalism.L2.SG.HidaSetting.psiEinf I x = 1) :
    ∃ n : ℤ, Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) = n := by
  have := I.cm.totReal
  have h' : PI.ScPsiExists.psiEinf I x = 1 := h
  rw [PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq] at h'
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h'
  refine ⟨n, ?_⟩
  have h2 : ∀ v : InfinitePlace I.F,
      I.φ v x + star (I.φ v x) = v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
    intro v
    rw [← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add, I.cm.cmUnram.2.1 (I.φ v) x]
    rfl
  have h3 : ((PI.ScPsiExists.UnitaryGroupMassFormula.sHom I x : ℝ) : ℂ) =
      algebraMap ℚ ℂ (Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x)) := by
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe, Finset.sum_congr rfl (fun v _ => h2 v),
      PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace]
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero
  have h4 : ((PI.ScPsiExists.UnitaryGroupMassFormula.sHom I x : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  rw [h3, show (n : ℂ) = algebraMap ℚ ℂ (n : ℚ) by rw [map_intCast]] at h4
  exact (algebraMap ℚ ℂ).injective h4

theorem core (psiEf : I.E ⊗[I.F] Af I.F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Af I.F) x) * Formalism.L2.SG.HidaSetting.psiEinf I x = 1)
    (g : ℕ) (ew : I.E ⊗[I.F] Af I.F) (v : HeightOneSpectrum (𝓞 I.F))
    (htr : Formalism.L2.SG.Pf.TypedLoc.trV I v (Formalism.UG.prV (E := I.E) v ew) = 1)
    (hg : v.valuation I.F ((g : ℕ) : I.F) = WithZero.exp (-1 : ℤ))
    (hun : Algebra.IsUnramifiedAt ℤ v.asIdeal) :
    ∃ o ∈ v.adicCompletionIntegers I.F,
      psiEf (Formalism.L2.SG.HidaSetting.divN I g (ew * ((1 : I.E) ⊗ₜ[I.F] Formalism.UG.P.afsplitI v o))) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy⟩ := approxF ((((g : ℕ) : I.F)⁻¹) • Formalism.UG.P.afsplitI v (1 : v.adicCompletion I.F))
  have htrz : ∀ z : 𝓞 I.F, ∃ n : ℤ, Algebra.trace ℚ I.F (y * algebraMap (𝓞 I.F) I.F z) = n := by
    intro z
    set o : v.adicCompletion I.F := (algebraMap I.F (Af I.F) (algebraMap (𝓞 I.F) I.F z)) v with ho
    have hoO : o ∈ v.adicCompletionIntegers I.F := intAd_at (PI.ScPsiExists.UnitaryGroupMassFormula.alg_int_mem I.F z) v
    set b := Formalism.L2.SG.HidaSetting.divN I g (ew * ((1 : I.E) ⊗ₜ[I.F] Formalism.UG.P.afsplitI v o)) with hb
    have hb1 : psiEf b = 1 := hcon o hoO
    obtain ⟨x, hx⟩ := approxE I.F I.E b
    have hbx : psiEf (Formalism.UG.inclE (F := I.F) (Af I.F) x) = 1 := by
      have := hadd (Formalism.UG.inclE (F := I.F) (Af I.F) x) (b - Formalism.UG.inclE (F := I.F) (Af I.F) x)
      rw [add_sub_cancel, hb1, hint _ hx, mul_one] at this
      exact this.symm
    have hinf : Formalism.L2.SG.HidaSetting.psiEinf I x = 1 := by
      have := hrat x
      rwa [hbx, one_mul] at this
    obtain ⟨n, hn⟩ := trace_of_psi I x hinf
    have htb : PI.ScPsiExists.UnitaryGroupMassFormula.tT (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed) b =
        ((((g : ℕ) : I.F)⁻¹) • Formalism.UG.P.afsplitI v (1 : v.adicCompletion I.F)) *
          algebraMap I.F (Af I.F) (algebraMap (𝓞 I.F) I.F z) := by
      rw [hb, Formalism.L2.SG.HidaSetting.divN, ← Algebra.smul_def, map_smul, tT_ew I ew v htr, ho,
        Formalism.UG.P.afsplitI_eval, smul_mul_assoc]
    have hmem : algebraMap I.F (Af I.F) (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x -
        y * algebraMap (𝓞 I.F) I.F z) ∈ Formalism.UG.intAd I.F := by
      have e1 : algebraMap I.F (Af I.F) (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x -
          y * algebraMap (𝓞 I.F) I.F z) =
          ((((g : ℕ) : I.F)⁻¹) • Formalism.UG.P.afsplitI v (1 : v.adicCompletion I.F) - algebraMap I.F (Af I.F) y) *
            algebraMap I.F (Af I.F) (algebraMap (𝓞 I.F) I.F z) -
          PI.ScPsiExists.UnitaryGroupMassFormula.tT (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed)
            (b - Formalism.UG.inclE (F := I.F) (Af I.F) x) := by
        rw [map_sub (PI.ScPsiExists.UnitaryGroupMassFormula.tT (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed)), htb, tT_incl,
          map_sub, map_mul]
        ring
      rw [e1]
      exact sub_mem (mul_mem hy (PI.ScPsiExists.UnitaryGroupMassFormula.alg_int_mem I.F z))
        (PI.ScPsiExists.UnitaryGroupMassFormula.tT_mem _ (PI.ScPsiExists.UnitaryGroupMassFormula.tau_int I.cm.fixed) _ hx)
    obtain ⟨d, hd⟩ := PI.ScPsiExists.UnitaryGroupMassFormula.int_of_alg_mem I.F _ hmem
    have hdi : ∃ k : ℤ, Algebra.trace ℚ I.F (algebraMap (𝓞 I.F) I.F d) = k := by
      have hi : IsIntegral ℤ (Algebra.trace ℚ I.F (algebraMap (𝓞 I.F) I.F d)) :=
        Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe d)
      obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hi
      exact ⟨k, by rw [← hk]; simp⟩
    obtain ⟨k, hk⟩ := hdi
    refine ⟨n - k, ?_⟩
    have e2 : y * algebraMap (𝓞 I.F) I.F z =
        PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x - algebraMap (𝓞 I.F) I.F d := by
      rw [hd]; ring
    rw [e2, map_sub, hn, hk]
    push_cast
    ring
  obtain ⟨d, hd, hdv⟩ := exists_diff_not_mem v hun
  obtain ⟨c, hc⟩ := mul_diff_int y htrz d hd
  have hvd : v.valuation I.F (algebraMap (𝓞 I.F) I.F d) = 1 := by
    rw [valuation_of_algebraMap, intValuation_eq_one_iff.2 hdv]
  have hvy : v.valuation I.F y ≤ 1 := by
    have h1 : v.valuation I.F (algebraMap (𝓞 I.F) I.F c) ≤ 1 := HeightOneSpectrum.valuation_le_one v c
    rw [hc, map_mul, hvd, mul_one] at h1
    exact h1
  have h1 := intAd_at hy v
  rw [Formalism.UG.P.afsplit_sub_apply, Formalism.UG.P.afsplit_smul_apply, Formalism.UG.P.afsplitI_self,
    FiniteAdeleRing.algebraMap_apply] at h1
  have h2 : ((y : I.F) : v.adicCompletion I.F) ∈ v.adicCompletionIntegers I.F := by
    rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']
    exact hvy
  have h3 := add_mem h1 h2
  rw [sub_add_cancel, Algebra.smul_def, mul_one, mem_adicCompletionIntegers] at h3
  have e3 : algebraMap I.F (v.adicCompletion I.F) (((g : ℕ) : I.F)⁻¹) =
      ((((g : ℕ) : I.F)⁻¹ : I.F) : v.adicCompletion I.F) := rfl
  rw [e3, valuedAdicCompletion_eq_valuation', map_inv₀, hg, ← WithZero.exp_neg, neg_neg,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
  omega

end Inst

end PsiCondAllPf

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in

theorem psi_conductor_all_places : Formalism.L2.SG.Pf.PsiCondAll := by
  intro D X v hv
  have hv' : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    rw [← Nat.cast_mul, ← X.g_eq]; exact hv
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    rcases v.isPrime.mem_or_mem hv' with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
    letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
    exact PsiCondAllPf.unram_of (D.host.g i) (D.host.g_prime i) v hi
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E (D.host.g_prime i) (D.nd.g_split i) v hi).1
  have hg : v.valuation X.B.I.F ((X.B.g : ℕ) : X.B.I.F) = WithZero.exp (-1 : ℤ) := by
    have h := Formalism.L2.SG.Pf.gUnif_holds X v hv
    have e : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) =
        (((X.B.g : ℕ) : X.B.I.F) : v.adicCompletion X.B.I.F) := by
      rw [← map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F))]; rfl
    rwa [e, valuedAdicCompletion_eq_valuation'] at h
  exact PsiCondAllPf.core X.B.I X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat X.B.g X.ew v
    (Formalism.L2.SG.Pf.TypedLoc.trV_eV X v hv) hg hun
