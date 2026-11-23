import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBase
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (AF psiV)
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

namespace GlobalTheory.HeckeEps

variable {E : Type} [Field E] [NumberField E]

variable (E) in

def stdChar : AddChar (AF E) ℂ := (GlobalTheory.StdCharUnique.existsUnique_isStdChar E).exists.choose

variable (E) in

theorem isStdChar_stdChar : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar E (stdChar E) :=
  (GlobalTheory.StdCharUnique.existsUnique_isStdChar E).exists.choose_spec

theorem eq_stdChar {ψ : AddChar (AF E) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar E ψ) : ψ = stdChar E :=
  (GlobalTheory.StdCharUnique.existsUnique_isStdChar E).unique h (isStdChar_stdChar E)

def psiAt (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : ℂ := psiV E (stdChar E) w x

def diffExp (w : HeightOneSpectrum (𝓞 E)) : ℕ := multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E))

open Classical in

def gaussTerm (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (c : Eˣ) (y : E) : ℂ :=
  if h : y = 0 then 0 else
    (((χ.locK w (Units.mk0 y h))⁻¹ : ℂˣ) : ℂ) * psiAt w (algebraMap E (w.adicCompletion E) (y / c))

def gaussSumAt (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) : ℂ :=
  ∑ᶠ y : (𝓞 E ⧸ w.asIdeal ^ a)ˣ, gaussTerm χ w c ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E)

def locEps (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (s : ℂ) : ℂ :=
  ((χ.locK w (unif w ^ (a + diffExp w)) : ℂˣ) : ℂ) *
    ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s * ((a + diffExp w : ℕ) : ℂ)) *
    ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((diffExp w : ℂ) / 2) *
    if a = 0 then 1 else gaussSumAt χ w a (unif w ^ (a + diffExp w))

def finEps (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) : ℂ := ∏ᶠ w, locEps χ w (a w) s

def archEps {I : Type} [Fintype I] (n : I → ℤ) : ℂ := (-Complex.I) ^ (∑ i, (n i).natAbs)

instance finite_units_quot (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) : Finite (𝓞 E ⧸ w.asIdeal ^ a)ˣ := by
  have : Finite (𝓞 E ⧸ w.asIdeal ^ a) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
  infer_instance

theorem psiAt_add (w : HeightOneSpectrum (𝓞 E)) (x y : w.adicCompletion E) : psiAt w (x + y) = psiAt w x * psiAt w y :=
  GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.psiV_add _ _ _ _ _

theorem psiAt_conductor (w : HeightOneSpectrum (𝓞 E)) (t : w.adicCompletion E) :
    (∀ r ∈ w.adicCompletionIntegers E, psiAt w (t * r) = 1) ↔ Valued.v t ≤ WithZero.exp (diffExp w : ℤ) := by
  classical
  have h := GlobalTheory.StdDual.mem_dualV_iff_valued (isStdChar_stdChar E) w t
  have hD := coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)
  have h2 : -FractionalIdeal.count E w (GlobalTheory.StdDual.codiff E) = (diffExp w : ℤ) := by
    rw [← FractionalIdeal.count_inv, ← hD, FractionalIdeal.count_coe E w differentIdeal_ne_bot, diffExp,
      ← w.count_normalizedFactors_eq_multiplicity differentIdeal_ne_bot,
      Ideal.count_associates_factors_eq differentIdeal_ne_bot w.isPrime w.ne_bot]
  rw [← h2]
  exact h

theorem psiAt_eq_one {w : HeightOneSpectrum (𝓞 E)} {t : w.adicCompletion E} (h : Valued.v t ≤ WithZero.exp (diffExp w : ℤ)) :
    psiAt w t = 1 := by
  simpa using (psiAt_conductor w t).2 h 1 (one_mem _)

theorem gaussTerm_congr' {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : LevelLe χ w a) {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) {y y' : E} (hy : w.valuation E y = 1)
    (hy' : w.valuation E y' = 1) (hd : w.valuation E (y - y') ≤ WithZero.exp (-(a : ℤ))) :
    gaussTerm χ w c y = gaussTerm χ w c y' := by
  have h0 : ∀ {z : E}, w.valuation E z = 1 → z ≠ 0 := fun {z} hz h => by
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [gaussTerm, gaussTerm, dif_neg (h0 hy), dif_neg (h0 hy')]
  congr 1
  · have h1 : χ.loc w (atFin w (Units.mk0 _ (h0 hy) * (Units.mk0 _ (h0 hy'))⁻¹)) = 1 := by
      have e : ((atFin w (Units.mk0 _ (h0 hy) * (Units.mk0 _ (h0 hy'))⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
          algebraMap E (w.adicCompletion E) (y / y') := by
        simp [atFin, div_eq_mul_inv]
      refine hχ _ ?_ ?_
      · rw [IsUnitAt, e, hval, map_div₀, hy, hy', div_one]
      · rw [e, ← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, hval, div_sub_one (h0 hy'), map_div₀, hy', div_one]
        exact hd
    rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h1
    exact congrArg (fun u : ℂˣ => ((u⁻¹ : ℂˣ) : ℂ)) h1
  · have e : y / c = y' / c + (y - y') / c := by ring
    rw [e, map_add, psiAt_add, psiAt_eq_one (t := algebraMap E _ ((y - y') / c)), mul_one]
    rw [hval, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
    convert hd using 2
    push_cast
    ring

theorem valuation_sub_le {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} {y y' : 𝓞 E} (h : y - y' ∈ w.asIdeal ^ a) :
    w.valuation E ((y : E) - y') ≤ WithZero.exp (-(a : ℤ)) := by
  have := (w.intValuation_le_pow_iff_mem (y - y') a).2 h
  rw [← w.valuation_of_algebraMap (K := E)] at this
  simpa using this

theorem gaussTerm_congr {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : LevelLe χ w a) {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) {y y' : 𝓞 E} (hy : y ∉ w.asIdeal) (hy' : y' ∉ w.asIdeal)
    (h : y - y' ∈ w.asIdeal ^ a) : gaussTerm χ w c y = gaussTerm χ w c y' :=
  gaussTerm_congr' hχ hc ((w.valuation_eq_one_iff_notMem (K := E)).2 hy) ((w.valuation_eq_one_iff_notMem (K := E)).2 hy')
    (valuation_sub_le h)

theorem valuation_unif_pow (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) :
    w.valuation E ((unif w ^ k : Eˣ) : E) = WithZero.exp (-(k : ℤ)) := by
  have h : w.valuation E ((unif w : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans (unif_spec w)
  rw [Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem out_notMem (w : HeightOneSpectrum (𝓞 E)) {a : ℕ} (ha : a ≠ 0) (y : (𝓞 E ⧸ w.asIdeal ^ a)ˣ) :
    (Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) ∉ w.asIdeal := by
  intro h
  have h1 := (y.isUnit.map (Ideal.Quotient.factor (Ideal.pow_le_self ha : w.asIdeal ^ a ≤ w.asIdeal)))
  rw [← Ideal.Quotient.mk_out (y : 𝓞 E ⧸ w.asIdeal ^ a), Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 h] at h1
  have := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  exact not_isUnit_zero h1

theorem locK_mul_gaussSumAt_eq {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (ha : a ≠ 0) (hχ : LevelLe χ w a) {c c' : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ)))
    (hc' : w.valuation E (c' : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ((χ.locK w c' : ℂˣ) : ℂ) * gaussSumAt χ w a c' = ((χ.locK w c : ℂˣ) : ℂ) * gaussSumAt χ w a c := by
  have := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal ^ a)ˣ
  have := w.isMaximal
  have hu : w.valuation E ((c : E) / c') = 1 := by rw [map_div₀, hc, hc', div_self WithZero.exp_ne_zero]
  obtain ⟨r, hr⟩ := w.exists_valuation_sub_lt_of_integer hu.le (Units.mk0 _ (WithZero.exp_ne_zero (a := -(a : ℤ))))
  rw [Units.val_mk0] at hr
  have hr1 : w.valuation E (r : E) = 1 := by
    rw [← hu]
    refine Valuation.map_eq_of_sub_lt _ (hr.trans_le ?_)
    rw [hu, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨ρ, hρ⟩ := Ideal.Quotient.isUnit_mk_pow_of_notMem w.asIdeal (n := a) ((w.valuation_eq_one_iff_notMem (K := E)).1 hr1)
  rw [gaussSumAt, gaussSumAt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight ρ) _ _ fun y => ?_
  set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) with hz
  have hz1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 (out_notMem w ha y)
  have hz0 : (z : E) ≠ 0 := fun h => by
    rw [h, map_zero] at hz1
    exact zero_ne_one hz1
  have hzc : (z : E) * (c / c') ≠ 0 := mul_ne_zero hz0 (div_ne_zero c.ne_zero c'.ne_zero)
  have h1 : gaussTerm χ w c ((Quotient.out ((Equiv.mulRight ρ y : (𝓞 E ⧸ w.asIdeal ^ a)ˣ) : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) =
      gaussTerm χ w c (z * (c / c')) := by
    have h2 : (Quotient.out ((Equiv.mulRight ρ y : (𝓞 E ⧸ w.asIdeal ^ a)ˣ) : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) - z * r ∈ w.asIdeal ^ a := by
      rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, map_mul, hz, Ideal.Quotient.mk_out, ← hρ]
      rfl
    have h3 : w.valuation E ((z * r : 𝓞 E) : E) = 1 := by
      push_cast
      rw [map_mul, hz1, hr1, one_mul]
    rw [gaussTerm_congr' hχ hc ((w.valuation_eq_one_iff_notMem (K := E)).2 (out_notMem w ha _)) h3 (valuation_sub_le h2)]
    refine gaussTerm_congr' hχ hc h3 (by rw [map_mul, hz1, hu, one_mul]) ?_
    push_cast
    rw [← mul_sub, map_mul, hz1, one_mul]
    exact hr.le
  have e1 : Units.mk0 _ hzc = Units.mk0 _ hz0 * c * c'⁻¹ := by
    ext
    simp [div_eq_mul_inv, mul_assoc]
  have e2 : (z : E) * (c / c') / c = z / c' := by
    have := c.ne_zero
    field_simp
  rw [h1, gaussTerm, gaussTerm, dif_neg hz0, dif_neg hzc, e1, e2, map_mul, map_mul, map_inv]
  simp only [mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have := (χ.locK w c).ne_zero
  field_simp

theorem locEps_of_ne_zero {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (ha : a ≠ 0) (hχ : LevelLe χ w a) {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) (s : ℂ) :
    locEps χ w a s = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s * ((a + diffExp w : ℕ) : ℂ)) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((diffExp w : ℂ) / 2) * (((χ.locK w c : ℂˣ) : ℂ) * gaussSumAt χ w a c) := by
  rw [locEps, if_neg ha, locK_mul_gaussSumAt_eq ha hχ (valuation_unif_pow w _) hc]
  ring

theorem locEps_zero (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    locEps χ w 0 s = ((val χ w : ℂˣ) : ℂ) ^ diffExp w * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s * (diffExp w : ℂ)) *
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((diffExp w : ℂ) / 2) := by
  simp [locEps, Formalism.L2.Host.HChar.val]

theorem locEps_eq_one (χ : HChar E) {w : HeightOneSpectrum (𝓞 E)} (h : diffExp w = 0) (s : ℂ) : locEps χ w 0 s = 1 := by
  simp [locEps_zero, h]

theorem finite_mulSupport_locEps (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) :
    (Function.mulSupport fun w => locEps χ w (a w) s).Finite := by
  refine ((Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E))).union a.support.finite_toSet).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
  exact hw (by simp only [hn.2]; exact locEps_eq_one χ (multiplicity_eq_zero.2 hn.1) s)

theorem archEps_two_mul {I : Type} [Fintype I] (m : I → ℤ) :
    archEps (fun i => 2 * m i) = Complex.I ^ (∑ i, (2 * m i).natAbs) := by
  refine Even.neg_pow (Finset.even_sum _ fun i _ => ?_) _
  rw [Int.natAbs_mul]
  exact even_two_mul _

theorem completed_eq_mul {I : Type} [Fintype I] {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ)
    (hL : IsHeckeL χ L) {s : ℂ} (hs : ∀ (i : I) (k : ℕ), s + ((|n i| : ℤ) : ℂ) / 2 ≠ -k) : Λ s = archFactor n s * L s := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hne : ∀ {s : ℂ}, (∀ (i : I) (k : ℕ), s + ((|n i| : ℤ) : ℂ) / 2 ≠ -k) → archFactor n s ≠ 0 := fun hs =>
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero
      (fun h0 => hπ ((Complex.cpow_eq_zero_iff _ _).1 h0).1)) (Complex.Gamma_ne_zero (hs i))
  have hd : Differentiable ℂ fun s => (archFactor n s)⁻¹ := by
    have : (fun s => (archFactor n s)⁻¹) = fun s => ∏ i, (2⁻¹ * (2 * (Real.pi : ℂ)) ^ (s + ((|n i| : ℤ) : ℂ) / 2) *
        (Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))⁻¹) := by
      funext s
      rw [archFactor, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_inv, mul_inv, Complex.cpow_neg, inv_inv]
    rw [this]
    refine Differentiable.fun_finset_prod fun i _ => Differentiable.mul (Differentiable.const_mul ?_ _) ?_
    · exact (differentiable_id.add_const _).const_cpow (Or.inl hπ)
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have key : (fun s => (archFactor n s)⁻¹ * Λ s) = L := by
    refine entire_eq_of_halfPlane (hd.mul h.1) hL.1 1 fun s hs => ?_
    rw [h.eq_mul hL hs, inv_mul_cancel_left₀ (hne fun i k hk => ?_)]
    have h1 := congrArg Complex.re hk
    have h2 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
    have h3 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.intCast_re, Complex.neg_re, Complex.natCast_re] at h1
    linarith
  rw [← key, mul_inv_cancel_left₀ (hne hs)]

end GlobalTheory.HeckeEps

namespace GlobalTheory.Published

open GlobalTheory.HeckeEps

def HeckeEntire : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E),
    IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ

theorem HeckeEntire_holds : HeckeEntire := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf

def HeckeTateFunctionalEquation : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ), IsUnitary χ → Formalism.L2.Host.HChar.HasInf χ φ n →
      (∃ i, n i ≠ 0) → (∀ w, ExpAt χ w (a w)) →
        ∃ Λ Λ' : ℂ → ℂ, IsCompletedL χ n Λ ∧ IsCompletedL χ⁻¹ (fun i => -n i) Λ' ∧
          ∀ s : ℂ, Λ s = archEps n * finEps χ a s * Λ' (1 - s)

def HeckeTateFunctionalEquationCM : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E)
    (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ Λ' : ℂ → ℂ), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) →
      (∀ w, ExpAt χ w (a w)) → IsHeckeL χ Λ → IsHeckeL χ⁻¹ Λ' → ∀ s : ℂ,
        (∀ (i : I) (k : ℕ), s + ((|m i| : ℤ) : ℂ) ≠ -k) → (∀ (i : I) (k : ℕ), 1 - s + ((|m i| : ℤ) : ℂ) ≠ -k) →
          LInf m s * Λ s = Complex.I ^ (∑ i, (2 * m i).natAbs) * finEps χ a s * (LInf m (1 - s) * Λ' (1 - s))

theorem HeckeTateFunctionalEquation.cm (h : HeckeTateFunctionalEquation) : HeckeTateFunctionalEquationCM := by
  intro E _ _ _ I _ φ m χ a L L' hφ hu hi ⟨i, hm⟩ ha hL hL' s hs hs'
  obtain ⟨Λ, Λ', h1, h2, h3⟩ := h E I φ hφ χ (fun i => 2 * m i) a hu hi ⟨i, mul_ne_zero two_ne_zero hm⟩ ha
  have e : ∀ i, (((|2 * m i| : ℤ) : ℂ)) / 2 = ((|m i| : ℤ) : ℂ) := fun i => by
    rw [abs_mul, abs_two]; push_cast; ring
  have e' : ∀ t, archFactor (fun i => -(2 * m i)) t = LInf m t := fun t => by
    rw [← archFactor_two_mul]; simp only [archFactor, abs_neg]
  rw [← archFactor_two_mul, ← completed_eq_mul h1 hL (fun i k => by rw [e]; exact hs i k), h3, archEps_two_mul,
    completed_eq_mul h2 hL' (fun i k => by rw [abs_neg, e]; exact hs' i k), e']

end GlobalTheory.Published

end
