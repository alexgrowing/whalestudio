import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel Topology Filter
open scoped TensorProduct

namespace GlobalTheory.LocalData

section Padic

variable {K : Type*} [NormedField K] [IsUltrametricDist K] (l : ℕ) [hl : Fact l.Prime]

theorem norm_natCast_eq_one (h : ‖(l : K)‖ < 1) {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by
  by_contra hne
  have hm1 : ‖(m : K)‖ < 1 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one K m) hne
  have hc : IsCoprime (l : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm)
  obtain ⟨s, t, hst⟩ := hc
  have h1 : (s : K) * l + t * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hst
  have := IsUltrametricDist.norm_add_le_max ((s : K) * l) (t * m)
  rw [h1, norm_one, norm_mul, norm_mul] at this
  refine absurd this (not_le.2 (max_lt ?_ ?_))
  · exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one K s)
      (norm_nonneg _) h
  · exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one K t)
      (norm_nonneg _) hm1

omit [IsUltrametricDist K] in
theorem not_dvd_den {q : ℚ} (hq : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  intro hd
  have h1 : ‖((q.den : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (by exact_mod_cast hd)
  have h2 : (q.num : ℚ_[l]) = q * ((q.den : ℤ) : ℚ_[l]) := by
    have : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    exact_mod_cast congrArg (Rat.cast : ℚ → ℚ_[l]) this
  have h3 : ‖(q.num : ℚ_[l])‖ < 1 := by
    rw [h2, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hq (norm_nonneg _) h1
  have h4 : l ∣ q.num.natAbs := Int.natCast_dvd.1 (Padic.norm_intCast_lt_one_iff.1 h3)
  exact hl.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes q.reduced h4 hd)

theorem norm_ratCast_le_one [CharZero K] (h : ‖(l : K)‖ < 1) {q : ℚ} (hq : ‖(q : ℚ_[l])‖ ≤ 1) :
    ‖(q : K)‖ ≤ 1 := by
  rw [Rat.cast_def, norm_div, norm_natCast_eq_one l h (not_dvd_den l hq), div_one]
  exact IsUltrametricDist.norm_intCast_le_one K _

theorem exists_continuous_padic [CharZero K] [CompleteSpace K] (h : ‖(l : K)‖ < 1) :
    ∃ j : ℚ_[l] →+* K, Continuous j := by
  let w : AbsoluteValue ℚ ℝ := Rat.AbsoluteValue.padic l
  let i : WithAbs w →+* ℚ_[l] := (Rat.castHom ℚ_[l]).comp (WithAbs.equiv w).toRingHom
  let f : WithAbs w →+* K := (Rat.castHom K).comp (WithAbs.equiv w).toRingHom
  have hi : ∀ x, ‖i x‖ = ‖x‖ := fun x => Padic.eq_padicNorm _
  have hi' : Isometry i := AddMonoidHomClass.isometry_of_norm i hi
  have hf : UniformContinuous f := by
    refine uniformContinuous_of_continuousAt_zero f ?_
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h
    have hl0 : (l : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.out.ne_zero)
    have hl1 : (0 : ℝ) < ‖(((l : ℚ) ^ n : ℚ) : ℚ_[l])‖ := norm_pos_iff.2 (by exact_mod_cast hl0)
    refine ⟨_, hl1, fun {x} hx => ?_⟩
    rw [dist_zero_right, ← hi] at hx
    rw [map_zero, dist_zero_right]
    set q : ℚ := WithAbs.equiv w x
    change ‖(q : ℚ_[l])‖ < _ at hx
    change ‖(q : K)‖ < ε
    have h1 : ‖((q / (l : ℚ) ^ n : ℚ) : K)‖ ≤ 1 := by
      refine norm_ratCast_le_one l h ?_
      rw [Rat.cast_div, norm_div, div_le_one hl1]
      exact hx.le
    have h2 : (q : K) = ((q / (l : ℚ) ^ n : ℚ) : K) * (l : K) ^ n := by
      have : q = q / (l : ℚ) ^ n * (l : ℚ) ^ n := (div_mul_cancel₀ q hl0).symm
      exact_mod_cast congrArg (Rat.cast : ℚ → K) this
    rw [h2, norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (by positivity) h1).trans_lt hn
  have hd : DenseRange i :=
    (Padic.denseRange_ratCast l).mono (by
      rintro _ ⟨q, rfl⟩
      exact ⟨WithAbs.toAbs w q, rfl⟩)
  exact ⟨IsDenseInducing.extendRingHom hi'.isUniformInducing hd hf,
    (uniformContinuous_uniformly_extend hi'.isUniformInducing hd hf).continuous⟩

def IsPrincipalPart (x : ℚ_[l]) (a : ℚ) : Prop :=
  (∃ n : ℕ, a.den = l ^ n) ∧ ‖x - (a : ℚ_[l])‖ ≤ 1

theorem exists_isPrincipalPart (x : ℚ_[l]) : ∃ a, IsPrincipalPart l x a := by
  have hp : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖x‖ + 1)⁻¹ by positivity) hp
  have hx : ‖x * (l : ℚ_[l]) ^ n‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    calc ‖x‖ * ‖(l : ℚ_[l])‖ ^ n ≤ (‖x‖ + 1) * (‖x‖ + 1)⁻¹ := by gcongr; linarith
      _ = 1 := mul_inv_cancel₀ (by positivity)
  let z : ℤ_[l] := ⟨_, hx⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  refine ⟨(z.appr n : ℚ) / (l : ℚ) ^ n, ?_, ?_⟩
  · have : ((z.appr n : ℚ) / (l : ℚ) ^ n).den ∣ l ^ n := by
      have h := Rat.den_dvd (z.appr n : ℤ) ((l : ℤ) ^ n)
      rw [Rat.divInt_eq_div] at h
      simp only [Int.cast_natCast, Int.cast_pow] at h
      rw [← Nat.cast_pow (α := ℤ)] at h
      exact Int.natCast_dvd_natCast.1 h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 this
    exact ⟨k, hk⟩
  · have h1 : (c : ℚ_[l]) * (l : ℚ_[l]) ^ n = x * (l : ℚ_[l]) ^ n - (z.appr n : ℚ_[l]) := by
      have := congrArg (fun t : ℤ_[l] => (t : ℚ_[l])) hc
      simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_sub, PadicInt.coe_natCast] at this
      exact this
    have h2 : x - (((z.appr n : ℚ) / (l : ℚ) ^ n : ℚ) : ℚ_[l]) = c := by
      push_cast
      field_simp
      linear_combination -h1
    rw [h2]
    exact c.2

theorem den_dvd_pow_sub {a b : ℚ} (ha : ∃ n : ℕ, a.den = l ^ n) (hb : ∃ n : ℕ, b.den = l ^ n) :
    (∃ n : ℕ, (a + b).den = l ^ n) ∧ ∃ n : ℕ, (a - b).den = l ^ n := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  have h1 := Rat.add_den_dvd a b
  have h2 := Rat.sub_den_dvd a b
  rw [hm, hn, ← pow_add] at h1 h2
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 h1
  obtain ⟨k', -, hk'⟩ := (Nat.dvd_prime_pow hl.out).1 h2
  exact ⟨⟨k, hk⟩, k', hk'⟩

theorem IsPrincipalPart.add {x y : ℚ_[l]} {a b : ℚ} (ha : IsPrincipalPart l x a)
    (hb : IsPrincipalPart l y b) : IsPrincipalPart l (x + y) (a + b) := by
  refine ⟨(den_dvd_pow_sub l ha.1 hb.1).1, ?_⟩
  have : x + y - ((a + b : ℚ) : ℚ_[l]) = (x - a) + (y - b) := by push_cast; ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)

theorem IsPrincipalPart.exp_eq {x : ℚ_[l]} {a b : ℚ} (ha : IsPrincipalPart l x a)
    (hb : IsPrincipalPart l x b) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)) := by
  obtain ⟨n, hn⟩ := (den_dvd_pow_sub l ha.1 hb.1).2
  have h1 : ‖((a - b : ℚ) : ℚ_[l])‖ ≤ 1 := by
    have : ((a - b : ℚ) : ℚ_[l]) = (x - b) + -(x - a) := by push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb.2 (by rw [norm_neg]; exact ha.2))
  have h2 := not_dvd_den l h1
  have h3 : (a - b).den = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exact absurd (hn ▸ dvd_pow_self l n.succ_ne_zero) h2
  have h4 : a = b + ((a - b).num : ℚ) := by
    rw [Rat.coe_int_num_of_den_eq_one h3]; ring
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨(a - b).num, ?_⟩
  have h5 : (a : ℂ) = b + ((a - b).num : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) h4
  rw [h5]
  ring

def padicChar : AddChar ℚ_[l] ℂ where
  toFun x := Complex.exp (2 * Real.pi * Complex.I * ((exists_isPrincipalPart l x).choose : ℂ))
  map_zero_eq_one' := by
    have h0 : IsPrincipalPart l 0 0 := ⟨⟨0, by simp⟩, by simp⟩
    rw [(exists_isPrincipalPart l 0).choose_spec.exp_eq l h0]
    simp
  map_add_eq_mul' x y := by
    rw [(exists_isPrincipalPart l (x + y)).choose_spec.exp_eq l
      ((exists_isPrincipalPart l x).choose_spec.add l (exists_isPrincipalPart l y).choose_spec),
      ← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem padicChar_eq {x : ℚ_[l]} {a : ℚ} (ha : IsPrincipalPart l x a) :
    padicChar l x = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) :=
  (exists_isPrincipalPart l x).choose_spec.exp_eq l ha

end Padic

section Completion

variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))

theorem resChar_prime : (resChar p).Prime := by
  haveI := p.isMaximal
  letI := Ideal.Quotient.field p.asIdeal
  haveI : Finite (𝓞 F ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot
  exact CharP.char_is_prime (𝓞 F ⧸ p.asIdeal) _

theorem resChar_mem : ((resChar p : ℕ) : 𝓞 F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

@[reducible] def complRel : ValuativeRel (p.adicCompletion F) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))

theorem isLocalField : letI := complRel p; IsNonarchimedeanLocalField (p.adicCompletion F) := by
  letI := complRel p
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  haveI : IsValuativeTopology (p.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))) Valued.mem_nhds_zero
  haveI : ValuativeRel.IsNontrivial (p.adicCompletion F) := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))]
    infer_instance
  exact {}

theorem norm_resChar_lt_one : ‖((resChar p : ℕ) : p.adicCompletion F)‖ < 1 := by
  have := (NumberField.FinitePlace.norm_lt_one_iff_mem F p _).2 (resChar_mem p)
  rwa [map_natCast, map_natCast] at this

theorem complRel_algebraMap (x y : F) : letI := complRel p
    (algebraMap F (p.adicCompletion F) x ≤ᵥ algebraMap F (p.adicCompletion F) y) ↔
      p.valuation F x ≤ p.valuation F y := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p x,
    ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p y]
  exact Iff.rfl

end Completion

theorem exists_locAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E), Module.finrank F E = 2 → ∀ p : HeightOneSpectrum (𝓞 F), ∃ L : LocAt F E sig p, L.split = none := by
  intro F E _ _ _ _ _ sig hr p
  letI := complRel p
  haveI hp : Fact (resChar p).Prime := ⟨resChar_prime p⟩
  haveI hc : CharZero (p.adicCompletion F) :=
    charZero_of_injective_ringHom (algebraMap F (p.adicCompletion F)).injective
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨j, hj⟩ := exists_continuous_padic (resChar p) (norm_resChar_lt_one p)
  letI alg : Algebra ℚ_[resChar p] (p.adicCompletion F) := j.toAlgebra
  haveI : ContinuousSMul ℚ_[resChar p] (p.adicCompletion F) :=
    ⟨(hj.comp continuous_fst).mul continuous_snd⟩
  let sigE : E ≃ₐ[F] E := AlgEquiv.ofBijective sig (AlgHom.bijective sig)
  letI top : TopologicalSpace (p.adicCompletion F ⊗[F] E) := moduleTopology (p.adicCompletion F) _
  letI ms : MeasurableSpace (p.adicCompletion F ⊗[F] E) := borel _
  letI algE : Algebra ℚ_[resChar p] (p.adicCompletion F ⊗[F] E) :=
    ((algebraMap (p.adicCompletion F) (p.adicCompletion F ⊗[F] E)).comp
      (algebraMap ℚ_[resChar p] (p.adicCompletion F))).toAlgebra
  refine ⟨{
    Fp := p.adicCompletion F
    Ep := p.adicCompletion F ⊗[F] E
    epT := top
    epM := ms
    lf := isLocalField p
    char0 := hc
    ιF := algebraMap F _
    ιE := (Algebra.TensorProduct.includeRight : E →ₐ[F] p.adicCompletion F ⊗[F] E).toRingHom
    compat := fun a => ?_
    dense := HeightOneSpectrum.denseRange_algebraMap F p
    val := complRel_algebraMap p
    free := inferInstance
    rank := by rw [Module.finrank_baseChange, hr]
    span := ?_
    top := ⟨rfl⟩
    borel := ⟨rfl⟩
    cj := Algebra.TensorProduct.congr AlgEquiv.refl sigE
    cj_ιE := fun x => ?_
    O := (integralClosure 𝒪[p.adicCompletion F] (p.adicCompletion F ⊗[F] E)).toSubring
    O_def := fun x => Iff.rfl
    ellPrime := hp
    qlA := alg
    qlCont := hj
    qlFin := FiniteDimensional.of_locallyCompactSpace _
    psiE := (padicChar (resChar p)).compAddMonoidHom
      (@Algebra.trace ℚ_[resChar p] (p.adicCompletion F ⊗[F] E) _ _ algE).toAddMonoidHom
    psiE_def := fun y => ?_
    split := none }, rfl⟩
  · simp [Algebra.TensorProduct.algebraMap_apply]
  · rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | tmul a b =>
      have : a ⊗ₜ[F] b = a • ((1 : p.adicCompletion F) ⊗ₜ[F] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · simp [sigE]
  · obtain ⟨a, ha⟩ := exists_isPrincipalPart (resChar p)
      (@Algebra.trace ℚ_[resChar p] (p.adicCompletion F ⊗[F] E) _ _ algE y)
    exact ⟨a, ha.1, ha.2, padicChar_eq _ ha⟩

end GlobalTheory.LocalData

end
