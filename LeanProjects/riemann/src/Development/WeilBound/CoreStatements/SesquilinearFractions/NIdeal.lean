import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

namespace NI

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le {E : Type} [Field E] [NumberField E] {p : Nat.Primes} (j : 𝓞 E →+* ℂ_[p]) (r : 𝓞 E) :
    ‖j r‖ ≤ 1 :=
  norm_le_one_of_isIntegral (map_isIntegral_int j (Algebra.IsIntegral.isIntegral r))

theorem logIdeal_eq {E : Type} [Field E] [NumberField E] {p : Nat.Primes} (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E))
    {a : 𝓞 E} (ha : a ∈ I) (h : ∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) : logIdeal j I = Real.log ‖j a‖ := by
  unfold logIdeal
  congr 1
  exact le_antisymm (ciSup_le fun x => h x.1 x.2)
    (le_ciSup (f := fun x : I => ‖j (x : 𝓞 E)‖) ⟨‖j a‖, by rintro _ ⟨x, rfl⟩; exact h x.1 x.2⟩ ⟨a, ha⟩)

end NI

theorem padic_logIdeal_max_element : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]) (I : Ideal (𝓞 E)), Function.Injective j → I ≠ ⊥ → ∃ a ∈ I, a ≠ 0 ∧ (∀ b ∈ I, ‖j b‖ ≤ ‖j a‖) ∧ logIdeal j I = Real.log ‖j a‖ := by
  intro E _ _ p j I hj hI
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact absurd (by rw [← hS, h, Finset.coe_empty, Submodule.span_empty]) hI
    · exact h
  obtain ⟨a, haS, hmax⟩ := S.exists_max_image (fun s => ‖j s‖) hSne
  have haI : a ∈ I := hS ▸ Submodule.subset_span haS
  have hle : ∀ b ∈ I, ‖j b‖ ≤ ‖j a‖ := by
    intro b hb
    rw [← hS] at hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact hmax x hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul r x _ hx =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (NI.norm_int_le j r)).trans hx
  have ha0 : a ≠ 0 := by
    intro h0
    apply hI
    rw [Submodule.eq_bot_iff]
    intro b hb
    have := hle b hb
    rw [h0, map_zero, norm_zero] at this
    exact hj (by rw [map_zero]; exact norm_le_zero_iff.1 this)
  exact ⟨a, haI, ha0, hle, NI.logIdeal_eq j I haI hle⟩

theorem log_ideal_mul_span_map : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (j : 𝓞 E →+* ℂ_[p]), Function.Injective j → (∀ I J : Ideal (𝓞 E), I ≠ ⊥ → J ≠ ⊥ → logIdeal j (I * J) = logIdeal j I + logIdeal j J) ∧ (∀ a : 𝓞 E, logIdeal j (Ideal.span {a}) = Real.log ‖j a‖) ∧ ∀ e : 𝓞 E ≃+* 𝓞 E, ∀ I : Ideal (𝓞 E), logIdeal j (I.map (e : 𝓞 E →+* 𝓞 E)) = logIdeal (j.comp (e : 𝓞 E →+* 𝓞 E)) I := by
  intro E _ _ p j hj
  refine ⟨fun I J hI hJ => ?_, fun a => ?_, fun e I => ?_⟩
  · obtain ⟨a, haI, ha0, hla, ea⟩ := padic_logIdeal_max_element E p j I hj hI
    obtain ⟨b, hbJ, hb0, hlb, eb⟩ := padic_logIdeal_max_element E p j J hj hJ
    have hle : ∀ c ∈ I * J, ‖j c‖ ≤ ‖j (a * b)‖ := by
      intro c hc
      rw [map_mul, norm_mul]
      refine Submodule.mul_induction_on (C := fun c => ‖j c‖ ≤ ‖j a‖ * ‖j b‖) hc (fun m hm n hn => ?_) (fun x y hx hy => ?_)
      · rw [map_mul, norm_mul]
        exact mul_le_mul (hla m hm) (hlb n hn) (norm_nonneg _) (norm_nonneg _)
      · rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    rw [NI.logIdeal_eq j (I * J) (Ideal.mul_mem_mul haI hbJ) hle, ea, eb, map_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 fun h => ha0 (hj (by rw [h, map_zero])))
        (norm_ne_zero_iff.2 fun h => hb0 (hj (by rw [h, map_zero])))]
  · refine NI.logIdeal_eq j _ (Ideal.mem_span_singleton_self a) fun b hb => ?_
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (NI.norm_int_le j r)
  · unfold logIdeal
    congr 1
    let eq : I ≃ I.map (e : 𝓞 E →+* 𝓞 E) :=
      { toFun := fun x => ⟨e x, Ideal.mem_map_of_mem _ x.2⟩
        invFun := fun y => ⟨e.symm y, by
          obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective (e : 𝓞 E →+* 𝓞 E) e.surjective).1 y.2
          have : e.symm (y : 𝓞 E) = x := by rw [← hxy]; exact e.symm_apply_apply x
          rw [this]; exact hx⟩
        left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
        right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
    exact (eq.iSup_congr fun x => rfl).symm

theorem logIdeal_support_finite : ∀ (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)), I ≠ ⊥ → {p : Nat.Primes | ∃ j : 𝓞 E →+* ℂ_[p], logIdeal j I ≠ 0}.Finite := by
  intro E _ _ I hI
  set n := Ideal.absNorm I with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hnI : (n : 𝓞 E) ∈ I := Ideal.absNorm_mem I
  refine ((Nat.primeFactors n).finite_toSet.preimage (Set.injOn_of_injective Subtype.val_injective)).subset ?_
  intro p hp
  obtain ⟨j, hj⟩ := hp
  simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_primeFactors]
  refine ⟨p.2, ?_, hn0⟩
  by_contra hdvd
  apply hj
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  have h1 : ‖j (n : 𝓞 E)‖ = 1 := by
    rw [map_natCast]
    have : ((n : ℚ_[p]) : ℂ_[p]) = (n : ℂ_[p]) := by simp
    rw [← this, PadicComplex.norm_extends', Padic.norm_natCast_eq_one_iff]
    first
    | exact hdvd
    | exact (Nat.Prime.coprime_iff_not_dvd p.2).2 hdvd
    | exact ((Nat.Prime.coprime_iff_not_dvd p.2).2 hdvd).symm
    | simpa using hdvd
  rw [NI.logIdeal_eq j I hnI (fun b _ => h1 ▸ NI.norm_int_le j b), h1, Real.log_one]

end PositivityTheory.Xgf
