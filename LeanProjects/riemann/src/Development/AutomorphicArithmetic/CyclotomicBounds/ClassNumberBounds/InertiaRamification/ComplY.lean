import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ComplDefY
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.LocDiffY
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDisc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.EmbDefY
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.SplitDef

namespace KStar.Ram

open NumberField IsDedekindDomain IsLocalRing

private theorem cy_mem_span_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (n : ℕ) (x : M) :
    x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R M) ↔ ∃ y, a ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem cy_precomplete_pi {R ι : Type*} [CommRing R] (a : R)
    [h : IsPrecomplete (Ideal.span {a}) R] : IsPrecomplete (Ideal.span {a}) (ι → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine h.prec' (fun n => f n i) ?_
    intro m n hmn
    have hm := hf hmn
    rw [SModEq.sub_mem, cy_mem_span_smul] at hm ⊢
    obtain ⟨y, hy⟩ := hm
    exact ⟨y i, by simpa using congrFun hy i⟩
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, cy_mem_span_smul]
  have hy : ∀ i, ∃ y : R, a ^ n • y = f n i - L i := by
    intro i
    have hi := hL i n
    rw [SModEq.sub_mem, cy_mem_span_smul] at hi
    exact hi
  choose y hy using hy
  exact ⟨y, funext fun i => by simpa using hy i⟩

variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
  (l : ℕ) [Fact l.Prime] [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})]

private theorem cy_pow_map {B R : Type*} [CommRing B] [IsDedekindDomain B] [CharZero B] [CommRing R]
    [IsLocalRing R] {P : Ideal B} (hP : P ≠ ⊥) {τ : B →+* R} (hτ : τ ∈ embOver R P) {l : ℕ}
    (hl : l ≠ 0) :
    (P ^ multiplicity P (Ideal.span {(l : B)})).map τ = Ideal.span {(l : R)} := by
  have hPp : P.IsPrime := by
    rw [← (hτ : Ideal.comap τ (maximalIdeal R) = P)]
    exact Ideal.comap_isPrime _ _
  have hprime : Prime P := Ideal.prime_of_isPrime hP hPp
  have hl0 : Ideal.span {(l : B)} ≠ ⊥ := by simp [hl]
  have hfin : FiniteMultiplicity P (Ideal.span {(l : B)}) :=
    FiniteMultiplicity.of_not_isUnit hprime.not_unit hl0
  obtain ⟨J, hJ⟩ := pow_multiplicity_dvd P (Ideal.span {(l : B)})
  set e := multiplicity P (Ideal.span {(l : B)}) with he
  have hJP : ¬ J ≤ P := by
    intro hle
    have hPJ : P ∣ J := Ideal.dvd_iff_le.mpr hle
    have hd : P ^ (e + 1) ∣ P ^ e * J := by
      rw [pow_succ]
      exact mul_dvd_mul_left (P ^ e) hPJ
    rw [← hJ] at hd
    exact hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self e) hd
  obtain ⟨j, hjJ, hjP⟩ := Set.not_subset.1 hJP
  have hJtop : J.map τ = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem τ hjJ)
    by_contra hu
    apply hjP
    have hc : Ideal.comap τ (maximalIdeal R) = P := hτ
    show j ∈ P
    rw [← hc, Ideal.mem_comap]
    exact (IsLocalRing.mem_maximalIdeal _).2 hu
  have hm := congrArg (Ideal.map τ) hJ
  rw [Ideal.map_mul, hJtop, Ideal.mul_top, Ideal.map_span, Set.image_singleton,
    map_natCast] at hm
  exact hm.symm

omit l in
private theorem cy_emb : algebraMap (𝓞 E) (w.adicCompletionIntegers E) ∈
    embOver (w.adicCompletionIntegers E) w.asIdeal := by
  simpa [embOver] using (complIntegers_quotient w 1).2.1

omit [NumberField E] [Fact (Nat.Prime l)] in
private theorem cy_l_mem' : (l : 𝓞 E) ∈ w.asIdeal := by
  have h : ((l : ℤ)) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
  rw [Ideal.mem_of_liesOver w.asIdeal (Ideal.span {(l : ℤ)})] at h
  simpa using h

private theorem cy_l_mem : (l : w.adicCompletionIntegers E) ∈
    maximalIdeal (w.adicCompletionIntegers E) := by
  have h : (maximalIdeal (w.adicCompletionIntegers E)).comap (algebraMap (𝓞 E) _) = w.asIdeal :=
    cy_emb w
  have := cy_l_mem' w l
  rw [← h, Ideal.mem_comap, map_natCast] at this
  exact this

omit [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})] in
private theorem cy_max_pow (n : ℕ) : maximalIdeal (w.adicCompletionIntegers E) ^
    (multiplicity w.asIdeal (Ideal.span {(l : 𝓞 E)}) * n) =
      Ideal.span {(l : w.adicCompletionIntegers E) ^ n} := by
  rw [pow_mul, ← (complIntegers_quotient w _).1,
    cy_pow_map w.ne_bot (cy_emb w) (Fact.out : l.Prime).ne_zero, Ideal.span_singleton_pow]

omit [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})] in
private theorem cy_approx (n : ℕ) (y : w.adicCompletionIntegers E) :
    ∃ (x : 𝓞 E) (z : w.adicCompletionIntegers E), y = algebraMap _ _ x + (l : _) ^ n * z := by
  obtain ⟨x, hx⟩ := (complIntegers_quotient w
    (multiplicity w.asIdeal (Ideal.span {(l : 𝓞 E)}) * n)).2.2 y
  rw [cy_max_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨z, hz⟩ := hx
  exact ⟨x, z, by rw [← hz]; ring⟩

private theorem cy_tf [Algebra ℤ_[l] (w.adicCompletionIntegers E)] :
    Module.IsTorsionFree ℤ_[l] (w.adicCompletionIntegers E) := by
  obtain ⟨f, F, h1, -, -, h2, -⟩ := existsUnique_padic_hom w l
  rw [Module.isTorsionFree_iff_algebraMap_injective, h2 (algebraMap _ _)]
  exact h1

private theorem cy_fin [Algebra ℤ_[l] (w.adicCompletionIntegers E)] :
    Module.Finite ℤ_[l] (w.adicCompletionIntegers E) := by
  have hIc : IsPrecomplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  haveI := cy_precomplete_pi (ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (l : ℤ_[l])
  have halg : algebraMap ℤ_[l] (w.adicCompletionIntegers E) (l : ℤ_[l]) =
      (l : w.adicCompletionIntegers E) := map_natCast _ _
  have he : 1 ≤ multiplicity w.asIdeal (Ideal.span {(l : 𝓞 E)}) := by
    by_contra h0
    have h1 := cy_max_pow w l 1
    rw [show multiplicity w.asIdeal (Ideal.span {(l : 𝓞 E)}) = 0 by omega, zero_mul, pow_zero,
      pow_one, eq_comm, Ideal.one_eq_top, Ideal.span_singleton_eq_top] at h1
    exact (maximalIdeal.isMaximal _).ne_top
      ((Ideal.eq_top_of_isUnit_mem _ (cy_l_mem w l) h1))
  haveI : IsHausdorff (Ideal.span {(l : ℤ_[l])}) (w.adicCompletionIntegers E) := by
    refine ⟨fun x hx => ?_⟩
    have hmem : ∀ n, x ∈ maximalIdeal (w.adicCompletionIntegers E) ^
        (multiplicity w.asIdeal (Ideal.span {(l : 𝓞 E)}) * n) := by
      intro n
      have h := hx n
      rw [SModEq.zero] at h
      obtain ⟨y, hy⟩ := (cy_mem_span_smul _ n x).1 h
      rw [cy_max_pow, Ideal.mem_span_singleton']
      exact ⟨y, by rw [← hy, Algebra.smul_def, map_pow, halg, mul_comm]⟩
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (w.adicCompletionIntegers E))
      (maximalIdeal.isMaximal _).ne_top
    rw [← Ideal.mem_bot, ← hbot, Ideal.mem_iInf]
    intro k
    exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left k he) (hmem k)
  let b := NumberField.RingOfIntegers.basis E
  let φ := Fintype.linearCombination ℤ_[l]
    (fun i => algebraMap (𝓞 E) (w.adicCompletionIntegers E) (b i))
  have hφ : Function.Surjective φ := by
    apply surjective_of_mkQ_comp_surjective (I := Ideal.span {(l : ℤ_[l])})
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, z, hxz⟩ := cy_approx w l 1 y
    refine ⟨fun i => ((b.repr x i : ℤ) : ℤ_[l]), ?_⟩
    have hx : φ (fun i => ((b.repr x i : ℤ) : ℤ_[l])) =
        algebraMap (𝓞 E) (w.adicCompletionIntegers E) x := by
      conv_rhs => rw [← b.sum_repr x]
      simp [φ, Fintype.linearCombination_apply, map_sum, Int.cast_smul_eq_zsmul]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hx]
    rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨-z, Submodule.mem_top, ?_⟩
    rw [hxz, Algebra.smul_def, halg, pow_one]
    ring
  exact Module.Finite.of_surjective φ hφ

private theorem cy_lies [Algebra ℤ_[l] (w.adicCompletionIntegers E)] :
    (maximalIdeal (w.adicCompletionIntegers E)).LiesOver (Ideal.span {(l : ℤ_[l])}) := by
  refine ⟨?_⟩
  rw [Ideal.under_def, ← PadicInt.maximalIdeal_eq_span_p]
  refine (maximalIdeal.isMaximal _).eq_of_le ?_ ?_
  · exact Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top
  · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact cy_l_mem w l

private theorem cy_efd [Algebra ℤ_[l] (w.adicCompletionIntegers E)]
    [Module.IsTorsionFree ℤ_[l] (w.adicCompletionIntegers E)] :
    w.asIdeal.ramificationIdx ℤ =
        (maximalIdeal (w.adicCompletionIntegers E)).ramificationIdx ℤ_[l] ∧
      w.asIdeal.inertiaDeg ℤ = (maximalIdeal (w.adicCompletionIntegers E)).inertiaDeg ℤ_[l] ∧
      multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) =
        multiplicity (maximalIdeal (w.adicCompletionIntegers E))
          (differentIdeal ℤ_[l] (w.adicCompletionIntegers E)) := by
  haveI := cy_fin w l
  haveI := cy_lies w l
  have hl : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
  have hf : algebraMap ℤ ℤ_[l] (l : ℤ) = (l : ℤ_[l]) := by simp
  haveI : (maximalIdeal (w.adicCompletionIntegers E)).LiesOver
      (Ideal.span {algebraMap ℤ ℤ_[l] (l : ℤ)}) := by rw [hf]; infer_instance
  refine multiplicity_differentIdeal_eq_of_quotient (algebraMap ℤ ℤ_[l])
    (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) (RingHom.ext_int _ _) hl
    (by rw [hf]; exact PadicInt.prime_p) w.asIdeal (maximalIdeal _) ?_ ?_ ?_ ?_
  · intro n y
    refine ⟨(PadicInt.appr y n : ℤ), ?_⟩
    rw [hf, ← Ideal.mem_span_singleton]
    simpa using PadicInt.appr_spec n y
  · intro n x hx
    rw [hf, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker] at hx
    have : ((x : ZMod (l ^ n))) = 0 := by simpa using hx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact_mod_cast this
  · intro n y
    obtain ⟨x, hx⟩ := (complIntegers_quotient w n).2.2 y
    exact ⟨x, hx⟩
  · intro n
    exact (complIntegers_quotient w n).2.1

theorem finrank_complIntegers [Algebra ℤ_[l] (w.adicCompletionIntegers E)] :
    Module.IsTorsionFree ℤ_[l] (w.adicCompletionIntegers E) ∧
      Module.Finite ℤ_[l] (w.adicCompletionIntegers E) ∧
      Module.Free ℤ_[l] (w.adicCompletionIntegers E) ∧
      Module.finrank ℤ_[l] (w.adicCompletionIntegers E) =
        w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ := by
  haveI := cy_tf w l
  haveI := cy_fin w l
  haveI : Module.Free ℤ_[l] (w.adicCompletionIntegers E) := Module.free_of_finite_type_torsion_free'
  refine ⟨‹_›, ‹_›, ‹_›, ?_⟩
  obtain ⟨he, hf, -⟩ := cy_efd w l
  rw [he, hf]
  haveI := cy_lies w l
  haveI hmax : (Ideal.span {(l : ℤ_[l])}).IsMaximal := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have hmem : maximalIdeal (w.adicCompletionIntegers E) ∈
      (Ideal.span {(l : ℤ_[l])}).primesOver (w.adicCompletionIntegers E) :=
    ⟨inferInstance, inferInstance⟩
  haveI : Unique ((Ideal.span {(l : ℤ_[l])}).primesOver (w.adicCompletionIntegers E)) :=
    { default := ⟨_, hmem⟩
      uniq := by
        rintro ⟨q, hq1, hq2⟩
        apply Subtype.ext
        have : q.IsMaximal := by
          apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l])
          rw [← Ideal.under_def, ← hq2.over]
          exact hmax
        exact IsLocalRing.eq_maximalIdeal this }
  haveI : Fintype ((Ideal.span {(l : ℤ_[l])}).primesOver (w.adicCompletionIntegers E)) :=
    Fintype.ofFinite _
  have h := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ_[l])})
    (w.adicCompletionIntegers E)
  rw [Fintype.sum_unique] at h
  have hd : ((default : (Ideal.span {(l : ℤ_[l])}).primesOver (w.adicCompletionIntegers E)) :
      Ideal (w.adicCompletionIntegers E)) = maximalIdeal (w.adicCompletionIntegers E) :=
    congrArg Subtype.val (Unique.eq_default (⟨_, hmem⟩ :
      (Ideal.span {(l : ℤ_[l])}).primesOver (w.adicCompletionIntegers E))).symm
  rw [hd] at h
  exact h.symm

private theorem ramificationIdx_mul_inertiaDeg_eq_one_of_splitsIn (hs : SplitsIn l E) :
    w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have hl : (l : ℕ).Prime := Fact.out
  haveI hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl)
  haveI : Fintype ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have hcard : Fintype.card ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hs
  have hge : ∀ q : (Ideal.span {(l : ℤ)}).primesOver (𝓞 E),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q
    haveI : q.1.IsPrime := q.2.1
    exact Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  let q0 : (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := ⟨w.asIdeal, w.isPrime, inferInstance⟩
  by_contra hne
  have hlt : ∑ _q : (Ideal.span {(l : ℤ)}).primesOver (𝓞 E), (1 : ℕ) <
      ∑ q : (Ideal.span {(l : ℤ)}).primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
    Finset.sum_lt_sum (fun q _ => hge q) ⟨q0, Finset.mem_univ _, lt_of_le_of_ne (hge q0) (Ne.symm hne)⟩
  rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hcard] at hlt
  exact lt_irrefl _ hlt

theorem finrank_compl [Algebra ℚ_[l] (w.adicCompletion E)]
    [ContinuousSMul ℚ_[l] (w.adicCompletion E)] :
    Module.Finite ℚ_[l] (w.adicCompletion E) ∧
      Module.finrank ℚ_[l] (w.adicCompletion E) =
        w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ ∧
      (SplitsIn l E → Function.Bijective (algebraMap ℚ_[l] (w.adicCompletion E))) := by
  obtain ⟨f, F, -, -, hFf, -, huF⟩ := existsUnique_padic_hom w l
  have hF : algebraMap ℚ_[l] (w.adicCompletion E) = F :=
    huF _ (continuous_algebraMap ℚ_[l] (w.adicCompletion E))
  letI : Algebra ℤ_[l] (w.adicCompletionIntegers E) := f.toAlgebra
  letI : Algebra ℤ_[l] (w.adicCompletion E) :=
    ((algebraMap ℚ_[l] (w.adicCompletion E)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (w.adicCompletion E) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ_[l] (w.adicCompletionIntegers E) (w.adicCompletion E) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap ℚ_[l] (w.adicCompletion E) (x : ℚ_[l]) =
        ((f x : w.adicCompletionIntegers E) : w.adicCompletion E)
      rw [hF, hFf]
  obtain ⟨-, -, -, hrank⟩ := finrank_complIntegers w l
  have hK : Module.finrank ℚ_[l] (w.adicCompletion E) =
      Module.finrank ℤ_[l] (w.adicCompletionIntegers E) :=
    IsFractionRing.finrank_eq ℤ_[l] ℚ_[l] (w.adicCompletionIntegers E) (w.adicCompletion E)
  have hpos : 0 < Module.finrank ℚ_[l] (w.adicCompletion E) := by
    rw [hK, hrank]
    exact Nat.mul_pos (Ideal.ramificationIdx_pos w.asIdeal ℤ) (Ideal.inertiaDeg_pos w.asIdeal ℤ)
  haveI : Module.Finite ℚ_[l] (w.adicCompletion E) := Module.finite_of_finrank_pos hpos
  refine ⟨inferInstance, hK.trans hrank, fun hs => ?_⟩
  have h1 : Module.finrank ℚ_[l] (w.adicCompletion E) = 1 := by
    rw [hK, hrank, ramificationIdx_mul_inertiaDeg_eq_one_of_splitsIn w l hs]
  refine ⟨(algebraMap ℚ_[l] (w.adicCompletion E)).injective, fun x => ?_⟩
  have htop := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hx : x ∈ (⊥ : Subalgebra ℚ_[l] (w.adicCompletion E)) := by
    rw [htop]
    trivial
  obtain ⟨q, hq⟩ := Algebra.mem_bot.1 hx
  exact ⟨q, hq⟩

end KStar.Ram
