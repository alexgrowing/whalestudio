import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeEqBotOrMaximalIdealOfIsFieldAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

namespace GlobalTheory

open IsLocalRing TensorProduct

section Nakayama

theorem finite_of_isHausdorff_of_finite_quotient {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [IsHausdorff I M]
    [Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))] : Module.Finite R M := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ (I • ⊤ : Submodule R M))
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • ⊤ : Submodule R M).mkQ g
    (Submodule.mkQ_surjective _)
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I (Fin n → R)
  exact Module.Finite.of_surjective f
    (surjective_of_mkQ_comp_surjective (I := I) (by rw [hf]; exact hg))

theorem finite_of_forall_prime_mem {R B : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra R B] [Finite (B ⧸ maximalIdeal B)] {f : B} (hf : f ≠ 0)
    (H : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → f ∈ P)
    (h0 : (maximalIdeal R).map (algebraMap R B) ≠ ⊥)
    (h1 : (maximalIdeal R).map (algebraMap R B) ≠ ⊤) : Module.Finite R B := by
  set J := (maximalIdeal R).map (algebraMap R B) with hJ
  have hrad : maximalIdeal B ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun q hq => ?_
    rcases prime_eq_bot_or_maximalIdeal_of_forall_mem hf H hq.2 with h | h
    · exact absurd (le_bot_iff.mp (h ▸ hq.1)) h0
    · exact h.ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal B)) n
  haveI : Finite (B ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)
  haveI : IsHausdorff J B := IsHausdorff.of_isLocalRing _ _ h1
  haveI : IsHausdorff (maximalIdeal R) B := IsHausdorff.map_algebraMap_iff.mp this
  haveI : Finite (B ⧸ (maximalIdeal R • ⊤ : Submodule R B)) := by
    rw [Ideal.smul_top_eq_map]
    exact ‹Finite (B ⧸ J)›
  exact finite_of_isHausdorff_of_finite_quotient (maximalIdeal R) B

end Nakayama

section Core

theorem exists_prime_notMem_forall_mem {A : Type*} [CommRing A] [IsNoetherianRing A] {f : A}
    {q : Ideal A} (hq : q.IsPrime) (hf : f ∉ q) : ∃ Q : Ideal A, Q.IsPrime ∧ f ∉ Q ∧
      ∀ P : Ideal (A ⧸ Q), P.IsPrime → P ≠ ⊥ → Ideal.Quotient.mk Q f ∈ P := by
  obtain ⟨Q, hQ, hmax⟩ := set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian A A)
    {Q : Ideal A | Q.IsPrime ∧ f ∉ Q} ⟨q, hq, hf⟩
  refine ⟨Q, hQ.1, hQ.2, fun P hP hP0 => ?_⟩
  by_contra h
  refine hmax (P.comap (Ideal.Quotient.mk Q)) ⟨Ideal.IsPrime.comap _, h⟩ ?_
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff P).mp hP0
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine SetLike.lt_iff_le_and_exists.mpr ⟨fun a ha => ?_, x, hx,
    fun hxQ => hx0 (Ideal.Quotient.eq_zero_iff_mem.mpr hxQ)⟩
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact P.zero_mem

theorem exists_prime_finite_quotient_atPrime {R A : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    (m : Ideal A) [m.IsMaximal] [Finite (A ⧸ m)]
    (hm : (maximalIdeal R).map (algebraMap R A) ≤ m) {q : Ideal A} (hq : q.IsPrime) (hqm : q ≤ m)
    {ϖ : R} (hϖ : ϖ ∈ maximalIdeal R) {f : A} (hf : algebraMap R A ϖ * f ∉ q) :
    ∃ Q : Ideal (Localization.AtPrime m), Q.IsPrime ∧
      algebraMap A _ (algebraMap R A ϖ * f) ∉ Q ∧ Module.Finite R (Localization.AtPrime m ⧸ Q) := by
  set L := Localization.AtPrime m
  have hdis : Disjoint (m.primeCompl : Set A) (q : Set A) :=
    Set.disjoint_left.mpr fun x hx hxq => hx (hqm hxq)
  have hq' : (q.map (algebraMap A L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl L q hq hdis
  have hf' : algebraMap A L (algebraMap R A ϖ * f) ∉ q.map (algebraMap A L) := by
    rw [← Ideal.mem_comap]
    have := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl L hq hdis
    rw [Ideal.under_def] at this
    rwa [this]
  obtain ⟨Q, hQ, hfQ, H⟩ := exists_prime_notMem_forall_mem hq' hf'
  refine ⟨Q, hQ, hfQ, ?_⟩
  haveI : IsLocalRing (L ⧸ Q) :=
    .of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  haveI hloc : IsLocalHom (Ideal.Quotient.mk Q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (ResidueField L) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal m L).toEquiv
  haveI : Finite ((L ⧸ Q) ⧸ maximalIdeal (L ⧸ Q)) := by
    refine Finite.of_surjective (ResidueField.map (Ideal.Quotient.mk Q)) fun x => ?_
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨residue L x, rfl⟩
  have hf0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hfQ
  refine finite_of_forall_prime_mem hf0 H (fun h => hf0 ?_) (fun h => ?_)
  · have h1 := Ideal.mem_map_of_mem (algebraMap R (L ⧸ Q)) hϖ
    rw [h, Ideal.mem_bot] at h1
    rw [map_mul, map_mul]
    exact mul_eq_zero_of_left h1 _
  · refine (maximalIdeal.isMaximal (L ⧸ Q)).ne_top (top_le_iff.mp (h ▸ ?_))
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have h1 : algebraMap A L (algebraMap R A r) ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L m _).mpr
        (hm (Ideal.mem_map_of_mem _ hr))
    exact map_nonunit (Ideal.Quotient.mk Q) _ h1

end Core

section Integers

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

instance finite_integralClosure_padicInt : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _

instance isDiscreteValuationRing_integralClosure_padicInt :
    IsDiscreteValuationRing (integralClosure ℤ_[p] K) :=
  ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] K

instance isFractionRing_integralClosure_padicInt : IsFractionRing (integralClosure ℤ_[p] K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

variable {p K}

omit [FiniteDimensional ℚ_[p] K] in
theorem charZero_integralClosure_padicInt : CharZero (integralClosure ℤ_[p] K) :=
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  inferInstance

omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in

theorem isLocalHom_of_injective_integralClosure {B : Type*} [CommRing B] [Algebra ℤ_[p] B]
    (g : B →ₐ[ℤ_[p]] integralClosure ℤ_[p] K) (hg : Function.Injective g) :
    IsLocalHom (g : B →+* integralClosure ℤ_[p] K) := by
  refine RingHom.IsIntegral.isLocalHom ?_ hg
  refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[p] B) _ ?_
  rw [g.comp_algebraMap]
  exact fun x => (Algebra.IsIntegral.isIntegral x : IsIntegral ℤ_[p] x)

theorem natCast_mem_maximalIdeal_integralClosure :
    (p : integralClosure ℤ_[p] K) ∈ maximalIdeal (integralClosure ℤ_[p] K) := by
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[p] ℚ_[p] K
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[p] K
  have : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  simpa using map_nonunit (algebraMap ℤ_[p] (integralClosure ℤ_[p] K)) _ this

variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L] in
theorem mapIntegralClosure_padicInt_injective (σ : K →ₐ[ℚ_[p]] L) :
    Function.Injective (σ.restrictScalars ℤ_[p]).mapIntegralClosure := fun _ _ h =>
  Subtype.ext (σ.toRingHom.injective (congrArg Subtype.val h))

theorem comap_maximalIdeal_mapIntegralClosure (σ : K →ₐ[ℚ_[p]] L) :
    (maximalIdeal (integralClosure ℤ_[p] L)).comap
        ((σ.restrictScalars ℤ_[p]).mapIntegralClosure :
          integralClosure ℤ_[p] K →+* integralClosure ℤ_[p] L) =
      maximalIdeal (integralClosure ℤ_[p] K) := by
  haveI := isLocalHom_of_injective_integralClosure _ (mapIntegralClosure_padicInt_injective σ)
  exact maximalIdeal_comap _

theorem isIntegral_padicInt_iff_norm_le_one (x : PadicAlgCl p) :
    IsIntegral ℤ_[p] x ↔ ‖x‖ ≤ 1 := by
  have hx : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] h, Polynomial.coeff_map]
    exact ((minpoly ℤ_[p] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem mem_integralClosure_padicInt_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : K) :
    x ∈ integralClosure ℤ_[p] K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  rw [← isIntegral_padicInt_iff_norm_le_one, mem_integralClosure_iff]
  exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[p]) K.val.toRingHom.injective).symm

theorem mem_maximalIdeal_integralClosure_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (x : integralClosure ℤ_[p] K) :
    x ∈ maximalIdeal (integralClosure ℤ_[p] K) ↔ ‖((x : K) : PadicAlgCl p)‖ < 1 := by
  have hle := fun y : integralClosure ℤ_[p] K => (mem_integralClosure_padicInt_iff K y).mp y.2
  rw [mem_maximalIdeal, mem_nonunits_iff, ← not_le]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, hy⟩ := h.exists_right_inv
    have h1 : ‖((x : K) : PadicAlgCl p)‖ * ‖((y : K) : PadicAlgCl p)‖ = 1 := by
      rw [← norm_mul]
      have : ((x : K) : PadicAlgCl p) * ((y : K) : PadicAlgCl p) = 1 := by
        exact_mod_cast congrArg (fun z : integralClosure ℤ_[p] K => ((z : K) : PadicAlgCl p)) hy
      rw [this, norm_one]
    calc 1 = _ := h1.symm
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (hle y)
  · have h0 : (x : K) ≠ 0 := by
      intro h0
      rw [h0] at h
      norm_num at h
    have hinv : (x : K)⁻¹ ∈ integralClosure ℤ_[p] K := by
      rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ h
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))

theorem exists_injective_algHom_integralClosure (B : Type*) [CommRing B] [IsDomain B]
    [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] (hp : (p : B) ≠ 0) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (g : B →ₐ[ℤ_[p]] integralClosure ℤ_[p] K), Function.Injective g := by
  classical
  have hinj : Function.Injective (algebraMap ℤ_[p] B) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0
      (PadicInt.irreducible_p (p := p))
    rw [map_mul, map_pow, map_natCast] at ha
    exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero n hp) ha
  haveI : FaithfulSMul ℤ_[p] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : FaithfulSMul ℤ_[p] (PadicAlgCl p) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective _ _))
  let φ : B →ₐ[ℤ_[p]] PadicAlgCl p := IsAlgClosed.lift
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have : (RingHom.ker φ).comap (algebraMap ℤ_[p] B) = ⊥ := by
      refine eq_bot_iff.mpr fun a ha => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, φ.commutes] at ha
      exact (FaithfulSMul.algebraMap_injective ℤ_[p] (PadicAlgCl p)) (by simpa using ha)
    have h := Ideal.eq_bot_of_comap_eq_bot this
    exact (Ideal.mem_bot.mp (h ▸ (RingHom.mem_ker.mpr hb : b ∈ RingHom.ker φ)))
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := B)
  let K := IntermediateField.adjoin ℚ_[p] ((s.image φ : Finset _) : Set (PadicAlgCl p))
  haveI : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ b, φ b ∈ K := by
    intro b
    have hb : b ∈ Submodule.span ℤ_[p] (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact K.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact K.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, ← algebraMap_smul ℚ_[p]]
      exact K.smul_mem hx
  let ψ : B →ₐ[ℤ_[p]] K :=
    { toFun := fun b => ⟨φ b, hmem b⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (map_add φ a b)
      commutes' := fun a => Subtype.ext (φ.commutes a) }
  refine ⟨K, inferInstance, ψ.codRestrict (integralClosure ℤ_[p] K) fun b =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) b).map ψ, fun a b h => hφ ?_⟩
  exact congrArg (fun z : integralClosure ℤ_[p] K => ((z : K) : PadicAlgCl p)) h

end Integers

section Affine

theorem finite_quotient_of_finiteType_int {A : Type*} [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : Finite (A ⧸ m) := by
  letI := Ideal.Quotient.field m
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ _
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ m)
  have hp0 : p ≠ 0 := by
    rintro rfl
    haveI := CharP.charP_to_charZero (A ⧸ m)
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (algebraMap ℤ (A ⧸ m)).injective_int (Field.toIsField _))
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero (A ⧸ m) p).resolve_right hp0⟩
  letI := ZMod.algebra (A ⧸ m) p
  haveI : Module.Finite (ZMod p) (A ⧸ m) := Module.Finite.of_restrictScalars_finite ℤ _ _
  exact Module.finite_of_finite (ZMod p)

theorem exists_prime_natCast_mem_of_finiteType_int {A : Type*} [CommRing A]
    [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] : ∃ p : ℕ, p.Prime ∧ (p : A) ∈ m := by
  letI := Ideal.Quotient.field m
  haveI := finite_quotient_of_finiteType_int m
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ m)
  refine ⟨p, (CharP.char_is_prime_or_zero (A ⧸ m) p).resolve_right
    (CharP.char_ne_zero_of_finite (A ⧸ m) p), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]

variable {p : ℕ} [Fact p.Prime]

theorem exists_padicInt_algHom_comap_eq {A : Type*} [CommRing A] [IsNoetherianRing A]
    [Algebra ℤ_[p] A] (m : Ideal A) [m.IsMaximal] [Finite (A ⧸ m)] (hp : (p : A) ∈ m)
    {q : Ideal A} (hq : q.IsPrime) (hqm : q ≤ m) {f : A} (hf : (p : A) * f ∉ q) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (y : A →ₐ[ℤ_[p]] integralClosure ℤ_[p] K),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 := by
  have hm : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) ≤ m := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.span_singleton_le_iff_mem]
    exact hp
  have hϖ : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  obtain ⟨Q, hQ, hfQ, hfin⟩ := exists_prime_finite_quotient_atPrime m hm hq hqm hϖ (f := f)
    (by rwa [map_natCast])
  set L := Localization.AtPrime m
  have hf0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hfQ
  rw [map_natCast, map_mul, map_mul, map_natCast, map_natCast] at hf0
  obtain ⟨K, hK, g, hg⟩ := exists_injective_algHom_integralClosure (p := p) (L ⧸ Q)
    (left_ne_zero_of_mul hf0)
  haveI : IsLocalRing (L ⧸ Q) :=
    .of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk Q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI := isLocalHom_of_injective_integralClosure g hg
  refine ⟨K, hK, g.comp ((Ideal.Quotient.mkₐ ℤ_[p] Q).comp (IsScalarTower.toAlgHom ℤ_[p] A L)),
    ?_, fun h => right_ne_zero_of_mul hf0 (hg (h.trans (map_zero g).symm))⟩
  ext a
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff L m,
    ← maximalIdeal_comap (Ideal.Quotient.mk Q),
    ← maximalIdeal_comap (g : L ⧸ Q →+* integralClosure ℤ_[p] K)]
  rfl

theorem exists_padic_point {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m) {f : A} (hf : f ≠ 0) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (y : A →+* integralClosure ℤ_[p] K),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 := by
  letI := Ideal.Quotient.field m
  haveI := finite_quotient_of_finiteType_int m
  haveI : CharP (A ⧸ m) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]; exact hp)
  letI : Algebra ℤ_[p] (A ⊗[ℤ] ℤ_[p]) := Algebra.TensorProduct.rightAlgebra
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] A) := Algebra.FiniteType.isNoetherianRing ℤ_[p] _
  haveI : IsNoetherianRing (A ⊗[ℤ] ℤ_[p]) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm ℤ ℤ_[p] A).toRingEquiv
  let ρ : A ⊗[ℤ] ℤ_[p] →ₐ[A] A ⧸ m := Algebra.TensorProduct.lift (Algebra.ofId A (A ⧸ m))
    ((ZMod.castHom (dvd_refl p) (A ⧸ m)).comp PadicInt.toZMod).toIntAlgHom
    fun _ _ => Commute.all _ _
  have hρ : Function.Surjective ρ := fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨algebraMap A _ a, ρ.commutes a⟩
  let m' : Ideal (A ⊗[ℤ] ℤ_[p]) := RingHom.ker ρ
  haveI : m'.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hρ
  haveI : Finite ((A ⊗[ℤ] ℤ_[p]) ⧸ m') :=
    Finite.of_equiv _ (Ideal.quotientKerAlgEquivOfSurjective hρ).symm.toEquiv
  have hmm : ∀ a : A, algebraMap A (A ⊗[ℤ] ℤ_[p]) a ∈ m' ↔ a ∈ m := fun a => by
    rw [RingHom.mem_ker, ρ.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem
  haveI : m'.LiesOver m := ⟨Ideal.ext fun a => (hmm a).symm⟩
  obtain ⟨q, hqm, hq, hq0⟩ := m'.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal A)) (q := m)
    bot_le
  obtain ⟨K, hK, y, hy, hyf⟩ := exists_padicInt_algHom_comap_eq (p := p) m'
    (by rw [← map_natCast (algebraMap A (A ⊗[ℤ] ℤ_[p])), hmm]; exact hp) hq hqm
    (f := algebraMap A _ f) (by
      rw [← map_natCast (algebraMap A (A ⊗[ℤ] ℤ_[p])), ← map_mul,
        ← Ideal.mem_of_liesOver q (⊥ : Ideal A), Ideal.mem_bot]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hf)
  refine ⟨K, hK, y.toRingHom.comp (algebraMap A _), ?_, hyf⟩
  ext a
  rw [← hmm, ← hy]
  rfl

theorem padic_point_comp {A : Type*} [CommRing A] {K L : Type*}
    [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] (σ : K →ₐ[ℚ_[p]] L)
    (y : A →+* integralClosure ℤ_[p] K) :
    (maximalIdeal (integralClosure ℤ_[p] L)).comap
        ((σ.restrictScalars ℤ_[p]).mapIntegralClosure.toRingHom.comp y) =
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y ∧
    RingHom.ker ((σ.restrictScalars ℤ_[p]).mapIntegralClosure.toRingHom.comp y) =
      RingHom.ker y := by
  refine ⟨by rw [← Ideal.comap_comap, ← comap_maximalIdeal_mapIntegralClosure σ]; rfl, ?_⟩
  exact RingHom.ker_comp_of_injective y (mapIntegralClosure_padicInt_injective σ)

theorem exists_padic_point_forall_ge {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m) {f : A} (hf : f ≠ 0) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ y : A →+* integralClosure ℤ_[p] K,
          (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 := by
  obtain ⟨K₀, hK₀, y, hy, hyf⟩ := exists_padic_point m hp hf
  refine ⟨K₀, hK₀, fun K _ h => ?_⟩
  obtain ⟨h1, h2⟩ := padic_point_comp (IntermediateField.inclusion h) y
  refine ⟨_, h1.trans hy, fun h0 => hyf ?_⟩
  rw [← RingHom.mem_ker, ← h2]
  exact h0

end Affine

section Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem finiteType_int_sections {Z : Scheme.{0}} (π : Z ⟶ Spec (.of ℤ)) [LocallyOfFiniteType π]
    {V : Z.Opens} (hV : IsAffineOpen V) : Algebra.FiniteType ℤ Γ(Z, V) := by
  have h := HasRingHomProperty.appLE @LocallyOfFiniteType π inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have h' := h.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (.of ℤ)).inv.hom
    (Scheme.ΓSpecIso (.of ℤ)).symm.commRingCatIsoToRingEquiv.surjective)
  rw [← RingHom.finiteType_algebraMap]
  convert h' using 1
  exact RingHom.ext_int _ _

theorem charZero_sections_of_flat {Z : Scheme.{0}} [IsIntegral Z] (π : Z ⟶ Spec (.of ℤ)) [Flat π]
    {V : Z.Opens} (hV : IsAffineOpen V) [Nonempty V] : CharZero Γ(Z, V) := by
  have h := HasRingHomProperty.appLE @Flat π inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have h' := (RingHom.Flat.of_bijective (f := (Scheme.ΓSpecIso (.of ℤ)).inv.hom)
    (Scheme.ΓSpecIso (.of ℤ)).symm.commRingCatIsoToRingEquiv.bijective).comp h
  have h'' : (algebraMap ℤ Γ(Z, V)).Flat := by
    convert h' using 1
    exact RingHom.ext_int _ _
  haveI := RingHom.flat_algebraMap_iff.mp h''
  refine ⟨fun a b hab => ?_⟩
  have := FaithfulSMul.algebraMap_injective ℤ Γ(Z, V) (a₁ := a) (a₂ := b) (by simpa using hab)
  exact_mod_cast this

theorem mem_primeIdealOf_iff_evaluation_eq_zero {Z : Scheme.{0}} {V : Z.Opens}
    (hV : IsAffineOpen V) {z : Z} (hz : z ∈ V) (a : Γ(Z, V)) :
    a ∈ (hV.primeIdealOf ⟨z, hz⟩).asIdeal ↔ Z.evaluation V z hz a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, ← not_iff_not, not_not,
    ← PrimeSpectrum.mem_basicOpen, ← hV.fromSpec_preimage_basicOpen]
  change hV.fromSpec (hV.primeIdealOf ⟨z, hz⟩) ∈ Z.basicOpen a ↔ _
  rw [hV.fromSpec_primeIdealOf]

theorem exists_prime_residueField_eq_zero {Z : Scheme.{0}} (π : Z ⟶ Spec (.of ℤ))
    [LocallyOfFiniteType π] {z : Z} (hz : IsClosed ({z} : Set Z)) :
    ∃ p : ℕ, p.Prime ∧ (p : Z.residueField z) = 0 := by
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  haveI := finiteType_int_sections π hV
  haveI := hV.primeIdealOf_isMaximal_of_isClosed ⟨z, hzV⟩ hz
  obtain ⟨p, hp, hpm⟩ :=
    exists_prime_natCast_mem_of_finiteType_int (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
  exact ⟨p, hp, by simpa using (mem_primeIdealOf_iff_evaluation_eq_zero hV hzV _).mp hpm⟩

variable {p : ℕ} [Fact p.Prime]

theorem apply_genericPoint_eq_of_charZero {R : CommRingCat.{0}} [IsDomain R] [CharZero R]
    (g : Spec R ⟶ Spec (.of ℤ)) : g (genericPoint (Spec R)) = genericPoint (Spec (.of ℤ)) := by
  have : g = Spec.map (CommRingCat.ofHom (Int.castRingHom R)) := specZIsTerminal.hom_ext _ _
  rw [this, genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  refine PrimeSpectrum.ext ?_
  exact Ideal.comap_bot_of_injective (Int.castRingHom R) Int.cast_injective

theorem exists_padic_point_scheme_forall_ge {Z : Scheme.{0}} [IsIntegral Z]
    (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π] {z : Z} (hz : IsClosed ({z} : Set Z))
    (hp : (p : Z.residueField z) = 0) (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z,
          y (closedPoint (integralClosure ℤ_[p] K)) = z ∧ y (genericPoint _) ∈ U ∧
            π (y (genericPoint _)) = genericPoint _ := by
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  haveI := finiteType_int_sections π hV
  haveI := charZero_sections_of_flat π hV
  haveI := hV.primeIdealOf_isMaximal_of_isClosed ⟨z, hzV⟩ hz
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hU ⟨z, hzV⟩
  obtain ⟨f, hfU, hxf⟩ := hV.exists_basicOpen_le (V := U) ⟨x, hxU⟩ hxV
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hxf
  obtain ⟨K₀, hK₀, H⟩ := exists_padic_point_forall_ge (p := p)
    (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
    ((mem_primeIdealOf_iff_evaluation_eq_zero hV hzV _).mpr (by simpa using hp)) hf
  refine ⟨K₀, hK₀, fun K _ h => ?_⟩
  obtain ⟨y, hy, hyf⟩ := H K h
  refine ⟨Spec.map (CommRingCat.ofHom y) ≫ hV.fromSpec, ?_, ?_, ?_⟩
  · refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    exact (congrArg hV.fromSpec (PrimeSpectrum.ext hy)).trans (hV.fromSpec_primeIdealOf ⟨z, hzV⟩)
  · apply hfU
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen,
      genericPoint_eq_bot_of_affine]
    exact hyf
  · haveI : CharZero (integralClosure ℤ_[p] K) := charZero_integralClosure_padicInt
    rw [← Scheme.Hom.comp_apply]
    exact apply_genericPoint_eq_of_charZero _

theorem exists_padic_point_scheme {Z : Scheme.{0}} [IsIntegral Z]
    (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π] {z : Z} (hz : IsClosed ({z} : Set Z))
    (hp : (p : Z.residueField z) = 0) (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z),
        y (closedPoint (integralClosure ℤ_[p] K)) = z ∧ y (genericPoint _) ∈ U ∧
          π (y (genericPoint _)) = genericPoint _ := by
  obtain ⟨K, hK, H⟩ := exists_padic_point_scheme_forall_ge π hz hp U hU
  exact ⟨K, hK, H K le_rfl⟩

end Scheme

example (p : ℕ) [Fact p.Prime] : ∃ m : Ideal (Polynomial ℤ), m.IsMaximal ∧
    (p : Polynomial ℤ) ∈ m ∧ Polynomial.X ∈ m := by
  let φ : Polynomial ℤ →+* ZMod p := Polynomial.eval₂RingHom (Int.castRingHom _) 0
  refine ⟨RingHom.ker φ, RingHom.ker_isMaximal_of_surjective φ fun x => ?_, ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨n, map_intCast φ n⟩
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker, φ]

end GlobalTheory
