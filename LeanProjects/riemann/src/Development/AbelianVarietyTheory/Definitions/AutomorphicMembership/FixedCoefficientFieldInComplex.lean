import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.RootValueClassBasis

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Chr
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

section Ray

def IsRayField (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)) :
    Prop :=
  IsAbelianGalois K L ∧
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) ∧
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
    ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
      ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
        ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

theorem rayField_iff : RayField ↔ ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L), IsRayField K L 𝔮 := by
  refine forall₃_congr fun K _ _ => forall₂_congr fun 𝔮 _ => ?_
  constructor
  · rintro ⟨L, _, _, _, h, h'⟩
    exact ⟨L, _, inferInstance, _, h, h'⟩
  · rintro ⟨L, _, _, _, h, h'⟩
    exact ⟨L, _, inferInstance, _, h, h'⟩

variable {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field L'] [NumberField L'] [Algebra K L']

omit [NumberField K] [NumberField L] [NumberField L'] in

theorem exists_prime_congr (e : L ≃ₐ[K] L') (𝔭 : Ideal (𝓞 K)) (σ : L ≃ₐ[K] L) (n : ℕ)
    (h : ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver 𝔭 ∧ ∀ x : 𝓞 L, σ • x - x ^ n ∈ P) :
    ∃ P : Ideal (𝓞 L'), P.IsPrime ∧ P.LiesOver 𝔭 ∧ ∀ x : 𝓞 L', e.autCongr σ • x - x ^ n ∈ P := by
  obtain ⟨P, hP, hPo, hx⟩ := h
  let f : 𝓞 L' ≃ₐ[𝓞 K] 𝓞 L := RingOfIntegers.mapAlgEquiv e.symm
  refine ⟨P.comap f, inferInstance, inferInstance, fun x => ?_⟩
  have h1 : f (e.autCongr σ • x) = σ • f x := by
    apply RingOfIntegers.ext
    change e.symm (e (σ (e.symm x))) = σ (e.symm x)
    rw [e.symm_apply_apply]
  rw [Ideal.mem_comap, map_sub, map_pow, h1]
  exact hx _

omit [NumberField L] [NumberField L'] in

theorem isFrob_congr (e : L ≃ₐ[K] L') (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) :
    IsFrob L' 𝔭 (e.autCongr σ) ↔ IsFrob L 𝔭 σ := by
  refine ⟨fun h => ?_, exists_prime_congr e _ σ _⟩
  have h1 := exists_prime_congr e.symm _ _ _ h
  rwa [show e.symm.autCongr (e.autCongr σ) = σ from e.autCongr.symm_apply_apply σ] at h1

omit [NumberField K] [NumberField L] [NumberField L'] in

theorem inInertia_congr (e : L ≃ₐ[K] L') (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) :
    InInertia L' 𝔭 (e.autCongr σ) ↔ InInertia L 𝔭 σ := by
  constructor
  · intro h
    have h1 := exists_prime_congr e.symm 𝔭.asIdeal (e.autCongr σ) 1 (by simpa only [pow_one, InInertia] using h)
    rw [show e.symm.autCongr (e.autCongr σ) = σ from e.autCongr.symm_apply_apply σ] at h1
    simpa only [pow_one, InInertia] using h1
  · intro h
    simpa only [pow_one, InInertia] using exists_prime_congr e 𝔭.asIdeal σ 1 (by simpa only [pow_one, InInertia] using h)

theorem heckeVal_congr [IsGalois K L] [IsGalois K L'] (e : L ≃ₐ[K] L') (χ : (L' ≃ₐ[K] L') →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) : heckeVal L (χ.comp e.autCongr.toMonoidHom) 𝔭 = heckeVal L' χ 𝔭 := by
  by_cases h : ∀ τ, InInertia L' 𝔭 τ → χ τ = 1
  · obtain ⟨σ, hσ⟩ := exists_isFrob L 𝔭
    rw [heckeVal_eq L _ 𝔭 (fun τ hτ => h _ ((inInertia_congr e 𝔭 τ).2 hτ)) hσ,
      heckeVal_eq L' χ 𝔭 h ((isFrob_congr e 𝔭 σ).2 hσ)]
    rfl
  · rw [heckeVal_eq_zero L' χ 𝔭 h, heckeVal_eq_zero L _ 𝔭 fun h' => h fun τ hτ => ?_]
    obtain ⟨σ, rfl⟩ := e.autCongr.surjective τ
    exact h' σ ((inInertia_congr e 𝔭 σ).1 hτ)

theorem IsRayField.of_algEquiv {𝔮 : Ideal (𝓞 K)} (h : IsRayField K L 𝔮) (e : L ≃ₐ[K] L') : IsRayField K L' 𝔮 := by
  obtain ⟨hab, hun, hgen, hart⟩ := h
  have hab' : IsAbelianGalois K L' := IsAbelianGalois.of_algHom (e.symm : L' →ₐ[K] L)
  refine ⟨hab', fun 𝔭 h𝔭 τ hτ => ?_, ?_, fun I hI hc => ?_⟩
  · obtain ⟨σ, rfl⟩ := e.autCongr.surjective τ
    rw [hun 𝔭 h𝔭 σ ((inInertia_congr e 𝔭 σ).1 hτ), map_one]
  · rw [eq_top_iff, ← Subgroup.map_top_of_surjective e.autCongr.toMonoidHom e.autCongr.surjective, ← hgen,
      MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨σ, ⟨𝔭, h𝔭, hσ⟩, rfl⟩
    exact ⟨𝔭, h𝔭, (isFrob_congr e 𝔭 σ).2 hσ⟩
  · rw [← hart I hI hc]
    have key : ∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, heckeIdeal L (χ.comp e.autCongr.toMonoidHom) I = heckeIdeal L' χ I :=
      fun χ => by simp only [heckeIdeal, heckeVal_congr]
    refine ⟨fun h χ => ?_, fun h χ => key χ ▸ h _⟩
    rw [← h (χ.comp e.autCongr.symm.toMonoidHom), ← key]
    congr 1
    exact MonoidHom.ext fun σ => (congrArg χ (e.autCongr.symm_apply_apply σ)).symm

theorem isRayField_rat_top : IsRayField ℚ ℚ ⊤ := by
  refine ⟨inferInstance, fun _ _ σ _ => Subsingleton.elim _ _, Subsingleton.elim _ _, fun I hI _ => ?_⟩
  refine iff_of_true (fun χ => ?_) ?_
  · rw [Subsingleton.elim χ 1]
    simp [heckeIdeal, heckeVal_one]
  · have : IsPrincipalIdealRing (𝓞 ℚ) :=
      IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ).toRingHom
        Rat.ringOfIntegersEquiv.symm.surjective
    obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
    have ha : a ≠ 0 := fun h => hI (by simp [h])
    have ha' : (a : ℚ) ≠ 0 := fun h => ha (RingOfIntegers.ext h)
    have hc : ∀ J : Ideal (𝓞 ℚ), IsCoprime J ⊤ := fun J => by
      rw [← Ideal.one_eq_top]; exact isCoprime_one_right
    rcases lt_or_gt_of_ne ha' with h | h
    · refine ⟨-a, 1, ⟨neg_ne_zero.2 ha, one_ne_zero, hc _, hc _, trivial, fun φ => ?_⟩, ?_⟩
      · simpa using h
      · simp [Ideal.span_singleton_neg]
    · refine ⟨a, 1, ⟨ha, one_ne_zero, hc _, hc _, trivial, fun φ => ?_⟩, ?_⟩
      · simpa using h
      · simp

theorem not_isRayField_rat_three : ¬ IsRayField ℚ ℚ (Ideal.span {3}) := by
  intro h
  let e := Rat.ringOfIntegersEquiv
  have hco : IsCoprime (2 : 𝓞 ℚ) 3 := ⟨-1, 1, by norm_num⟩
  obtain ⟨α, β, ⟨-, -, -, hβ, hm, hpos⟩, hI⟩ := (h.2.2.2 (Ideal.span {2}) (by simp)
    ((Ideal.isCoprime_span_singleton_iff _ _).2 hco)).1 fun χ => by
      rw [Subsingleton.elim χ 1]
      simp [heckeIdeal, heckeVal_one]
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_span_singleton] at hI
  have h1 := Int.associated_iff.1 (hI.map e)
  have h2 := ((Ideal.isCoprime_span_singleton_iff _ _).1 hβ).map e.toRingHom
  have h3 := map_dvd e (Ideal.mem_span_singleton.1 hm)
  have h4 : (0 : ℚ) < ((e α * e β : ℤ) : ℚ) := by
    have := hpos (algebraMap ℚ ℝ)
    rw [← map_mul, eq_ratCast, Rat.cast_pos] at this
    rwa [Int.cast_mul, Rat.ringOfIntegersEquiv_apply_coe, Rat.ringOfIntegersEquiv_apply_coe]
  have h5 : 0 < e α * e β := by exact_mod_cast h4
  rw [map_mul, map_ofNat] at h1
  rw [map_sub, map_ofNat] at h3
  rw [map_ofNat] at h2
  have h6 : ¬ (3 : ℤ) ∣ e β := fun hd => by
    have := h2.isUnit_of_dvd' hd dvd_rfl
    rw [Int.isUnit_iff] at this
    omega
  rcases h1 with h1 | h1
  · omega
  · have : e α = -(2 * e β) := by omega
    rw [this] at h5
    nlinarith [sq_nonneg (e β)]

end Ray

section Sub

abbrev rootOne (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))

def cycField (N : ℕ) : IntermediateField ℚ ℂ := ℚ⟮rootOne N⟯

theorem cycField_le_iff {N : ℕ} {M : IntermediateField ℚ ℂ} : cycField N ≤ M ↔ rootOne N ∈ M :=
  IntermediateField.adjoin_simple_le_iff

theorem mem_cycField {N : ℕ} (hN : N ≠ 0) {z : ℂ} (hz : z ^ N = 1) : z ∈ cycField N := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp N hN).eq_pow_of_pow_eq_one hz
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

theorem cycField_mono {N N' : ℕ} (hN' : N' ≠ 0) (h : N ∣ N') : cycField N ≤ cycField N' :=
  cycField_le_iff.2 (mem_cycField hN'
    (((Complex.isPrimitiveRoot_exp N (ne_zero_of_dvd_ne_zero hN' h)).pow_eq_one_iff_dvd N').2 h))

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

def imField : IntermediateField ℚ ℂ := φ.toRatAlgHom.fieldRange

theorem mem_imField {z : ℂ} : z ∈ imField φ ↔ ∃ x, φ x = z := Iff.rfl

theorem imField_le_iff {M : IntermediateField ℚ ℂ} : imField φ ≤ M ↔ ∀ x, φ x ∈ M :=
  ⟨fun h x => h ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

@[instance_reducible] def algOf (M : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ M) : Algebra E M :=
  (φ.codRestrict M h).toAlgebra

omit [NumberField E] in

theorem algOf_apply (M : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ M) (x : E) :
    letI := algOf φ M h; ((algebraMap E M x : M) : ℂ) = φ x := rfl

def degOver (M : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ M) : ℕ := letI := algOf φ M h; Module.finrank E M

theorem finrank_mul_degOver (M : IntermediateField ℚ ℂ) (h : ∀ x, φ x ∈ M) :
    Module.finrank ℚ E * degOver φ M h = Module.finrank ℚ M := by
  let := algOf φ M h
  exact Module.finrank_mul_finrank ℚ E M

theorem degOver_pos (M : IntermediateField ℚ ℂ) [NumberField M] (h : ∀ x, φ x ∈ M) : 0 < degOver φ M h := by
  have h1 := finrank_mul_degOver φ M h
  have h2 : 0 < Module.finrank ℚ M := Module.finrank_pos
  exact Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at h1; omega

def IsRayFieldIn (𝔮 : Ideal (𝓞 E)) (M : IntermediateField ℚ ℂ) : Prop :=
  ∃ (h : ∀ x, φ x ∈ M) (_ : NumberField M), letI := algOf φ M h; IsRayField E M 𝔮

variable {φ} in

theorem IsRayFieldIn.emb_mem {𝔮 : Ideal (𝓞 E)} {M : IntermediateField ℚ ℂ} (h : IsRayFieldIn φ 𝔮 M) (x : E) :
    φ x ∈ M := h.1 x

variable {φ} in

theorem IsRayFieldIn.numberField {𝔮 : Ideal (𝓞 E)} {M : IntermediateField ℚ ℂ} (h : IsRayFieldIn φ 𝔮 M) :
    NumberField M := h.2.1

variable {φ} in

theorem IsRayFieldIn.isRayField {𝔮 : Ideal (𝓞 E)} {M : IntermediateField ℚ ℂ} [NumberField M]
    (h : IsRayFieldIn φ 𝔮 M) : letI := algOf φ M h.emb_mem; IsRayField E M 𝔮 := h.2.2

theorem IsRayField.exists_isRayFieldIn {L : Type} [Field L] [NumberField L] [Algebra E L] {𝔮 : Ideal (𝓞 E)}
    (h : IsRayField E L 𝔮) : ∃ M, IsRayFieldIn φ 𝔮 M := by
  let := φ.toAlgebra
  let ψ : L →ₐ[E] ℂ := IsAlgClosed.lift
  have hm : ∀ x, φ x ∈ imField (ψ : L →+* ℂ) := fun x => ⟨algebraMap E L x, ψ.commutes x⟩
  let e₀ : L ≃ₐ[ℚ] imField (ψ : L →+* ℂ) := AlgEquiv.ofInjectiveField (ψ : L →+* ℂ).toRatAlgHom
  have : FiniteDimensional ℚ (imField (ψ : L →+* ℂ)) := e₀.toLinearEquiv.finiteDimensional
  have hN : NumberField (imField (ψ : L →+* ℂ)) := NumberField.of_module_finite ℚ _
  let := algOf φ _ hm
  exact ⟨_, hm, hN, h.of_algEquiv
    (AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun x => Subtype.ext (ψ.commutes x))⟩

theorem exists_isRayFieldIn (h : RayField) {𝔮 : Ideal (𝓞 E)} (h𝔮 : 𝔮 ≠ ⊥) : ∃ M, IsRayFieldIn φ 𝔮 M := by
  obtain ⟨L, _, _, _, hL⟩ := rayField_iff.1 h E 𝔮 h𝔮
  exact hL.exists_isRayFieldIn φ

example : ∃ M, IsRayFieldIn (algebraMap ℚ ℂ) ⊤ M := isRayField_rat_top.exists_isRayFieldIn _

variable (E) in

abbrev natIdeal (n : ℕ) : Ideal (𝓞 E) := Ideal.span {(n : 𝓞 E)}

theorem natIdeal_ne_bot {n : ℕ} (hn : n ≠ 0) : natIdeal E n ≠ ⊥ := by
  simpa using hn

variable (E) in

def powIdealElts (h : ℕ) : Set E :=
  {y | y ≠ 0 ∧ ∃ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, FractionalIdeal.spanSingleton (𝓞 E)⁰ y = 𝔞 ^ h}

def kummerField (h : ℕ) : IntermediateField ℚ ℂ :=
  imField φ ⊔ cycField h ⊔ IntermediateField.adjoin ℚ {z | ∃ y ∈ powIdealElts E h, z ^ h = φ y}

theorem imField_le_kummerField (h : ℕ) : imField φ ≤ kummerField φ h := le_sup_left.trans le_sup_left

theorem cycField_le_kummerField (h : ℕ) : cycField h ≤ kummerField φ h := le_sup_right.trans le_sup_left

theorem mem_kummerField {h : ℕ} {y : E} (hy : y ∈ powIdealElts E h) {z : ℂ} (hz : z ^ h = φ y) :
    z ∈ kummerField φ h :=
  (le_sup_right : _ ≤ kummerField φ h) (IntermediateField.subset_adjoin ℚ _ ⟨y, hy, hz⟩)

theorem kummerField_le_iff {h : ℕ} {M : IntermediateField ℚ ℂ} : kummerField φ h ≤ M ↔
    (∀ x, φ x ∈ M) ∧ rootOne h ∈ M ∧ ∀ y ∈ powIdealElts E h, ∀ z : ℂ, z ^ h = φ y → z ∈ M := by
  rw [kummerField, sup_le_iff, sup_le_iff, imField_le_iff, cycField_le_iff, IntermediateField.adjoin_le_iff, and_assoc]
  exact and_congr_right' (and_congr_right' ⟨fun H y hy z hz => H ⟨y, hy, hz⟩, fun H z ⟨y, hy, hz⟩ => H y hy z hz⟩)

theorem pow_mem_powIdealElts {h : ℕ} {y : E} (hy : y ∈ powIdealElts E h) (k : ℕ) :
    y ^ k ∈ powIdealElts E (h * k) := by
  obtain ⟨h0, 𝔞, ha⟩ := hy
  exact ⟨pow_ne_zero _ h0, 𝔞, by rw [← FractionalIdeal.spanSingleton_pow, ha, pow_mul]⟩

theorem kummerField_mono {h h' : ℕ} (h0 : h' ≠ 0) (hd : h ∣ h') : kummerField φ h ≤ kummerField φ h' := by
  refine sup_le (sup_le (imField_le_kummerField φ _) ((cycField_mono h0 hd).trans (cycField_le_kummerField φ _))) ?_
  obtain ⟨k, rfl⟩ := hd
  rw [IntermediateField.adjoin_le_iff]
  rintro z ⟨y, hy, hz⟩
  exact mem_kummerField φ (pow_mem_powIdealElts hy k) (by rw [pow_mul, hz, map_pow])

theorem kummerField_one : kummerField φ 1 = imField φ := by
  refine le_antisymm ((kummerField_le_iff φ).2 ⟨fun x => ⟨x, rfl⟩, ?_, fun y _ z hz => ⟨y, ?_⟩⟩)
    (imField_le_kummerField φ 1)
  · have h : rootOne 1 = 1 := (pow_one _).symm.trans (Complex.isPrimitiveRoot_exp 1 one_ne_zero).pow_eq_one
    exact h ▸ one_mem _
  · rw [pow_one] at hz
    exact hz.symm

example : Complex.I ∈ kummerField φ 2 :=
  mem_kummerField φ (y := -1) ⟨by simp, 1, by
    rw [one_pow, ← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]
    exact ⟨-1, by simp⟩⟩ (by simp)

def valueSet (χ : HChar E) (s : ℝ) : Set ℂ := {z | ∃ v, χ.UnrAt v ∧ z = χ.valTw s v}

def valueField (χ : HChar E) (s : ℝ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (valueSet χ s)

theorem valueField_le_iff {χ : HChar E} {s : ℝ} {M : IntermediateField ℚ ℂ} :
    valueField χ s ≤ M ↔ χ.ValuesIn s M.val.toRingHom := by
  rw [valueField, IntermediateField.adjoin_le_iff]
  exact ⟨fun h v hv => ⟨⟨_, h ⟨v, hv, rfl⟩⟩, rfl⟩, fun h z ⟨v, hv, hz⟩ => by
    obtain ⟨y, hy⟩ := h v hv
    exact hz ▸ hy ▸ y.2⟩

theorem valuesIn_iff {χ : HChar E} {s : ℝ} {C : Type} [Field C] [NumberField C] (e : C →+* ℂ) :
    χ.ValuesIn s e ↔ valueField χ s ≤ imField e := by
  rw [valueField, IntermediateField.adjoin_le_iff]
  exact ⟨fun h z ⟨v, hv, hz⟩ => hz ▸ h v hv, fun h v hv => h ⟨v, hv, rfl⟩⟩

end Sub

section Curve

def torsionCoords (W : WeierstrassCurve ℂ) (n : ℕ) : Set ℂ :=
  {z | ∃ (x y : ℂ) (h : W.toAffine.Nonsingular x y), n • WeierstrassCurve.Affine.Point.some x y h = 0 ∧ (z = x ∨ z = y)}

theorem torsionCoords_mono (W : WeierstrassCurve ℂ) {n n' : ℕ} (h : n ∣ n') :
    torsionCoords W n ⊆ torsionCoords W n' := by
  rintro z ⟨x, y, hxy, h0, hz⟩
  obtain ⟨k, rfl⟩ := h
  exact ⟨x, y, hxy, by rw [mul_comm, mul_smul, h0, smul_zero], hz⟩

theorem torsionCoords_one (W : WeierstrassCurve ℂ) : torsionCoords W 1 = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro z ⟨x, y, hxy, h0, -⟩
  rw [one_smul] at h0
  exact WeierstrassCurve.Affine.Point.some_ne_zero hxy h0

example : Complex.I ∈ torsionCoords ⟨0, 0, 0, 1, 0⟩ 12 := by
  refine torsionCoords_mono _ (show 2 ∣ 12 by norm_num) ⟨Complex.I, 0, ?_, ?_, Or.inl rfl⟩
  · rw [WeierstrassCurve.Affine.nonsingular_iff, WeierstrassCurve.Affine.equation_iff]
    simp [pow_succ]
    norm_num
  · rw [two_smul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by simp [WeierstrassCurve.Affine.negY])

def hilbertField (d : ℕ) (F : IntermediateField ℚ ℂ) : IntermediateField ℚ ℂ := ℚ⟮sqrtNegNat d⟯ ⊔ F

variable (d : ℕ) {F : IntermediateField ℚ ℂ} (A : WeierstrassCurve F)

def torsionField : IntermediateField ℚ ℂ :=
  hilbertField d F ⊔ IntermediateField.adjoin ℚ (torsionCoords (A.baseChange ℂ) 12)

def discField : IntermediateField ℚ ℂ :=
  torsionField d A ⊔ IntermediateField.adjoin ℚ {z : ℂ | z ^ 12 = (A.Δ : ℂ)}

theorem hilbertField_le_torsionField : hilbertField d F ≤ torsionField d A := le_sup_left

theorem torsionField_le_discField : torsionField d A ≤ discField d A := le_sup_left

theorem discField_le_iff {M : IntermediateField ℚ ℂ} : discField d A ≤ M ↔
    sqrtNegNat d ∈ M ∧ F ≤ M ∧ torsionCoords (A.baseChange ℂ) 12 ⊆ M ∧ ∀ z : ℂ, z ^ 12 = (A.Δ : ℂ) → z ∈ M := by
  simp only [discField, torsionField, hilbertField, sup_le_iff, IntermediateField.adjoin_le_iff, and_assoc,
    Set.singleton_subset_iff, SetLike.mem_coe]
  rfl

theorem discField_eq_of_mem {u : ℂ} (hu : u ∈ torsionField d A) (h0 : u ≠ 0) :
    torsionField d A ⊔ IntermediateField.adjoin ℚ {z : ℂ | z ^ 12 = u ^ 12 * (A.Δ : ℂ)} = discField d A := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_) <;> rw [IntermediateField.adjoin_le_iff]
  · intro z (hz : z ^ 12 = _)
    have h1 : z / u ∈ discField d A :=
      ((discField_le_iff d A).1 le_rfl).2.2.2 _ (by rw [div_pow, hz]; field_simp)
    simpa [h0] using mul_mem h1 (torsionField_le_discField d A hu)
  · intro z (hz : z ^ 12 = _)
    have h1 := (le_sup_right : _ ≤ torsionField d A ⊔ _) (IntermediateField.subset_adjoin ℚ
      {z : ℂ | z ^ 12 = u ^ 12 * (A.Δ : ℂ)} (show (u * z) ^ 12 = _ by rw [mul_pow, hz]))
    simpa [h0] using mul_mem (inv_mem ((le_sup_left : torsionField d A ≤ _) hu)) h1

variable {d A} in

theorem hilbertField_eq (h : IsGoodCMCurve d F A) {L : PeriodPair} (hL : IsIntegersLattice d L) :
    hilbertField d F = ℚ⟮sqrtNegNat d, (latticeCurve L).j⟯ := by
  rw [hilbertField, h.field_eq hL, ← IntermediateField.adjoin_union]
  rfl

end Curve

section TypeNorm

open GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis (ClassBasis)

variable {R : Ranks} (H : Host R)

def typeNorm (p q : ℕ) (γ : H.E) : H.E := ∏ g : Tau R, (H.sigmaOf g γ ^ p * H.sigmaOf g (H.conj γ) ^ q)

theorem typeNorm_mul (p q : ℕ) (γ γ' : H.E) : typeNorm H p q (γ * γ') = typeNorm H p q γ * typeNorm H p q γ' := by
  rw [typeNorm, typeNorm, typeNorm, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun g _ => by rw [map_mul, map_mul, map_mul]; ring

theorem typeNorm_ne_zero (p q : ℕ) {γ : H.E} (h : γ ≠ 0) : typeNorm H p q γ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun g _ => mul_ne_zero (pow_ne_zero _ (by simpa using h)) (pow_ne_zero _ (by simpa using h))

theorem typeNorm_natCast (p q n : ℕ) : typeNorm H p q (n : H.E) = (n : H.E) ^ (R.f * (p + q)) := by
  simp only [typeNorm, map_natCast, Finset.prod_const, Finset.card_univ, card_Tau H, ← pow_add, ← pow_mul]
  rw [mul_comm]

def kPsiField (b : ClassBasis H.E) (p q : ℕ) : IntermediateField ℚ ℂ :=
  imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔
    IntermediateField.adjoin ℚ {z | ∃ i, z ^ b.h i = H.φ₀ (typeNorm H p q (b.γ i : H.E))}

theorem kPsiField_eq (b : ClassBasis H.E) (p q : ℕ) (ψ : Fin b.k → ℂ)
    (hψ : ∀ i, ψ i ^ b.h i = H.φ₀ (typeNorm H p q (b.γ i : H.E))) :
    kPsiField H b p q = imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔ IntermediateField.adjoin ℚ (Set.range ψ) := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
  · rw [IntermediateField.adjoin_le_iff]
    rintro z ⟨i, hz⟩
    have h0 : ψ i ≠ 0 := fun h => by
      have h1 := hψ i
      rw [h, zero_pow (b.h_pos i).ne'] at h1
      exact typeNorm_ne_zero H p q (b.γ i).ne_zero ((map_eq_zero _).1 h1.symm)
    obtain ⟨k, hk⟩ : b.h i ∣ classNumber H.E := orderOf_dvd_card
    have h1 : z / ψ i ∈ cycField (classNumber H.E) := mem_cycField (classNumber_ne_zero _) (by
      rw [hk, pow_mul, div_pow, hz, ← hψ i, div_self (pow_ne_zero _ h0), one_pow])
    have h2 := mul_mem ((le_sup_right.trans le_sup_left : _ ≤ imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔
      IntermediateField.adjoin ℚ (Set.range ψ)) h1)
      ((le_sup_right : _ ≤ imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔ IntermediateField.adjoin ℚ (Set.range ψ))
        (IntermediateField.subset_adjoin ℚ (Set.range ψ) ⟨i, rfl⟩))
    simpa [h0] using h2
  · rintro _ ⟨i, rfl⟩
    exact ⟨i, hψ i⟩

end TypeNorm

abbrev Chars (P : Pre) : Type := HFrame P.host (fun j τ => (P.hc τ).e j)

def modulus (P : Pre) : ℕ := P.host.g 0 * P.host.g 1 * P.host.pde * P.host.pde'

theorem modulus_ne_zero (P : Pre) : modulus P ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero)
    P.host.pde_prime.ne_zero) P.host.pde'_prime.ne_zero

def rootOrder (P : Pre) : ℕ := Nat.lcm P.restRowsFiniteGroupCard (3 ^ 4 * 5 ^ 4)

theorem rootOrder_ne_zero (P : Pre) : rootOrder P ≠ 0 := Nat.lcm_ne_zero P.restRowsFiniteGroupCard_pos.ne' (by norm_num)

structure FieldDat (P : Pre) where

  ray : IntermediateField ℚ ℂ
  isRay : IsRayFieldIn P.host.φ₀ (natIdeal P.host.E (modulus P)) ray

  jField : IntermediateField ℚ ℂ

  curve : WeierstrassCurve jField
  good : IsGoodCMCurve P.host.d jField curve

  basis : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis P.host.E

theorem nonempty_fieldDat (hR : RayField) (hA : CMCurveGoodOutsidePrimeSt) (P : Pre) : Nonempty (FieldDat P) := by
  obtain ⟨M, hM⟩ := exists_isRayFieldIn P.host.φ₀ hR (natIdeal_ne_bot (modulus_ne_zero P))
  have h16 : P.host.d % 16 = 7 := P.host.hyp.2.2.2.1
  obtain ⟨F, A, hF⟩ := hA.exists_isGoodCMCurve P.host.hyp.2.1 (by omega) (by omega)
  exact ⟨⟨M, hM, F, A, hF, Classical.choice inferInstance⟩⟩

namespace FieldDat

variable {P : Pre} (D : FieldDat P)

instance rayNumberField : NumberField D.ray := D.isRay.numberField

def hstar : ℕ := degOver P.host.φ₀ D.ray D.isRay.emb_mem

theorem hstar_pos : 0 < D.hstar := degOver_pos _ _ _

theorem finrank_mul_hstar : Module.finrank ℚ P.host.E * D.hstar = Module.finrank ℚ D.ray :=
  finrank_mul_degOver _ _ _

def M : IntermediateField ℚ ℂ := torsionField P.host.d D.curve

def M' : IntermediateField ℚ ℂ := discField P.host.d D.curve

def V : IntermediateField ℚ ℂ := kummerField P.host.φ₀ D.hstar

def Om : IntermediateField ℚ ℂ := D.M' ⊔ D.ray ⊔ cycField (rootOrder P) ⊔ D.V

def KPsi (j : ℕ) : IntermediateField ℚ ℂ := kPsiField P.host D.basis (P.R.sigW j).1 (P.R.sigW j).2

theorem M_le_M' : D.M ≤ D.M' := torsionField_le_discField _ _

theorem M'_le_Om : D.M' ≤ D.Om := (le_sup_left.trans le_sup_left).trans le_sup_left

theorem ray_le_Om : D.ray ≤ D.Om := (le_sup_right.trans le_sup_left).trans le_sup_left

theorem cycField_le_Om : cycField (rootOrder P) ≤ D.Om := le_sup_right.trans le_sup_left

theorem V_le_Om : D.V ≤ D.Om := le_sup_right

theorem imField_le_Om : imField P.host.φ₀ ≤ D.Om := (imField_le_kummerField _ _).trans D.V_le_Om

example : rootOne 15 ∈ D.Om :=
  cycField_le_iff.1 ((cycField_mono (rootOrder_ne_zero P)
    ((show 15 ∣ 3 ^ 4 * 5 ^ 4 by norm_num).trans (Nat.dvd_lcm_right _ _))).trans D.cycField_le_Om)

end FieldDat

def rootsField (P : Pre) : IntermediateField ℚ ℂ :=
  cycField P.restRowsFiniteGroupCard ⊔ cycField (P.host.g 0 * (P.host.g 0 - 1)) ⊔ cycField (P.host.g 1 * (P.host.g 1 - 1)) ⊔
    cycField (3 ^ 4) ⊔ cycField (5 ^ 4)

def charField {P : Pre} (C : Chars P) : IntermediateField ℚ ℂ :=
  (⨆ j, valueField (C.mu0 j) 0) ⊔ valueField C.eta (1 / 2) ⊔ valueField C.del 0 ⊔ valueField C.del' 0 ⊔
    IntermediateField.adjoin ℚ {z | ∃ k a, z = ((C.W.om k a : ℂˣ) : ℂ)}

def listField {P : Pre} (D : FieldDat P) (C : Chars P) : IntermediateField ℚ ℂ :=
  imField P.host.φ₀ ⊔ D.M' ⊔ D.ray ⊔ rootsField P ⊔ charField C ⊔ ⨆ j ∈ Set.Icc 1 P.R.m, D.KPsi j

theorem listField_le_iff {P : Pre} (D : FieldDat P) (C : Chars P) {N : IntermediateField ℚ ℂ} :
    listField D C ≤ N ↔ imField P.host.φ₀ ≤ N ∧ D.M' ≤ N ∧ D.ray ≤ N ∧ rootsField P ≤ N ∧ charField C ≤ N ∧
      ∀ j, 1 ≤ j → j ≤ P.R.m → D.KPsi j ≤ N := by
  simp only [listField, sup_le_iff, iSup_le_iff, and_assoc, Set.mem_Icc, and_imp]

theorem om_mem_rootsField {P : Pre} (C : Chars P) (k : Fin 2) (a : (ZMod (P.host.g k))ˣ) :
    ((C.W.om k a : ℂˣ) : ℂ) ∈ rootsField P := by
  have hp := P.host.g_prime k
  have : Fact (P.host.g k).Prime := ⟨hp⟩
  have h : ((C.W.om k a : ℂˣ) : ℂ) ∈ cycField (P.host.g k * (P.host.g k - 1)) :=
    mem_cycField (mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)) (by
      rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, ZMod.units_pow_card_sub_one_eq_one]
      simp)
  have h' : cycField (P.host.g k * (P.host.g k - 1)) ≤ rootsField P := by
    fin_cases k
    · exact ((le_sup_right.trans le_sup_left).trans le_sup_left).trans le_sup_left
    · exact (le_sup_right.trans le_sup_left).trans le_sup_left
  exact h' h

end GlobalTheory.Mem.Fld

namespace GlobalTheory.Mem.Base

open Fld

variable (B : Base)

def LLC : IntermediateField ℚ ℂ := imField B.embLL

def fixedCoefficientFieldInComplex : IntermediateField ℚ ℂ := B.LL0.map B.embLL.toRatAlgHom

def KsC : IntermediateField ℚ ℂ := B.Ks.map B.embLL.toRatAlgHom

def AutomorphicRingToComplex : B.LL0 →+* ℂ := B.embLL.comp B.LL0.val.toRingHom

def KstoC : B.Ks →+* ℂ := B.embLL.comp B.Ks.val.toRingHom

theorem mem_LLC {z : ℂ} : z ∈ B.LLC ↔ ∃ x, B.embLL x = z := Iff.rfl

theorem mem_LL0C {z : ℂ} : z ∈ B.fixedCoefficientFieldInComplex ↔ ∃ x ∈ B.LL0, B.embLL x = z := Iff.rfl

theorem mem_KsC {z : ℂ} : z ∈ B.KsC ↔ ∃ x ∈ B.Ks, B.embLL x = z := Iff.rfl

theorem KsC_le_LL0C : B.KsC ≤ B.fixedCoefficientFieldInComplex := fun _ ⟨x, hx, h⟩ => ⟨x, B.Ks_le hx, h⟩

theorem fixedField_le_coefficientField : B.fixedCoefficientFieldInComplex ≤ B.LLC := fun _ ⟨x, _, h⟩ => ⟨x, h⟩

theorem imField_KstoC : imField B.KstoC = B.KsC :=
  le_antisymm (fun _ ⟨x, h⟩ => ⟨x.1, x.2, h⟩) fun _ ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩

theorem imField_LL0toC : imField B.AutomorphicRingToComplex = B.fixedCoefficientFieldInComplex :=
  le_antisymm (fun _ ⟨x, h⟩ => ⟨x.1, x.2, h⟩) fun _ ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩

def KsEquiv : B.Ks ≃ₐ[ℚ] B.KsC := B.Ks.equivMap B.embLL.toRatAlgHom

instance numberField_KsC : NumberField B.KsC :=
  have : FiniteDimensional ℚ B.KsC := B.KsEquiv.toLinearEquiv.finiteDimensional
  NumberField.of_module_finite ℚ _

theorem finrank_KsC : Module.finrank ℚ B.KsC = Module.finrank ℚ B.Ks := B.KsEquiv.toLinearEquiv.finrank_eq.symm

theorem discr_KsC : discr B.KsC = discr B.Ks := (discr_eq_discr_of_algEquiv _ B.KsEquiv).symm

theorem imField_le_KsC : imField B.host.φ₀ ≤ B.KsC :=
  (imField_le_iff _).2 fun x => ⟨B.embE x, B.E_le_Ks x, RingHom.congr_fun B.embE_φ₀ x⟩

theorem rootsField_le_KsC : rootsField B.toPre ≤ B.KsC := by
  simp only [rootsField, sup_le_iff, cycField_le_iff]
  exact ⟨⟨⟨⟨B.roots_Ks _ (by simp), B.roots_Ks _ (by simp)⟩, B.roots_Ks _ (by simp)⟩, B.roots_Ks _ (by simp)⟩,
    B.roots_Ks _ (by simp)⟩

variable (D : FieldDat B.toPre) (C : Chars B.toPre) (c M : ℕ)

def RayInLL : Prop :=
  (∀ u, ∃ R, IsRayFieldIn B.host.φ₀ (natIdeal B.host.E (B.T u)) R ∧ R ≤ B.LLC) ∧
    ∃ R, IsRayFieldIn B.host.φ₀ (natIdeal B.host.E (B.host.g 0 * B.host.g 1)) R ∧ R ≤ B.LLC

def RayIn : Prop := D.ray ≤ B.KsC ∧ B.RayInLL

def CurveIn : Prop := D.M' ≤ B.KsC

def ValIn : Prop :=
  (∀ j, (C.mu0 j).ValuesIn 0 B.KstoC) ∧ C.eta.ValuesIn (1 / 2) B.KstoC ∧ C.del.ValuesIn 0 B.KstoC ∧
    C.del'.ValuesIn 0 B.KstoC ∧ (∀ k a, ((C.W.om k a : ℂˣ) : ℂ) ∈ B.KsC) ∧ C.chiPsi.ValuesIn 0 B.AutomorphicRingToComplex

def RootsIn : Prop :=
  rootOne (15 ^ c) ∈ B.fixedCoefficientFieldInComplex ∧ rootOne (B.host.pde ^ (2 * M)) ∈ B.fixedCoefficientFieldInComplex ∧ rootOne (B.host.pde' ^ (2 * M)) ∈ B.fixedCoefficientFieldInComplex

def KummerIn : Prop := ∀ j, 1 ≤ j → j ≤ B.R.m → D.KPsi j ≤ B.KsC

def KsLeOm : Prop := B.KsC ≤ D.Om

def KsExact : Prop := B.KsC = listField D C

def LowerOK : Prop := B.RayIn D ∧ B.CurveIn D ∧ B.ValIn C ∧ B.RootsIn c M ∧ B.KummerIn D

def FieldsOK : Prop := B.LowerOK D C c M ∧ B.KsLeOm D

theorem valIn_iff : B.ValIn C ↔ charField C ≤ B.KsC ∧ valueField C.chiPsi 0 ≤ B.fixedCoefficientFieldInComplex := by
  simp only [ValIn, charField, valuesIn_iff, imField_KstoC, imField_LL0toC, sup_le_iff, iSup_le_iff, and_assoc,
    IntermediateField.adjoin_le_iff]
  refine and_congr_right' (and_congr_right' (and_congr_right' (and_congr_right' (and_congr_left' ?_))))
  exact ⟨fun h z ⟨k, a, hz⟩ => hz ▸ h k a, fun h k a => h ⟨k, a, rfl⟩⟩

theorem lowerOK_iff : B.LowerOK D C c M ↔
    listField D C ≤ B.KsC ∧ valueField C.chiPsi 0 ≤ B.fixedCoefficientFieldInComplex ∧ B.RootsIn c M ∧ B.RayInLL := by
  rw [LowerOK, RayIn, valIn_iff, listField_le_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3, ⟨h4, h5⟩, h6, h7⟩ => ⟨⟨B.imField_le_KsC, h3, h1, B.rootsField_le_KsC, h4, h7⟩, h5, h6, h2⟩,
    fun ⟨⟨_, h3, h1, _, h4, h7⟩, h5, h6, h2⟩ => ⟨⟨h1, h2⟩, h3, ⟨h4, h5⟩, h6, h7⟩⟩

theorem fieldsOK_iff : B.FieldsOK D C c M ↔ (listField D C ≤ B.KsC ∧ B.KsC ≤ D.Om) ∧
    valueField C.chiPsi 0 ≤ B.fixedCoefficientFieldInComplex ∧ B.RootsIn c M ∧ B.RayInLL := by
  rw [FieldsOK, lowerOK_iff, KsLeOm]
  tauto

variable {B D C c M}

theorem ValIn.characterValues_mem_fixedField (h : B.ValIn C) :
    (∀ j, (C.mu0 j).ValuesIn 0 B.AutomorphicRingToComplex) ∧ C.eta.ValuesIn (1 / 2) B.AutomorphicRingToComplex ∧ C.chiPsi.ValuesIn 0 B.AutomorphicRingToComplex ∧
      C.del.ValuesIn 0 B.AutomorphicRingToComplex ∧ C.del'.ValuesIn 0 B.AutomorphicRingToComplex := by
  have key : ∀ {χ : HChar B.host.E} {s : ℝ}, χ.ValuesIn s B.KstoC → χ.ValuesIn s B.AutomorphicRingToComplex := fun hχ v hv => by
    obtain ⟨y, hy⟩ := hχ v hv
    exact ⟨⟨y.1, B.Ks_le y.2⟩, hy⟩
  exact ⟨fun j => key (h.1 j), key h.2.1, h.2.2.2.2.2, key h.2.2.1, key h.2.2.2.1⟩

theorem RootsIn.mono (h : B.RootsIn c M) {c' M' : ℕ} (hc : c' ≤ c) (hM : M' ≤ M) : B.RootsIn c' M' := by
  have key : ∀ {p a a' : ℕ}, p ≠ 0 → a' ≤ a → rootOne (p ^ a) ∈ B.fixedCoefficientFieldInComplex → rootOne (p ^ a') ∈ B.fixedCoefficientFieldInComplex :=
    fun hp ha h => cycField_le_iff.1 ((cycField_mono (pow_ne_zero _ hp) (pow_dvd_pow _ ha)).trans (cycField_le_iff.2 h))
  exact ⟨key (by norm_num) hc h.1, key B.host.pde_prime.ne_zero (by omega) h.2.1,
    key B.host.pde'_prime.ne_zero (by omega) h.2.2⟩

theorem KsExact.lower (h : B.KsExact D C) :
    D.ray ≤ B.KsC ∧ B.CurveIn D ∧ charField C ≤ B.KsC ∧ B.KummerIn D := by
  obtain ⟨-, h1, h2, -, h3, h4⟩ := (listField_le_iff D C).1 h.ge
  exact ⟨h2, h1, h3, h4⟩

theorem KsExact.ksLeOm_iff (h : B.KsExact D C) : B.KsLeOm D ↔ listField D C ≤ D.Om := by
  rw [KsLeOm, show B.KsC = listField D C from h]

namespace FieldsOK

variable (h : B.FieldsOK D C c M)
include h

theorem rayIn : B.RayIn D := h.1.1

theorem curveIn : B.CurveIn D := h.1.2.1

theorem valIn : B.ValIn C := h.1.2.2.1

theorem rootsIn : B.RootsIn c M := h.1.2.2.2.1

theorem kummerIn : B.KummerIn D := h.1.2.2.2.2

theorem ksLeOm : B.KsLeOm D := h.2

theorem listField_le : listField D C ≤ B.KsC := ((B.fieldsOK_iff D C c M).1 h).1.1

end FieldsOK

end GlobalTheory.Mem.Base

end
