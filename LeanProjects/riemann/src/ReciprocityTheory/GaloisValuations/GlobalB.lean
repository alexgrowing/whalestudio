import ReciprocityTheory.GaloisValuations.GlobalA

set_option linter.style.haveILetI false

noncomputable section

open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors

namespace ReciprocityTheory.Gal

section den

variable {Ω : Type*} [Field Ω]

theorem isIntegral_int_of_isIntegral {F : Type*} [Field F] [NumberField F] [Algebra F Ω] {b : Ω} (hb : IsIntegral (𝓞 F) b) : IsIntegral ℤ b :=
  isIntegral_trans b hb

theorem mem_of_isIntegral_int (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ A := by
  have h1 : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem exists_den (F : Type*) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ s t : Ω, IsIntegral ℤ s ∧ IsIntegral ℤ t ∧ A.valuation s = 1 ∧ s * x = t := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hxF : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hxQ : IsIntegral ℚ x := isIntegral_trans x hxF
  let E := IntermediateField.adjoin ℚ ({x} : Set Ω)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxQ
  have : NumberField E := ⟨⟩
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  let M : FractionalIdeal (𝓞 E)⁰ E := 1 + FractionalIdeal.spanSingleton _ x'
  have h1M : (1 : E) ∈ M := by
    have hle1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact hle1 (FractionalIdeal.one_mem_one _)
  have hxM : x' ∈ M := by
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x' ≤ M := by
      simp only [M, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
    exact hle1 (FractionalIdeal.mem_spanSingleton_self _ _)
  have hM : M ≠ 0 := by
    intro h
    rw [h] at h1M
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).mp h1M)
  have hMM : M * M⁻¹ = 1 := mul_inv_cancel₀ hM
  obtain ⟨α, hα, β, hβ, e⟩ : ∃ α ∈ M⁻¹, ∃ β ∈ M⁻¹, α + x' * β = 1 := by
    have h1 : (1 : E) ∈ M * M⁻¹ := by rw [hMM]; exact FractionalIdeal.one_mem_one _
    have e2 : M * M⁻¹ = M⁻¹ ⊔ FractionalIdeal.spanSingleton _ x' * M⁻¹ := by
      simp only [M, add_mul, one_mul, FractionalIdeal.sup_eq_add]
    rw [e2, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
    obtain ⟨α, hα, z, hz, e⟩ := h1
    obtain ⟨β, hβ, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hz
    exact ⟨α, hα, β, hβ, e⟩
  have hint : ∀ γ ∈ M⁻¹, IsIntegral ℤ (γ : Ω) ∧ IsIntegral ℤ ((γ * x' : E) : Ω) := by
    intro γ hγ
    rw [FractionalIdeal.mem_inv_iff hM] at hγ
    have key : ∀ z : E, z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) → IsIntegral ℤ (z : Ω) := by
      intro z hz
      obtain ⟨z', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hz
      have : IsIntegral ℤ (algebraMap (𝓞 E) E z') := z'.2
      exact this.map (IsScalarTower.toAlgHom ℤ E Ω)
    exact ⟨by simpa using key _ (hγ 1 h1M), key _ (hγ x' hxM)⟩
  have hle : ∀ γ ∈ M⁻¹, A.valuation (γ : Ω) ≤ 1 := fun γ hγ =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (hint γ hγ).1)
  by_cases ha : A.valuation (α : Ω) = 1
  · exact ⟨α, _, (hint α hα).1, (hint α hα).2, ha, by simp [x']⟩
  by_cases hb : A.valuation (β : Ω) = 1
  · exact ⟨β, _, (hint β hβ).1, (hint β hβ).2, hb, by simp [x', mul_comm]⟩
  exfalso
  have ha' : A.valuation (α : Ω) < 1 := lt_of_le_of_ne (hle α hα) ha
  have hb' : A.valuation (β : Ω) < 1 := lt_of_le_of_ne (hle β hβ) hb
  have e' : (α : Ω) + x * (β : Ω) = 1 := by
    have := congrArg (fun z : E => (z : Ω)) e
    simpa [x'] using this
  have : A.valuation ((α : Ω) + x * (β : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ha' ?_
    rw [Valuation.map_mul]
    calc A.valuation x * A.valuation (β : Ω) ≤ 1 * A.valuation (β : Ω) := mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact hb'
  rw [e', Valuation.map_one] at this
  exact lt_irrefl _ this

theorem le_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A ≤ A' := by
  intro x hx
  have hx' : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx'
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have hs1' : A'.valuation s = 1 := by
    refine le_antisymm ((A'.valuation_le_one_iff s).mpr (mem_of_isIntegral_int A' hs)) ?_
    rw [← not_lt, ← h s hs, hs1]
    exact lt_irrefl 1
  have hxt : x = t * s⁻¹ := by rw [← e]; field_simp
  rw [← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, mul_one,
    A'.valuation_le_one_iff]
  exact mem_of_isIntegral_int A' ht

theorem eq_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A = A' :=
  le_antisymm (le_of_valuation_lt_one_iff F h)
    (le_of_valuation_lt_one_iff F fun b hb => (h b hb).symm)

end den

section places

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem smul_valuation_lt_one_iff (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Ω ≃ₐ[F] Ω) y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : Ω ≃ₐ[F] Ω).injective]

omit [NumberField F] [IsAlgClosure F Ω] in
theorem smul_le_one_of_isIntegral (g : Ω ≃ₐ[F] Ω) {A : ValuationSubring Ω}
    (hA : ∀ b : Ω, IsIntegral ℤ b → b ∈ A) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ g • A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  exact hA _ (hb.map ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ))

variable (F Ω) in

abbrev IntCl := integralClosure (𝓞 F) Ω

theorem valuation_le_one_intCl (A : ValuationSubring Ω) (b : IntCl F Ω) :
    A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (isIntegral_int_of_isIntegral b.2))

def primeBelow (A : ValuationSubring Ω) : Ideal (IntCl F Ω) where
  carrier := {b | A.valuation (b : Ω) < 1}
  add_mem' {a b} ha hb := by
    show A.valuation ((a : Ω) + b) < 1
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by show A.valuation ((0 : IntCl F Ω) : Ω) < 1; simp
  smul_mem' c b hb := by
    show A.valuation ((c : Ω) * b) < 1
    rw [Valuation.map_mul]
    calc A.valuation (c : Ω) * A.valuation (b : Ω) ≤ 1 * A.valuation (b : Ω) :=
          mul_le_mul_left (valuation_le_one_intCl A c) _
      _ < 1 := by rw [one_mul]; exact hb

theorem mem_primeBelow {A : ValuationSubring Ω} {b : IntCl F Ω} :
    b ∈ primeBelow A ↔ A.valuation (b : Ω) < 1 := Iff.rfl

instance isPrime_primeBelow (A : ValuationSubring Ω) : (primeBelow (F := F) A).IsPrime where
  ne_top' h := by
    have : (1 : IntCl F Ω) ∈ primeBelow A := h ▸ Submodule.mem_top
    rw [mem_primeBelow] at this
    simp at this
  mem_or_mem' {a b} hab := by
    rw [mem_primeBelow, mem_primeBelow]
    rw [mem_primeBelow] at hab
    by_contra hn
    simp only [not_or, not_lt] at hn
    have ha : A.valuation (a : Ω) = 1 := le_antisymm (valuation_le_one_intCl A a) hn.1
    have hb : A.valuation (b : Ω) = 1 := le_antisymm (valuation_le_one_intCl A b) hn.2
    have : A.valuation ((a * b : IntCl F Ω) : Ω) = 1 := by
      rw [MulMemClass.coe_mul, Valuation.map_mul, ha, hb, one_mul]
    rw [this] at hab
    exact lt_irrefl _ hab

theorem under_primeBelow {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    (primeBelow (F := F) A).under (𝓞 F) = v.asIdeal := by
  ext x
  rw [Ideal.under, Ideal.mem_comap, mem_primeBelow, ← hA x]
  rfl

theorem primeBelow_smul (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) :
    primeBelow (F := F) (g • A) = g • primeBelow (F := F) A := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_primeBelow, mem_primeBelow,
    smul_valuation_lt_one_iff]
  rfl

end places

section profinite

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

variable (F Ω) in

theorem continuousSMul_intCl :
    @ContinuousSMul (Ω ≃ₐ[F] Ω) (IntCl F Ω) _ _ ⊥ := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  refine ⟨continuous_discrete_rng.mpr fun c => ?_⟩
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g₀, b₀⟩ h
  refine ⟨{g : Ω ≃ₐ[F] Ω | g (b₀ : Ω) = g₀ (b₀ : Ω)} ×ˢ {b₀}, ?_,
    (isOpen_setOf_apply (F := F) (b₀ : Ω) (· = g₀ (b₀ : Ω))).prod (isOpen_discrete _), ⟨rfl, rfl⟩⟩
  rintro ⟨g, b⟩ ⟨hg, hb⟩
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢
  rw [← h]
  exact Subtype.ext hg

variable (F Ω) in

theorem isInvariant_intCl : Algebra.IsInvariant (𝓞 F) (IntCl F Ω) (Ω ≃ₐ[F] Ω) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Ω ≃ₐ[F] Ω, σ (b : Ω) = b := fun σ => congrArg Subtype.val (hb σ)
  have hbot := (InfiniteGalois.mem_bot_iff_fixed (b : Ω)).mpr hfix
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hbot
  have hcint : IsIntegral (𝓞 F) c := by
    have : IsIntegral (𝓞 F) (algebraMap F Ω c) := hc ▸ b.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (𝓞 F) F Ω)
      (algebraMap F Ω).injective).mp this
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 F) (K := F)).mp hcint
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hc, ← ha]
  rfl

theorem exists_smul_eq_of_over {A A' : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal)
    (hA' : ∀ x : 𝓞 F, A'.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ g : Ω ≃ₐ[F] Ω, g • A = A' := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A')
    (by rw [under_primeBelow hA, under_primeBelow hA'])
  refine ⟨g, eq_of_valuation_lt_one_iff F fun b hb => ?_⟩
  let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
  change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'
  rw [primeBelow_smul, hg]

theorem exists_frob_over {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∀ x, A.valuation x ≤ 1 →
      A.valuation (σ x - x ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Q.LiesOver v.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q
    (by rw [show Ideal.comap (algebraMap (𝓞 F) (IntCl F Ω)) Q = v.asIdeal from
      under_primeBelow hA]; exact v.isMaximal)
  letI : Field (IntCl F Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI hBi : Algebra.IsIntegral (𝓞 F) (IntCl F Ω) := inferInstance
  haveI : Algebra.IsIntegral (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q v.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ v.asIdeal] (IntCl F Ω ⧸ Q) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (IntCl F Ω ⧸ Q)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) v.asIdeal Q φ
  have hσQ' : σ • Q = Q := hσQ
  set q := Nat.card (𝓞 F ⧸ v.asIdeal) with hq
  have hqc : Fintype.card (𝓞 F ⧸ v.asIdeal) = q := Fintype.card_eq_nat_card
  have hcong : ∀ b : IntCl F Ω, A.valuation (σ (b : Ω) - (b : Ω) ^ q) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (σ • b) =
        Ideal.Quotient.mk Q b ^ Fintype.card (𝓞 F ⧸ v.asIdeal) :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b)
    have h2 : σ • b - b ^ q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, h1, hqc, sub_self]
    exact h2
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  refine ⟨σ, hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hcs := hcong ⟨s, hs.tower_top⟩
  have hct := hcong ⟨t, ht.tower_top⟩
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[F] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv

end profinite

end ReciprocityTheory.Gal
