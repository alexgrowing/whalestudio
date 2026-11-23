import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.TameCharUnique
open scoped Pointwise

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild {A : ValuationSubring Ω} {σ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  have hval : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h1 : A.valuation (σ y / y) = 1 := by
        have := A.valuation.map_one_add_of_lt (hσ y hy)
        rwa [add_sub_cancel] at this
      have h2 : σ y = σ y / y * y := (div_mul_cancel₀ _ hy).symm
      rw [h2, map_mul, h1, one_mul]
  rw [_root_.ReciprocityTheory.Gal.mem_Ine]
  unfold _root_.Formalism.ConjugateSelfDual.Inertia
  refine ⟨?_, fun x hx => ?_⟩
  · change (σ : Gal(Ω/E)) • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, AlgEquiv.smul_def]
    have hx := hval (σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hx
    rw [← hx]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hsplit : σ x - x = (σ x / x - 1) * x := by
        rw [sub_mul, div_mul_cancel₀ _ hx0, one_mul]
      rw [hsplit, map_mul]
      calc A.valuation (σ x / x - 1) * A.valuation x ≤ A.valuation (σ x / x - 1) :=
            mul_le_of_le_one_right' hx
        _ < 1 := hσ x hx0

variable [IsAlgClosure E Ω]

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.mem_of_tameGen {A : ValuationSubring Ω} {γ : _root_.Formalism.ConjugateSelfDual.G E Ω}
    (hγ : _root_.Formalism.BasicNotions.TameGenAt A γ)
    (S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) (hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)))
    (h1 : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S)
    (h2 : ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) → σ ∈ S)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) : σ ∈ S := by
  obtain ⟨C, hC, hCS⟩ := (Topology.IsInducing.subtypeVal.isClosed_iff).mp hS
  have hmapC : ((S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype : Subgroup (_root_.Formalism.ConjugateSelfDual.G E Ω)) :
      Set (_root_.Formalism.ConjugateSelfDual.G E Ω)) ⊆ C := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (Set.ext_iff.mp hCS τ).mpr hτ
  have hle : Subgroup.closure (insert γ {τ : _root_.Formalism.ConjugateSelfDual.G E Ω |
      ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1}) ≤ S.map (_root_.ReciprocityTheory.Gal.Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro τ (rfl | hτ)
    · exact ⟨_, h1, rfl⟩
    · exact ⟨⟨τ, _root_.GlobalTheory.TameCharUnique.mem_Ine_of_wild hτ⟩, h2 _ hτ, rfl⟩
  have hσC : (σ : _root_.Formalism.ConjugateSelfDual.G E Ω) ∈ C :=
    closure_minimal ((SetLike.coe_subset_coe.mpr hle).trans hmapC) hC (hγ.2 σ.2)
  exact (Set.ext_iff.mp hCS σ).mp hσC

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in
private lemma exists_pow_fixes_finiteDimensional (K : IntermediateField E Ω)
    [FiniteDimensional E K] (τ : Gal(Ω/E)) : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((τ ^ n : Gal(Ω/E)).toAlgHom.comp K.val : K →ₐ[E] Ω))
  have hfix : ∀ a b : ℕ, a < b → (∀ x ∈ K, (τ ^ a) x = (τ ^ b) x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ K, (τ ^ m) x = x := by
    intro a b hab hx
    refine ⟨b - a, Nat.sub_pos_of_lt hab, fun x hxK => ?_⟩
    apply (τ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact (hx x hxK).symm
  have hij' : ∀ x ∈ K, (τ ^ i) x = (τ ^ j) x := fun x hx => by
    simpa using DFunLike.congr_fun heq ⟨x, hx⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact hfix i j h hij'
  · exact hfix j i h fun x hx => (hij' x hx).symm

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {l : ℕ} [Fact l.Prime] (hlw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (t : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]) (ht : Continuous t)
    (σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) : (t σ).toAdd = 0 := by
  have hl1 : l ≠ 1 := (Fact.out : l.Prime).ne_one
  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
  rw [zero_add]
  have hUo : IsOpen (t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε}) :=
    (isOpen_lt (continuous_norm.comp continuous_toAdd) continuous_const).preimage ht
  obtain ⟨V, hVo, hVU⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hUo
  have h1V : (1 : Gal(Ω/E)) ∈ V := by
    have h1U : (1 : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
      simp [hε]
    rw [← hVU] at h1U
    exact h1U
  obtain ⟨K, hK, hKV⟩ := (krullTopology_mem_nhds_one_iff E Ω V).mp (hVo.mem_nhds h1V)
  obtain ⟨m, hm0, hmK⟩ := exists_pow_fixes_finiteDimensional K σ.1
  obtain ⟨e, m', hlm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' l hl1
  have hτ := _root_.GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m'
  have hfix : (σ ^ m' : _root_.ReciprocityTheory.Gal.Ine (F := E) A).1 ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [Subgroup.coe_pow]
    refine _root_.GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A _ hτ (l ^ e) (_root_.ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver hlw h e) x ?_
    rw [← pow_mul, mul_comm, ← hm]
    exact hmK x hx
  have hmem : σ ^ m' ∈ t ⁻¹' {x : Multiplicative ℤ_[l] | ‖x.toAdd‖ < ε} := by
    rw [← hVU]
    exact hKV hfix
  have hnorm : ‖(t (σ ^ m')).toAdd‖ < ε := hmem
  rwa [map_pow, toAdd_pow, nsmul_eq_mul, norm_mul,
    PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm'),
    one_mul] at hnorm

open NumberField IsDedekindDomain Polynomial Module in
open scoped Pointwise in
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] in
variable [IsAlgClosure E Ω] in

theorem _root_.GlobalTheory.TameCharUnique.exists_eq_mul : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (l : ℕ) [Fact l.Prime], ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (t t' : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l]), Continuous t → Continuous t' → Function.Surjective t' → ∃ c : ℤ_[l], ∀ σ, (t σ).toAdd = c * (t' σ).toAdd := by
  intro E Ω _ _ _ _ _ A w h l _ hlw t t' ht ht' hsurj
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have hwild : ∀ s : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l], Continuous s →
      ∀ σ : _root_.ReciprocityTheory.Gal.Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) →
        s σ = 1 := by
    intro s hs σ hσ
    rw [← toAdd_eq_zero]
    exact _root_.GlobalTheory.TameCharUnique.eq_zero_of_wild h hlw s hs σ hσ
  have hb : IsUnit (t' ⟨γ, hγ.1⟩).toAdd := by
    by_contra hb
    let S : Subgroup (_root_.ReciprocityTheory.Gal.Ine (F := E) A) :=
      { carrier := {σ | ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at *
          exact (PadicInt.nonarchimedean _ _).trans (max_le ha hb)
        one_mem' := by simp
        inv_mem' := fun {a} ha => by simpa using ha }
    have hS : IsClosed (S : Set (_root_.ReciprocityTheory.Gal.Ine (F := E) A)) :=
      isClosed_le (continuous_norm.comp (continuous_toAdd.comp ht')) continuous_const
    have hγS : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ S := by
      show ‖(t' ⟨γ, hγ.1⟩).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
      rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
      rw [PadicInt.isUnit_iff] at hb
      norm_num
      exact lt_of_le_of_ne (PadicInt.norm_le_one _) hb
    have hall : ∀ σ, σ ∈ S := fun σ =>
      _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ S hS hγS
        (fun τ hτ => by
          show ‖(t' τ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ)
          rw [hwild t' ht' τ hτ]
          simp) σ
    obtain ⟨σ, hσ⟩ := hsurj (Multiplicative.ofAdd 1)
    have h1 : ‖(t' σ).toAdd‖ ≤ (l : ℝ) ^ (-1 : ℤ) := hall σ
    rw [hσ, toAdd_ofAdd, norm_one, zpow_neg_one] at h1
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact absurd h1 (not_le.mpr (inv_lt_one_of_one_lt₀ hl))
  refine ⟨(t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹, fun σ => ?_⟩
  let f : _root_.ReciprocityTheory.Gal.Ine (F := E) A →* Multiplicative ℤ_[l] :=
    (AddMonoidHom.toMultiplicative
      (AddMonoidHom.mulLeft ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹))).comp t'
  have hf : Continuous f := by
    show Continuous fun τ => Multiplicative.ofAdd
      ((t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' τ).toAdd)
    exact continuous_ofAdd.comp (continuous_const.mul (continuous_toAdd.comp ht'))
  have hγmem : (⟨γ, hγ.1⟩ : _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∈ MonoidHom.eqLocus t f := by
    show t ⟨γ, hγ.1⟩ = f ⟨γ, hγ.1⟩
    apply Multiplicative.toAdd.injective
    show (t ⟨γ, hγ.1⟩).toAdd = (t ⟨γ, hγ.1⟩).toAdd * ↑hb.unit⁻¹ * (t' ⟨γ, hγ.1⟩).toAdd
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hwmem : ∀ τ : _root_.ReciprocityTheory.Gal.Ine (F := E) A,
      (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → τ ∈ MonoidHom.eqLocus t f := by
    intro τ hτ
    show t τ = f τ
    simp [f, hwild t ht τ hτ, hwild t' ht' τ hτ]
  have hmem := _root_.GlobalTheory.TameCharUnique.mem_of_tameGen hγ (MonoidHom.eqLocus t f)
    (isClosed_eq ht hf) hγmem hwmem σ
  exact congrArg Multiplicative.toAdd hmem

end GlobalTheory.TameCharUnique
