import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedHermitianSpace

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LeastExponentCompare
open NumberField NumberField.IsCMField TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in

theorem _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj (E : Type) [Field E] [NumberField E] (cj : E → E)
    (h : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) (hne : ∃ z : E, cj z ≠ z) :
    IsCMField E := by
  let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  have inj := φ₀.injective
  have hadd : ∀ a b, cj (a + b) = cj a + cj b := fun a b =>
    inj (by rw [h, map_add, map_add, h, h, star_add])
  have hmul : ∀ a b, cj (a * b) = cj a * cj b := fun a b =>
    inj (by rw [h, map_mul, map_mul, h, h, star_mul'])
  have hinv : ∀ z, cj (cj z) = z := fun z => inj (by rw [h, h, star_star])
  let e : E ≃+* E :=
    { toFun := cj, invFun := cj, left_inv := hinv, right_inv := hinv,
      map_mul' := hmul, map_add' := hadd }
  let σ : E ≃ₐ[ℚ] E := e.toRatAlgEquiv
  have hσ : ∀ z, σ z = cj z := fun _ => rfl
  have hsq : σ ^ 2 = 1 := AlgEquiv.ext fun z => by
    rw [pow_two, AlgEquiv.mul_apply, hσ, hσ, hinv, AlgEquiv.one_apply]
  have hne1 : σ ≠ 1 := by
    obtain ⟨z, hz⟩ := hne
    intro h1
    exact hz (by rw [← hσ, h1, AlgEquiv.one_apply])
  have hord : orderOf σ = 2 := orderOf_eq_prime hsq hne1
  have hfix : ∀ x, x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ cj x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun hx => hx σ (Subgroup.mem_zpowers σ), fun hx f hf => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    clear hf
    have hσx : σ x = x := hx
    have hσx' : σ⁻¹ x = x := by
      calc σ⁻¹ x = (σ⁻¹ * σ) x := by rw [AlgEquiv.mul_apply, hσx]
        _ = x := by rw [inv_mul_cancel, AlgEquiv.one_apply]
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hσx, ih]
    | pred k ih => rw [zpow_sub_one, AlgEquiv.mul_apply, hσx', ih]
  have hS : maximalRealSubfield E =
      (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield := by
    ext x
    rw [mem_maximalRealSubfield_iff, IntermediateField.mem_toSubfield, hfix]
    exact ⟨fun hx => inj ((h φ₀ x).trans (hx φ₀)), fun hx φ => by rw [← h φ x, hx]⟩
  have hfin : Module.finrank (maximalRealSubfield E) E = 2 := by
    rw [hS]
    exact (IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)).trans
      (by rw [Nat.card_zpowers, hord])
  haveI : IsTotallyComplex E := ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mp fun hv => by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hv
    obtain ⟨z, hz⟩ := hne
    exact hz (v.embedding.injective ((h _ z).trans (RingHom.congr_fun hv z)))⟩
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield E) E := ⟨hfin⟩
  exact ⟨⟩

set_option autoImplicit false in
open NumberField NumberField.IsCMField TensorProduct in

theorem _root_.GlobalTheory.LeastExponentCompare.conj_iff (E : Type) [Field E] [NumberField E]
    (cj : E → E) :
    ((∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ ∃ z : E, cj z ≠ z) ↔
      ∃ _ : IsCMField E, cj = fun z => complexConj E z := by
  constructor
  · rintro ⟨h, hne⟩
    haveI := _root_.GlobalTheory.LeastExponentCompare.isCMField_of_conj E cj h hne
    refine ⟨this, funext fun z => ?_⟩
    let φ₀ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
    exact φ₀.injective (by rw [h, complexEmbedding_complexConj, RCLike.star_def])
  · rintro ⟨_, rfl⟩
    refine ⟨fun φ z => by rw [complexEmbedding_complexConj, RCLike.star_def], ?_⟩
    by_contra hall
    push_neg at hall
    exact complexConj_ne_one E (AlgEquiv.ext hall)

section Comparison₂
variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

def IntegralAreSums (S : Submodule ℝ (Bil Y)) : Prop :=
  ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Bil Y) (x i) (x' i)

end Comparison₂

section AtLattice
variable (E : Type) [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def SpanBound (S : Submodule ℝ (Bil Y)) (φ : S → ℝ) (w : 𝓞 E) : Prop :=
  ∀ (β : S), (∀ a, 0 ≤ (β : Bil Y) a a) → ∀ (k : ℕ) (x : Fin k → Y),
    (∀ y : Y, ∃ n : ℕ, 0 < n ∧ n • y ∈ Submodule.span (𝓞 E) (Set.range x)) →
    φ β ≤ ∑ b, (β : Bil Y) (w • x b) (x b)

def MinimaBound (S : Submodule ℝ (Bil Y)) (φ : S → ℝ) : Prop :=
  ∀ (β : S), (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
      (Matrix.of fun i j => (β : Bil Y) (b i) (b j)).PosDef) →
    ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧
      ∀ i, (β : Bil Y) (v i) (v i) / 2 ≤
        (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
            (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * φ β

variable [IsCMField E]

end AtLattice

section Families

abbrev SpaceRule : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (_ : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    Submodule ℝ (Bil Y)

abbrev ValueRule (S : SpaceRule) : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    S E cj Y → ℝ

def Matches (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y],
    IsBalancedSpace E (S E (fun z => complexConj E z) Y) ∧
      φ E (fun z => complexConj E z) Y = leastExponent (S E (fun z => complexConj E z) Y)

def ForAllLattices (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y], Submodule ℝ (Bil Y) → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (S : Submodule ℝ (Bil Y)), IsBalancedSpace E S → P E Y S

def SpanAll (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] (w : 𝓞 E), (w : E) + cj w = 1 →
      SpanBound E (S E cj Y) (φ E cj Y) w

def SpanCM (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Free ℤ Y] [Module.Finite ℤ Y] (w : 𝓞 E), (w : E) + complexConj E w = 1 →
      SpanBound E (S E (fun z => complexConj E z) Y) (φ E (fun z => complexConj E z) Y) w

def MinimaAll (S : SpaceRule) (φ : ValueRule S) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (σ : E →+* ℂ) (z : E), σ (cj z) = star (σ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w : 𝓞 E), (w : E) + cj w = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y],
      MinimaBound E (S E cj Y) (φ E cj Y)

def SumsAll (S : SpaceRule) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y], IntegralAreSums (S E cj Y)

def SumsCM (S : SpaceRule) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], HasTraceOne E → ∀ (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y],
      IntegralAreSums (S E (fun z => complexConj E z) Y)

variable {S : SpaceRule} {φ : ValueRule S}

end Families

end GlobalTheory.LeastExponentCompare
