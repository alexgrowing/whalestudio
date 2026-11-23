import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolPrimeTo

open Classical in

theorem exists_uniform {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) (l : ℕ) [hl : Fact l.Prime]
    (c₀ : 𝔠.elt) (h : ∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 F), n.Coprime l ∧ n • c = t • c₀) :
    ∃ m : ℕ, 0 < m ∧ m.Coprime l ∧ ∀ c : 𝔠.elt, ∃ t : 𝓞 F, (m : 𝓞 F) • c = t • c₀ := by
  obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  have hmem : ∀ x ∈ s, x ∈ 𝔠.elt := fun x hx ↦ by
    show x ∈ ((𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F)
    rw [← hs]; exact Submodule.subset_span hx
  choose n t hn ht using h
  let N : F → ℕ := fun x ↦ if hx : x ∈ 𝔠.elt then n ⟨x, hx⟩ else 1
  have hN : ∀ x, (N x).Coprime l := fun x ↦ by
    by_cases hx : x ∈ 𝔠.elt
    · simp only [N, dif_pos hx]; exact hn _
    · simp only [N, dif_neg hx]; exact Nat.coprime_one_left l
  have hpos : ∀ k : ℕ, k.Coprime l → 0 < k := fun k hk ↦ Nat.pos_of_ne_zero fun h0 ↦ by
    subst h0; exact hl.out.one_lt.ne' ((Nat.coprime_zero_left l).1 hk)
  refine ⟨∏ x ∈ s, N x, Finset.prod_pos fun x _ ↦ hpos _ (hN x), Nat.Coprime.prod_left fun x _ ↦ hN x, ?_⟩
  intro c

  let W : Submodule (𝓞 F) F :=
    { carrier := {y | ∃ hy : y ∈ 𝔠.elt, ∃ t : 𝓞 F, ((∏ x ∈ s, N x : ℕ) : 𝓞 F) • (⟨y, hy⟩ : 𝔠.elt) = t • c₀}
      add_mem' := by
        rintro a b ⟨ha, ta, ea⟩ ⟨hb, tb, eb⟩
        refine ⟨add_mem ha hb, ta + tb, ?_⟩
        have : (⟨a + b, add_mem ha hb⟩ : 𝔠.elt) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, smul_add, ea, eb, add_smul]
      zero_mem' := ⟨zero_mem _, 0, by
        have : (⟨0, zero_mem _⟩ : 𝔠.elt) = 0 := rfl
        rw [this, smul_zero, zero_smul]⟩
      smul_mem' := by
        rintro r a ⟨ha, ta, ea⟩
        refine ⟨Submodule.smul_mem _ r ha, r * ta, ?_⟩
        have : (⟨r • a, Submodule.smul_mem _ r ha⟩ : 𝔠.elt) = r • ⟨a, ha⟩ := rfl
        rw [this, smul_comm, ea, smul_smul] }
  have hsW : 𝔠.elt ≤ W := by
    have : ((𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) = 𝔠.elt := rfl
    rw [← this, ← hs, Submodule.span_le]
    intro x hx
    have hx' := hmem x hx
    refine ⟨hx', (∏ y ∈ s.erase x, N y : ℕ) * t ⟨x, hx'⟩, ?_⟩
    have e := ht ⟨x, hx'⟩
    rw [← Nat.cast_smul_eq_nsmul (𝓞 F)] at e
    have e2 : ((N x : ℕ) : 𝓞 F) • (⟨x, hx'⟩ : 𝔠.elt) = t ⟨x, hx'⟩ • c₀ := by simpa only [N, dif_pos hx'] using e
    rw [← Finset.mul_prod_erase s N hx, Nat.cast_mul, mul_comm, mul_smul, e2, smul_smul]
  obtain ⟨hc, t', e'⟩ := hsW c.2
  exact ⟨t', e'⟩

end GlobalTheory.PolPrimeTo

namespace GlobalTheory.PolPrimeTo

section Push

variable {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)

theorem isMonHom_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) : IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact isMonHom_one A A
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem push_id_pow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    haveI := isMonHom_id_pow A n
    push κ t ((𝟙 A) ^ n : A ⟶ A) = (n : R) • LinearMap.id := by
  induction n with
  | zero =>
    haveI := isMonHom_id_pow A 0
    rw [push_congr κ t (pow_zero (𝟙 A)), push_one, Nat.cast_zero, zero_smul]
  | succ n ih =>
    haveI := isMonHom_id_pow A n
    haveI := isMonHom_id_pow A (n + 1)
    haveI : IsMonHom ((𝟙 A) ^ n * 𝟙 A) := inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))
    rw [push_congr κ t (pow_succ (𝟙 A) n), push_mul, ih, push_id, Nat.cast_succ, add_smul, one_smul]

end Push

end GlobalTheory.PolPrimeTo

namespace GlobalTheory.PolPrimeTo

theorem act_natCast {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (a : OAct O G) (n : ℕ) :
    a.act (n : O) = (𝟙 G) ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    simpa using h
  | succ n ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

theorem bijective_push {S : Scheme.{0}} {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (t : S ⟶ Sp R)
    {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (f : A ⟶ B) (h : B ⟶ A)
    [IsMonHom f] [IsMonHom h] (m : ℕ) (hm : IsUnit (m : R)) (e₁ : f ≫ h = 𝟙 A ^ m) (e₂ : h ≫ f = 𝟙 B ^ m) :
    Function.Bijective (push κ t f) := by
  haveI := isMonHom_id_pow A m
  haveI := isMonHom_id_pow B m
  have k₁ : ∀ x, push κ t h (push κ t f x) = (m : R) • x := fun x ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₁, push_id_pow]; rfl
  have k₂ : ∀ y, push κ t f (push κ t h y) = (m : R) • y := fun y ↦ by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr κ t e₂, push_id_pow]; rfl
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨push κ t h ((↑hm.unit⁻¹ : R) • y), ?_⟩⟩
  · have e := congrArg (push κ t h) hxy
    rw [k₁, k₁] at e
    exact (hm.smul_left_cancel).1 e
  · rw [k₂, smul_smul, hm.mul_val_inv, one_smul]

end GlobalTheory.PolPrimeTo

namespace GlobalTheory.PolPrimeTo

theorem exists_totPos {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) (c₀ : 𝔠.elt) (hc₀ : (c₀ : F) ≠ 0) :
    ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  obtain ⟨a, s, hs, e⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (c₀ : F)
  have hs0 : (algebraMap (𝓞 F) F s) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)
  refine ⟨(s * a) • c₀, fun τ ↦ ?_⟩
  have : (((s * a) • c₀ : 𝔠.elt) : F) = (algebraMap (𝓞 F) F a) ^ 2 := by
    rw [Submodule.coe_smul, Algebra.smul_def, map_mul, ← e]
    field_simp
  rw [this, map_pow]
  have ha : algebraMap (𝓞 F) F a ≠ 0 := fun h0 ↦ hc₀ (by rw [← e, h0, zero_div])
  have hτ : τ (algebraMap (𝓞 F) F a) ≠ 0 := (map_ne_zero τ).2 ha
  positivity

end GlobalTheory.PolPrimeTo
