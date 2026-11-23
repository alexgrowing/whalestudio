import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_prime_nonunitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hg : IsCptGen ξ) (p : Cpt ξ) {o : Type} [CommRing o] [Algebra o Ω] (A : Subalgebra o Ω)
    (hA : ∀ s ∈ A, s ∈ regAt ξ p) :
    ∃ I : Ideal A, I.IsPrime ∧ ∀ s : A, s ∉ I ↔ unitAt ξ p (s : Ω) := by
  haveI : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).1
  let φ : A →+* regAt ξ p := RingHom.codRestrict A.val.toRingHom (regAt ξ p) (fun s => hA s s.2)
  refine ⟨Ideal.comap φ (IsLocalRing.maximalIdeal _), inferInstance, fun s => ?_⟩
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h.exists_right_inv
    have e : (s : Ω) * (t : Ω) = 1 := congrArg Subtype.val ht
    refine ⟨left_ne_zero_of_mul_eq_one e, hA s s.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right e]
    exact t.2
  · rintro ⟨h0, -, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : regAt ξ p) (Subtype.ext ?_)
    exact mul_inv_cancel₀ h0

theorem unitAt_of_le {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (p : Cpt ξ) (p' : Cpt ξ') (h : regAt ξ p ≤ regAt ξ' p') {a : Ω}
    (ha : unitAt ξ p a) : unitAt ξ' p' a :=
  ⟨ha.1, h ha.2.1, h ha.2.2⟩

theorem image_eq_of_regAt_eq :
    ∀ (P X₁ X₂ : Scheme.{0}) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ P) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (f₁ : X₁ ⟶ P)
      (f₂ : X₂ ⟶ P) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (u : κ → Ω), CoordTie o ξ₀ u → IsCptGen ξ₁ →
      IsCptGen ξ₂ → ξ₁ ≫ f₁ = ξ₀ → ξ₂ ≫ f₂ = ξ₀ → ∀ (p₁ : Cpt ξ₁) (p₂ : Cpt ξ₂), regAt ξ₁ p₁ = regAt ξ₂ p₂ →
      f₁ p₁.1 = f₂ p₂.1 := by
  intro P X₁ X₂ Ω _ ξ₀ ξ₁ ξ₂ f₁ f₂ o _ _ κ u hu g₁ g₂ e₁ e₂ p₁ p₂ hR
  have dom : ∀ {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ P), ξ ≫ f = ξ₀ →
      Dominates ξ ξ₀ f (RingHom.id Ω) := by
    intro X ξ f e
    have : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
      rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ₀
    rw [this, Category.id_comp, e]
  obtain ⟨h₁, r₁, n₁⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₁ Ω ξ₁ f₁ (RingHom.id Ω) (dom ξ₁ f₁ e₁) p₁
  obtain ⟨h₂, r₂, n₂⟩ := RegAtDom.regAt_dominates P Ω ξ₀ X₂ Ω ξ₂ f₂ (RingHom.id Ω) (dom ξ₂ f₂ e₂) p₂
  set a₁ : Cpt ξ₀ := ⟨f₁ p₁.1, h₁⟩ with ha₁
  set a₂ : Cpt ξ₀ := ⟨f₂ p₂.1, h₂⟩ with ha₂
  have l₁ : regAt ξ₀ a₁ ≤ regAt ξ₁ p₁ := fun a ha => r₁ a ha
  have l₂ : regAt ξ₀ a₂ ≤ regAt ξ₁ p₁ := fun a ha => hR ▸ r₂ a ha
  have m₁ : ∀ a ∈ regAt ξ₀ a₁, unitAt ξ₁ p₁ a → unitAt ξ₀ a₁ a := n₁ g₁
  have m₂ : ∀ a ∈ regAt ξ₀ a₂, unitAt ξ₁ p₁ a → unitAt ξ₀ a₂ a := fun a ha h =>
    n₂ g₂ a ha ⟨h.1, hR ▸ h.2.1, hR ▸ h.2.2⟩
  obtain ⟨c₁, hc₁⟩ := hu.cover a₁
  obtain ⟨c, hc⟩ := hu.cover a₂

  have hq : unitAt ξ₀ a₁ (u c / u c₁) := by
    refine m₁ _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, l₁ (hc₁.2 c), ?_⟩
    rw [inv_div]
    exact l₂ (hc.2 c₁)
  have hin : InChart ξ₀ u c a₁ := by
    refine ⟨hc.1, fun j => ?_⟩
    have : u j / u c = u j / u c₁ * (u c / u c₁)⁻¹ := by
      have := hc₁.1
      have := hc.1
      field_simp
    rw [this]
    exact mul_mem (hc₁.2 j) hq.2.2
  set A := Algebra.adjoin o (Set.range fun j => u j / u c) with hA
  have A₁ : ∀ s ∈ A, s ∈ regAt ξ₀ a₁ := fun s hs => (hu.ring c hc.1 s).1 hs a₁ hin
  have A₂ : ∀ s ∈ A, s ∈ regAt ξ₀ a₂ := fun s hs => (hu.ring c hc.1 s).1 hs a₂ hc
  obtain ⟨I, hI, hI₁⟩ := exists_prime_nonunitAt ξ₀ hu.gen a₁ A A₁
  have hI₂ : ∀ s : A, s ∉ I ↔ unitAt ξ₀ a₂ (s : Ω) := fun s => by
    rw [hI₁ s]
    exact ⟨fun h => m₂ _ (A₂ s s.2) (unitAt_of_le ξ₀ ξ₁ a₁ p₁ l₁ h),
      fun h => m₁ _ (A₁ s s.2) (unitAt_of_le ξ₀ ξ₁ a₂ p₁ l₂ h)⟩
  have e := (GlobalTheory.T.prime_chart_existsUnique_point P Ω ξ₀ o κ u hu c hc.1 I hI).unique ⟨hin, hI₁⟩ ⟨hc, hI₂⟩
  exact congrArg Subtype.val e

end GlobalTheory.CompanionTheory.Ar.SncBase
