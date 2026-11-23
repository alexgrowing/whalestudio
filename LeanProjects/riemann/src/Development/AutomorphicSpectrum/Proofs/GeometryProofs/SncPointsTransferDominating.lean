import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PatchIso

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (a : Ω) : unitAt ξ' p' a ↔ unitAt ξ p a := by
  unfold unitAt
  rw [h]

theorem char_zero_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (hp : Char0 ξ p) : Char0 ξ' p' := fun r hr hf =>
  hp r hr fun hu => hf ((unitAt_congr h _).2 hu)

theorem mem_genFib_of_char0 [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) :
    p ∈ genFib ξ := by
  have key : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n
    induction n using induction_on_primes with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | one => intro _; simpa using (regAt ξ p).one_mem
    | prime_mul r a hr ih =>
      intro h
      have ha : 0 < a := Nat.pos_of_mul_pos_left h
      have hu : unitAt ξ p (r : Ω) := not_not.1 (hp r hr)
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem hu.2.2 (ih ha)
  exact fun n hn => ⟨Nat.cast_ne_zero.2 hn.ne', natCast_mem _ n, key n hn⟩

theorem exists_below [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁} (hg : IsCptGen ξ₂)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p : Cpt ξ₂) (hp : Char0 ξ₂ p) :
    ∃ p₁ : Cpt ξ₁, p₁.1 = g p.1 ∧ Char0 ξ₁ p₁ ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  obtain ⟨h, -, hu⟩ := RegAtDom.regAt_dominates X₁ Ω ξ₁ X₂ Ω ξ₂ g (RingHom.id Ω) hd p
  have c : Char0 ξ₁ ⟨g p.1, h⟩ := fun r hr hf =>
    hf (hu hg (r : Ω) (natCast_mem _ r) (not_not.1 (hp r hr)))
  refine ⟨⟨g p.1, h⟩, rfl, c, ?_⟩
  rw [(hi _ (mem_genFib_of_char0 c)).regAt_eq p rfl, Subring.map_id]

theorem exists_above [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p₁ : Cpt ξ₁) (hp : Char0 ξ₁ p₁) :
    ∃ p : Cpt ξ₂, g p.1 = p₁.1 ∧ Char0 ξ₂ p ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  have I := hi p₁ (mem_genFib_of_char0 hp)
  obtain ⟨p, hp', -⟩ := I.existsUnique
  have e : regAt ξ₂ p = regAt ξ₁ p₁ := by rw [I.regAt_eq p hp', Subring.map_id]
  exact ⟨p, hp', char_zero_congr e hp, e⟩

theorem sncPts_of_isoAt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ κ₁ κ₂ x₁ x₂ X₁ X₂ ξ₁ ξ₂ g e Ab _ _ _ t₂ hd hi hs p hp
  have ePts : Pts ξ₂ = Pts ξ₁ := by
    ext R
    constructor
    · rintro ⟨p₂, c, rfl⟩
      obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, c₁, r⟩
    · rintro ⟨p₁, c, rfl⟩
      obtain ⟨p₂, -, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, c₂, r.symm⟩
  have eB : regAt ξ₂ '' {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} = regAt ξ₁ '' {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} := by
    ext R
    constructor
    · rintro ⟨p₂, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₁, e₁, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, ⟨c₁, e₁ ▸ ha⟩, r.symm⟩
    · rintro ⟨p₁, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₂, e₂, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, ⟨c₂, by rwa [e₂]⟩, r⟩
  obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p hp
  obtain ⟨A, z, n, q, hP, hq, hl⟩ := hs p₁ c₁
  refine ⟨A, z, n, q, ?_, hq, ?_⟩
  · rw [ePts, eB]
    exact hP
  · rw [r]
    exact hl

end GlobalTheory.CompanionTheory.Ar.PatchIso
