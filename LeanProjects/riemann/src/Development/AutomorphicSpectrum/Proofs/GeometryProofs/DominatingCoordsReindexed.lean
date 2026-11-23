import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

private lemma valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r') : r = r' := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b := hs1'
  have e0 : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ (s - s') = 0 :=
    (map_sub _ s s').trans (by rw [hs1, hs1'', sub_self])
  have hnu : ¬ IsUnit (s - s') := by
    intro hu
    have hu' := hu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩)
    exact not_isUnit_zero ((congrArg IsUnit e0).mp hu')
  have e1 : (Scheme.stalkClosedPointTo z).hom (s - s') = r - r' := by
    rw [← hs2, ← hs2']
    exact map_sub _ _ _
  by_contra hne
  apply hnu
  apply (Scheme.isLocalHom_stalkClosedPointTo z).map_nonunit
  exact (congrArg IsUnit e1).mpr (sub_ne_zero.mpr hne).isUnit

private lemma valAt_mul_lemma_2 {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b b' : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b' r') :
    GlobalTheory.CompanionTheory.Ar.ValAt ξ z (b * b') (r * r') ∧ GlobalTheory.CompanionTheory.Ar.ValAt ξ z 1 1 := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b' := hs1'
  exact ⟨⟨hs, s * s', (map_mul _ s s').trans (congrArg₂ (· * ·) hs1 hs1''),
      (map_mul _ s s').trans (congrArg₂ (· * ·) hs2 hs2')⟩,
    ⟨hs, 1, map_one _, map_one _⟩⟩

theorem coordsAt_blkV : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)), GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i → CoordTie ℤ ξ₀ (fun c' : (k : K₀) → J₀ k => ∏ k, y₀ ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ₀ y₀ (z ≫ h) (fun p => w (blkV bk bx p)) := by
  classical
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i K₀ K _ _ J₀ J _ _ y₀ y bk bx hdom htie hgen hy hval z w hw
  unfold GlobalTheory.CompanionTheory.Ar.Dominates at hdom
  have hpt : ∀ (a b : PrimeSpectrum Ω₀), a = b := fun a b =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ⤳ GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) := by
    have h2 := (hgen (GlobalTheory.CompanionTheory.Ar.centre z)).map h.continuous
    have e1 : h (GlobalTheory.CompanionTheory.Ar.genPt ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
      have hh := congrArg (fun f => f (IsLocalRing.closedPoint Ω)) hdom
      simp only [Scheme.Hom.comp_apply] at hh
      exact hh.trans (congrArg ξ₀ (hpt _ _))
    have e2 : h (GlobalTheory.CompanionTheory.Ar.centre z) = GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) :=
      (Scheme.Hom.comp_apply z h _).symm
    rw [← e1, ← e2]
    exact h2
  unfold GlobalTheory.CompanionTheory.Ar.CoordsAt at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c', hc'⟩ := hw1 (bk k)
    refine ⟨(bx k).symm c', ?_⟩
    simpa [GlobalTheory.CompanionTheory.Ar.Chg.blkV] using hc'
  · simp only [GlobalTheory.CompanionTheory.Ar.Chg.blkV] at hc ⊢
    obtain ⟨hyne, hrat⟩ := hw2 (bk k) (bx k c) hc
    have hy0c : y₀ ⟨k, c⟩ ≠ 0 := fun h0 => hyne (by rw [hy, h0, map_zero])
    refine ⟨hy0c, fun j => ?_⟩
    obtain ⟨c', hc'0, hc'reg⟩ := htie.cover ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩
    dsimp only at hc'0 hc'reg
    have hprod : ∀ c'' : (k' : K₀) → J₀ k', (∏ k', y₀ ⟨k', c'' k'⟩) =
        y₀ ⟨k, c'' k⟩ * ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c'' k'⟩ :=
      fun c'' => Fintype.prod_eq_mul_prod_compl k _
    have hQ : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, mul_zero]
    have hd : y₀ ⟨k, c' k⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, zero_mul]
    have hrat0 : ∀ j' : J₀ k, y₀ ⟨k, j'⟩ / y₀ ⟨k, c' k⟩ ∈
        GlobalTheory.CompanionTheory.Ar.regAt ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ := by
      intro j'
      have hm := hc'reg (Function.update c' k j')
      have hrest : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', Function.update c' k j' k'⟩ =
          ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ := by
        apply Finset.prod_congr rfl
        intro k' hk'
        rw [Function.update_of_ne (by simpa using hk')]
      rw [hprod (Function.update c' k j'), hprod c', hrest, Function.update_self,
        mul_div_mul_right _ _ hQ] at hm
      exact hm
    obtain ⟨sj, hsj⟩ := RingHom.mem_range.mp (hrat0 j)
    obtain ⟨sc, hsc⟩ := RingHom.mem_range.mp (hrat0 c)
    have hvalc : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom sc) := ⟨hsp, sc, hsc, rfl⟩
    have hvalc' := hval z _ _ hvalc
    obtain ⟨rd, hrd, -⟩ := hrat (bx k (c' k))
    rw [hy, hy, ← map_div₀] at hrd
    obtain ⟨hprodv, hone⟩ := valAt_mul_lemma_2 ξ z hvalc' hrd
    rw [← map_mul, div_mul_div_comm, mul_comm (y₀ ⟨k, c⟩), div_self (mul_ne_zero hd hy0c),
      map_one] at hprodv
    have h1 := valAt_unique_lemma ξ z hprodv hone
    have hv : (Scheme.stalkClosedPointTo (z ≫ h)).hom sc ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hunit : IsUnit sc := (Scheme.isLocalHom_stalkClosedPointTo (z ≫ h)).map_nonunit _ (Ne.isUnit hv)
    let sci : X₀.presheaf.stalk (↑(⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ : GlobalTheory.CompanionTheory.Ar.Cpt ξ₀)) :=
      ↑hunit.unit⁻¹
    have hsci : sci * sc = 1 := by
      have hinv := hunit.unit.inv_mul
      rw [IsUnit.unit_spec] at hinv
      exact hinv
    have hgsci : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ sci *
        (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩) = 1 := by
      rw [← hsc, ← map_mul, hsci, map_one]
    have hs₀ : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ (sj * sci) =
        y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩ := by
      rw [map_mul, hsj, eq_inv_of_mul_eq_one_left hgsci]
      field_simp
    have hex : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom (sj * sci)) := ⟨hsp, _, hs₀, rfl⟩
    have hex' := hval z _ _ hex
    obtain ⟨r, hr, hwr⟩ := hrat (bx k j)
    rw [hy, hy, ← map_div₀] at hr
    have hrr := valAt_unique_lemma ξ z hr hex'
    refine ⟨r, ?_, hwr⟩
    rw [hrr]
    exact hex

end GlobalTheory.CompanionTheory.Ar.Chg
