import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChart

theorem denseRange_jK (R : Type) [CommRing R] [IsDomain R] : DenseRange (jK R) := by
  let ξ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  intro y
  have hs : jK R ξ ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => by
    have h₁ : algebraMap R (FractionRing R) a ∈ IsLocalRing.maximalIdeal (FractionRing R) := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h₁
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (h₁.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (f := jK R) ξ)) (specializes_iff_mem_closure.1 hs)

theorem isDominant_of_isPullback_jK {R : Type} [CommRing R] [IsDomain R] {X X' : Scheme.{0}}
    (p : X ⟶ Sp R) [Smooth p] (p' : X' ⟶ Sp (FractionRing R)) (φ : X' ⟶ X) (h : IsPullback φ p' p (jK R)) :
    IsDominant φ := by
  have hd : IsDominant (pullback.fst p (jK R)) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Pullback.range_fst]
    exact (denseRange_jK R).preimage p.isOpenMap
  have e : h.isoPullback.hom ≫ pullback.fst p (jK R) = φ := h.isoPullback_hom_fst
  rw [← e]
  infer_instance

theorem act_chart_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] (tC : SAB H (Sp R)) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S)
    (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (act : OAct (𝓞 E) G)
    (tK : SAB H (Sp (FractionRing R))) (a : SABMap tK tC (jK R)) (ψ : tK.G.left ⟶ G.left),
    (∀ u, (tK.act.act u).left ≫ ψ = ψ ≫ (act.act u).left) → a.φ ≫ πC = ψ →
    ∀ u, (tC.act.act u).left ≫ πC = πC ≫ (act.act u).left := by
  intro E _ _ _ H R _ _ tC S G _ _ ξ πC hG hP act tK a ψ hψ hφ u
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth tC.G.hom := tC.semi.smooth
  haveI : IsReduced tC.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced tC.G.hom
  haveI : IsDominant a.φ := isDominant_of_isPullback_jK tC.G.hom tK.G.hom a.φ a.cart.1
  have hw : πC ≫ G.hom = tC.G.hom ≫ ξ := hP.1.w
  refine ext_of_isDominant_of_isSeparated G.hom ?_ a.φ ?_
  · rw [Category.assoc, Category.assoc, hw, Over.w (act.act u), hw, ← Category.assoc, Over.w (tC.act.act u)]
  · have e : (tK.act.act u).left ≫ a.φ = a.φ ≫ (tC.act.act u).left := a.act u
    rw [← Category.assoc, ← e, Category.assoc, hφ, hψ, ← hφ, Category.assoc]

end GlobalTheory.UChart
