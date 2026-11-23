import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.MuThick

universe w w' v u v' u'

theorem d_pullC_eq_zero {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'} (m : CH.Mor F F' σ) (n : ℕ) (b : CH.Cn F n)
    (hb : CH.d F n b = 0) : CH.d F' n (m.pullC n b) = 0 := by
  rw [m.d_pullC, hb, map_zero]

theorem muB_incl {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (j : ℕ) (x : HdR q j) :
    (incl h).o.pull j (muB γ q l s' 𝒱 j x) = muB γ q l s 𝒱 j x := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx (GlobalTheory.LogCris.O (smFun X q))) j).1 x
  have d1 : ∀ (s₀ : ℕ), CH.d _ j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).pullC j a) = 0 := fun s₀ =>
    d_pullC_eq_zero _ j a ha
  have d2 : ∀ (s₀ : ℕ), CH.d _ j ((smO γ q l s₀ 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).pullC j a)) = 0 := fun s₀ =>
    d_pullC_eq_zero _ j _ (d1 s₀)
  have d3 : CH.d _ j ((incl h).o.pullC j ((smO γ q l s' 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s' 𝒱).ι).pullC j a))) = 0 :=
    d_pullC_eq_zero _ j _ (d2 s')
  have e : ∀ s₀ : ℕ, muB γ q l s₀ 𝒱 j ((CH.cx (GlobalTheory.LogCris.O (smFun X q))).cls a ha) =
      (CH.cx _).cls _ (d2 s₀) := fun s₀ =>
    (congrArg ((smO γ q l s₀ 𝒱).o.pull j) (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s₀ 𝒱).ι).hom j a ha (d1 s₀))).trans
      (CrystallineSemistableComparison.P.mapH_cls (smO γ q l s₀ 𝒱).o.hom j _ (d1 s₀) (d2 s₀))
  rw [e s', e s]
  refine (CrystallineSemistableComparison.P.mapH_cls (incl h).o.hom j _ (d2 s') d3).trans ?_
  have key : ∀ (b : CH.Cn (CH.modF (sP (TS γ q l s 𝒱)).A) j) (hb : CH.d _ j b = 0),
      b = (smO γ q l s 𝒱).o.pullC j ((CH.Mor.restrict (GlobalTheory.LogCris.O (smFun X q)) (TO q l s 𝒱).ι).pullC j a) →
      (CH.cx (CH.modF (sP (TS γ q l s 𝒱)).A)).cls b hb = (CH.cx _).cls _ (d2 s) := by
    rintro _ _ rfl
    rfl
  refine key _ d3 ?_
  funext t
  rfl

end GlobalTheory.CompanionTheory.MuThick
