import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG

theorem points_defOver : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (N : ℕ), 1 ≤ N → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N = 1 → ∀ a : D.X,
      DefOver k₀ (spMap ev ≫ b.left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) ∧
        DefOver k₀ (spMap ev ≫ (b * D.c a).left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a * b).left ≫ β) := by
  intro V₁ _ _ _ hV hunit D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hF K _ _ ev k₀ hk₀ hk N hN b hb a
  classical
  obtain ⟨-, -, hβ, -, hc, -, -⟩ := hF
  haveI : IsNoetherianRing V₁ := hV.1
  have hg : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ, hΦ⟩ :=
    GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (spMap ev) (spMap (ev.comp ib)) hg

  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → DefOver k₀ (x.left ≫ β) := by
    intro x hx
    have hNK : (N : K) ≠ 0 := by
      have := ((hunit N (by omega)).map ev).ne_zero
      simpa using this
    have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
    have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range
      fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} => (Φ y.1).left).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    have hσf : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap (ev.comp ib) := by
      have e1 : (σ.toRingHom).comp (ev.comp ib) = ev.comp ib := RingHom.ext fun u => hσ _ (hk u)
      have e0 : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap ((σ.toRingHom).comp (ev.comp ib)) := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e0, e1]
    let hh : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap (ev.comp ib)) := Over.homMk (spMap σ.toRingHom) hσf
    refine ⟨⟨Φ.symm (hh ≫ Φ x), ?_⟩, ?_⟩
    · rw [← map_pow, ← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one, map_one]
    · show (Φ (Φ.symm (hh ≫ Φ x))).left = _
      rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
      rfl

  have hsub : spMap k₀.subtype ≫ spMap ((ev.comp ib).codRestrict k₀ hk) = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  let j : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) :=
    Over.homMk (spMap k₀.subtype) hsub
  have hdesc : ∀ p : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left →
      ∃ p₀ : Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) ⟶ B₀, j ≫ p₀ = p := by
    intro p ⟨P₀, hP₀⟩
    have e : P₀ ≫ B₀.hom = spMap ((ev.comp ib).codRestrict k₀ hk) := spMap_subtype_cancel k₀ (by
      rw [← Category.assoc, hP₀, Over.w p, hsub]; rfl)
    exact ⟨Over.homMk P₀ e, Over.OverMorphism.ext hP₀⟩
  have hmul : ∀ p q : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left → DefOver k₀ q.left →
      DefOver k₀ (p * q).left := by
    intro p q hp hq
    obtain ⟨p₀, rfl⟩ := hdesc p hp
    obtain ⟨q₀, rfl⟩ := hdesc q hq
    rw [← MonObj.comp_mul]
    exact ⟨(p₀ * q₀).left, rfl⟩
  have hprod : ∀ y z : Over.mk (spMap ev) ⟶ D.P.A, DefOver k₀ (y.left ≫ β) → DefOver k₀ (z.left ≫ β) →
      DefOver k₀ ((y * z).left ≫ β) := by
    intro y z hy hz
    rw [← hΦ, map_mul]
    exact hmul _ _ (by rw [hΦ]; exact hy) (by rw [hΦ]; exact hz)

  let h : Over.mk (spMap ev) ⟶ 𝟙_ (Over (Sp V₁)) := Over.homMk (spMap ev) (Category.comp_id _)
  have hl : ∀ y : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, spMap ev ≫ y.left ≫ β = (h ≫ y).left ≫ β := by
    intro y
    rw [Over.comp_left, Category.assoc]
    rfl
  have h1 : DefOver k₀ (spMap ev ≫ b.left ≫ β) := by
    rw [hl]
    exact htor _ (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have h2 : DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) := by
    have e : spMap ev ≫ (D.c a).left ≫ β = spMap (ev.comp ib) ≫ c₀ a := by
      rw [show (D.c a).left ≫ β = spMap ib ≫ c₀ a from hc a, ← Category.assoc, hg]
    rw [e]
    exact defOver_comp k₀ (defOver_spMap k₀ _ hk) _
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h1) (by rw [← hl]; exact h2)
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h2) (by rw [← hl]; exact h1)

end GlobalTheory.USep.EvG
