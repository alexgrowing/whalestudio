import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

theorem GlobalTheory.Poinc.finite_preimage_integral : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ U : M₁.Z.Opens, IsAffineOpen U → (U : Set M₁.Z).Nonempty → ∀ b ∈ M₂.ringOn ((q ⁻¹ᵁ U : M₂.Z.Opens) : Set M₂.Z), ∃ f : Polynomial Ω₁, f.Monic ∧ (∀ i, f.coeff i ∈ M₁.ringOn (U : Set M₁.Z)) ∧ Polynomial.eval₂ (algebraMap Ω₁ Ω₂) b f = 0 := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hq hg U hUa hU b hb
  have hpt : ⊤ ≤ (M₂.pt ≫ q) ⁻¹ᵁ U := by
    rw [hg]
    exact fun x _ => M₁.top_le_preimage_pt hU (x := (spMap (algebraMap Ω₁ Ω₂)) x) trivial
  have hV : (((q ⁻¹ᵁ U : M₂.Z.Opens)) : Set M₂.Z).Nonempty :=
    ⟨M₂.pt (IsLocalRing.closedPoint Ω₂), hpt (x := IsLocalRing.closedPoint Ω₂) trivial⟩
  have h1 : ∀ a : Γ(M₁.Z, U), valF M₂.pt (q ⁻¹ᵁ U) ((q.app U).hom a) = algebraMap Ω₁ Ω₂ (valF M₁.pt U a) := by
    intro a
    refine (valR_comp M₂.pt q U a).symm.trans ?_
    rw [hg]
    exact valR_spMap_comp _ M₁.pt U (M₁.top_le_preimage_pt hU) a
  have hint : (q.app U).hom.IsIntegral := RingHom.IsIntegral.of_finite (hq.finite_app U hUa)
  obtain ⟨g, rfl⟩ := (RatModel.mem_ringOn_iff_exists hV).1 hb
  obtain ⟨P, hPm, hP⟩ := hint g
  refine ⟨P.map (M₁.res U hU), hPm.map _, fun i => ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact (RatModel.mem_ringOn_iff_exists hU).2 ⟨P.coeff i, (M₁.res_apply U hU _).symm⟩
  · have hc : (algebraMap Ω₁ Ω₂).comp (M₁.res U hU) = (M₂.res (q ⁻¹ᵁ U) hV).comp (q.app U).hom := by
      ext a
      simp only [RingHom.comp_apply, RatModel.res_apply]
      exact (h1 a).symm
    rw [Polynomial.eval₂_map, hc, ← RatModel.res_apply _ _ hV, ← Polynomial.hom_eval₂, hP, map_zero]
