import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

lemma arcι_X_isUnit (Dw : Datum H) (K₁ : Type) [Field K₁] : IsUnit (arcι Dw K₁ PowerSeries.X) := by
  have h : IsUnit (HahnSeries.ofPowerSeries ℤ K₁ PowerSeries.X) := by
    rw [isUnit_iff_ne_zero]
    first
      | (rw [HahnSeries.ofPowerSeries_X]; exact HahnSeries.single_ne_zero one_ne_zero)
      | (intro h0
         exact PowerSeries.X_ne_zero ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h0))
      | (simp; done)
  exact (h.map (MvPolynomial.C (σ := ArcLt Dw))).map
    (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁))

lemma arc_pt_X (Dw : Datum H) (K₁ : Type) [Field K₁] (q : Sp (ArcS Dw K₁)) :
    PowerSeries.X ∉ ((spMap (arcι Dw K₁)) q).asIdeal := by
  intro hX
  have h1 : arcι Dw K₁ PowerSeries.X ∈ q.asIdeal := by
    first
      | exact hX
      | (simpa using hX)
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (arcι_X_isUnit Dw K₁))

theorem arcPt_point (Y : Model Xo c β) {K₁ : Type} [Field K₁] (b : O →+* K₁) [Algebra c.F (ArcS Dw K₁)]
    (hcomp : (algebraMap c.F (ArcS Dw K₁)).comp β = (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp b))
    (χ : Sp (PowerSeries K₁) ⟶ Y.X) (hχs : χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b)
    (hj : ∀ x : Sp (PowerSeries K₁), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧
      z ≫ Y.jQ ≫ pullback.snd _ _ = spMap (algebraMap c.F (ArcS Dw K₁)) := by
  haveI := Y.jQ_open
  have hw : (spMap (arcι Dw K₁) ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcS Dw K₁)) ≫ spMap β := by
    rw [Category.assoc, hχs, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
  let g : Sp (ArcS Dw K₁) ⟶ pullback Y.s (spMap β) :=
    pullback.lift (spMap (arcι Dw K₁) ≫ χ) (spMap (algebraMap c.F (ArcS Dw K₁))) hw
  have hg : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    have e1 : (pullback.fst Y.s (spMap β)) (g q) = χ ((spMap (arcι Dw K₁)) q) := by
      have := congrArg (fun f : Sp (ArcS Dw K₁) ⟶ Y.X => f q) (pullback.lift_fst _ _ hw)
      first
        | exact this
        | (simpa using this)
    show (pullback.fst Y.s (spMap β)) (g q) ∈ abLocus Y.t.G
    rw [e1]
    obtain ⟨p, hp⟩ := hj _ (arc_pt_X Dw K₁ q)
    rw [← hp]
    have h2 : Y.jQ p ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]
      exact ⟨p, rfl⟩
    exact h2
  refine ⟨IsOpenImmersion.lift Y.jQ g hg, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ g hg ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

end Formalism.L2.Pj
