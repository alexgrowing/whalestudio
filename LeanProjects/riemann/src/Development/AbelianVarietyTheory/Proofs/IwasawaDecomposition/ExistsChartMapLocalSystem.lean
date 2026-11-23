import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenImmersionGeneric

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

namespace GlobalTheory.LocM.ChartLift

theorem exists_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p}, p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (a : Fin Z.m),
      ∃ g : Sp Γ(Z.X, (Z.U a).1) ⟶ (Xo Z.i.l).XF Z.i.c,
        g ≫ (Y Z.i).j = Z.chart a ≫ Z.π ∧ g ≫ pullback.snd _ _ = spMap (Z.alg a) := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z a
  have := GlobalTheory.ArcValuationSetting.isDiscreteValuationRing_place Z.i.c W hp.ne_zero hW
  have := GlobalTheory.LocM.Inhab.isOpenImmersion_generic (Z.i.c.V W)
  have := (Y Z.i).jQ_open
  have hj : IsOpenImmersion (Y Z.i).j := by unfold Model.j; infer_instance
  have hr : Set.range (Z.chart a) = (Z.U a).1 := (Z.U a).2.range_fromSpec
  let g := IsOpenImmersion.lift (Y Z.i).j (Z.chart a ≫ Z.π) (by
    rintro _ ⟨x, rfl⟩
    have : Z.chart a x ∈ Z.opn := Z.cover.le (Set.mem_iUnion.2 ⟨a, hr.le ⟨x, rfl⟩⟩)
    rw [Scheme.Hom.comp_apply]
    exact this)
  have hg : g ≫ (Y Z.i).j = Z.chart a ≫ Z.π := IsOpenImmersion.lift_fac _ _ _
  refine ⟨g, hg, ?_⟩
  have hjs : (Y Z.i).j ≫ (Y Z.i).s = pullback.snd _ _ ≫ spMap (Z.i.c.V W).subtype := by
    unfold Model.j
    rw [Category.assoc, pullback.condition, ← Category.assoc, (Y Z.i).jQ_over]
  rw [← cancel_mono (spMap (Z.i.c.V W).subtype), Category.assoc, ← hjs, reassoc_of% hg, Z.π_s, Z.alg_s]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.LocM.ChartLift
