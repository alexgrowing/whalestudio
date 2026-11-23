import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem holArc_nilpotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ nn : (Fu.Di Ha.i).La →ₗ[𝓞 E] (Fu.Di Ha.i).La, (∀ v, Ha.N v = Ha.P₀ (nn v)) ∧ (∀ v v', -(Fu.Di Ha.i).EF (nn v) v' = a.be (Ha.y v) (Ha.y v')) ∧ (∀ v, Ha.y (nn v) = 0) ∧ (∀ v, Ha.y v = 0 → nn v = 0) ∧ (∀ t, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF t v' = 0) → Ha.y t = 0) ∧ ∀ ξ : Module.Dual ℤ a.D₀.X, ∃! t, ∀ v', -(Fu.Di Ha.i).EF t v' = ξ (Ha.y v') := by
  intro E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha
  letI := GlobalTheory.TorusExt.gtGroup a.D₀ ℂ
  have hadj := (Fu.Di Ha.i).adj
  have hb := (Fu.Di Ha.i).unimod
  have hle : ∀ t, (∀ v', Ha.y v' = 0 → (Fu.Di Ha.i).EF t v' = 0) → Ha.y t = 0 := fun t ht => ((Ha.riemann t).1 ht).1
  let n := GlobalTheory.KerPerp.nilTo (bar := fun x => H.bar x) hadj hb Ha.y_onto a.be_adj
  have hn : ∀ v v', -(Fu.Di Ha.i).EF (n v) v' = a.be (Ha.y v) (Ha.y v') :=
    GlobalTheory.KerPerp.neg_apply_nilTo (bar := fun x => H.bar x) hadj hb Ha.y_onto a.be_adj
  refine ⟨(Submodule.subtype _).comp n, fun v => ?_, hn, fun v => hle _ (n v).2, fun v hv => ?_, hle, fun ξ => ?_⟩
  · let ex : (Fin g → ℂ) →+ Out.GtPtF a.D₀ ℂ :=
      AddMonoidHom.mk' Ha.ex₀ fun z z' => (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 (Ha.add z z')
    have hO : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
    have hfin := (Fu.Di Ha.i).fin
    have hL : Countable (Fu.Di Ha.i).La := Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
    rw [← sub_eq_zero]
    refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (Set.countable_range Ha.P₀) fun s => ?_
    obtain ⟨x, hx, hx'⟩ := ((Ha.riemann (n v)).1 (n v).2).2 s
    have hxe : x = fun z => eTwoPi (s * a.be (Ha.y v) z) := funext fun z => by
      obtain ⟨v', rfl⟩ := Ha.y_onto z
      rw [hx', ← hn]
      congr 1
      push_cast
      ring
    subst hxe
    have he : ex (s • Ha.N v) = ex (s • Ha.P₀ (n v)) :=
      GlobalTheory.TorusExt.IsTorusPtF.unique ((GlobalTheory.TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (Ha.shift s v))
        ((GlobalTheory.TorusExt.isTorusPtF_iff_isTorusPt _ _).2 hx)
    have h0 : ex (s • (Ha.N v - Ha.P₀ (n v))) = 0 := by rw [smul_sub, map_sub, he, sub_self]
    obtain ⟨u, -, hu⟩ := (Ha.ker _).1 ((GlobalTheory.TorusExt.isZero_iff_eq _).2 h0)
    exact ⟨u, hu.symm⟩
  · exact GlobalTheory.KerPerp.nil_eq_zero (nn := fun v => (n v : (Fu.Di Ha.i).La)) hb.1 hn hv
  · obtain ⟨t, -, ht⟩ := GlobalTheory.KerPerp.exists_of_dual (bar := fun x => H.bar x) (hadj := hadj) (y := Ha.y) hb.2 ξ
    exact ⟨t, ht, fun t' ht' => hb.1 (LinearMap.ext fun v => neg_injective ((ht' v).trans (ht v).symm))⟩

end GlobalTheory.ArcQ
