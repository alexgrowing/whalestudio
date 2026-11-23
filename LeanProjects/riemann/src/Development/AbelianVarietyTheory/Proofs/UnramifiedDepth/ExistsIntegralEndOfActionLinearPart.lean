import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAdjointIntegralEndOfLadicLimit

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit

namespace GlobalTheory.ActionEnd

variable {C : Type} [Field C]

theorem germ_comp1_zero_point_left {dd n : ℕ} (a : Pt C n dd) (ha : GP a) : comp1 (pt C dd (0 : Fin 1)) a = a := by
  funext i
  rw [germComp1_eq_subst]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) _

theorem actK_self [CharZero C] {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (B : FB C dd O) (a : O) :
    B.actK C a = B.A.act a := by
  funext i
  show MvPowerSeries.map (RingHom.id C) _ = _
  rw [MvPowerSeries.map_id]; rfl

theorem exists_isEnd_act : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  intro C _ _ V O _ _ dd Y d _ I _ p a
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine ⟨dLin (Y.B.A.act a), dLin (Y.B.A.act (star a)), fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · refine isEnd_of_hom Y p _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
    have h := Y.gauge.ad a
    rw [actK_self, actK_self] at h
    rw [← h]
    have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
      show MvPowerSeries.map (RingHom.id C) _ = _
      rw [MvPowerSeries.map_id]; rfl
    rw [e]
    exact Y.intAd a
  · have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
    have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
    have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
    have hs : MvPowerSeries.HasSubst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
    have e1 := matrixEnd_eq_subst Y p (pt C dd 0) q0 (by
      rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
    rw [germLinearPart_coordinatePoint_zero] at e1
    have e2 := matrixEnd_eq_subst Y p _ (g a) (Y.B.A.hom a) _ hX
    have e3 : comp1 (Y.B.A.act a) (pt C dd (0 : Fin 1)) = Y.B.A.act a := by
      funext i
      rw [germComp1_eq_subst]
      have : (fun q : Fin 1 × Fin dd => pt C dd (0 : Fin 1) q.2) = MvPowerSeries.X := by
        funext ⟨s, x⟩
        obtain rfl : s = 0 := Subsingleton.elim _ _
        rfl
      rw [this, MvPowerSeries.subst_self]; rfl
    have e4 : un1 (Y.B.hL C Y.h a) = MvPowerSeries.subst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) (Y.B.hL C Y.h a) := by
      rw [← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]; rfl
    rw [e4, FB.hL, actK_self, e3, ev, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 2 × Fin dd => pair_points_zero_constant q0 (g a) q.1 q.2) hs,
      hEnd, hAt]
    show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
    congr 1
    funext ⟨s, x⟩
    fin_cases s
    · exact (e1 x).symm
    · exact (e2 x).symm

end GlobalTheory.ActionEnd
