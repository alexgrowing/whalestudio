import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CoeffActAdd
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimit
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit GlobalTheory.ActionEnd

namespace GlobalTheory.ActionEndSelf

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)

include hlg hex hh in

theorem isEnd_act_raw (a : O) : IsEnd X V (dLin (Y.B.A.act a)) (dLin (Y.B.A.act (star a))) := by
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine isEnd_of_hom_raw Y X hlg hex hh _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
  have h := Y.gauge.ad a
  rw [actK_self, actK_self] at h
  rw [← h]
  have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
    show MvPowerSeries.map (RingHom.id C) _ = _
    rw [MvPowerSeries.map_id]; rfl
  rw [e]
  exact Y.intAd a

include hlg hex hh in

theorem gauge_at_linearPart_action_eq_hermitianLift (a : O) : un1 (Y.B.hL C Y.h a) =
    hAt X (endP X 1 (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C))
      (endP X (dLin (Y.B.A.act a)) (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C)) := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
  have hs : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
  have e1 := matrixEnd_eq_subst' Y X hlg hex (pt C dd 0) q0 (by
    rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
  rw [germLinearPart_coordinatePoint_zero] at e1
  have e2 := matrixEnd_eq_subst' Y X hlg hex _ (g a) (Y.B.A.hom a) _ hX
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
    hAt, hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s
  · exact (e1 x).symm
  · exact (e2 x).symm

theorem linear_parts_w0_sum_one : dLin (Y.B.A.act Y.w0) + dLin (Y.B.A.act (star Y.w0)) = 1 := by
  rw [← germLinearPart_coordinatePoint_zero, ← Y.B.A.one_act, ← Y.halfIntegralGenerator_add_conj_eq_one]
  ext i j
  exact (Nab.coeff_act_add Y.B _ _ i j).symm

end Chart

theorem exists_endomorphism_w0 : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∃ W W' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf p) V W W' ∧ W + W' = 1 ∧ (∀ (v : Fin 2 × Fin dd → C) (x : Fin 2 × Fin dd), W.mulVec v x = linAct (Y.B.A.act Y.w0) (fun i => v (x.1, i)) x.2) ∧ ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)) = hEnd (Y.rawSelf p) 1 W := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  let X : RawChart C d (fun _ => I0) (Fin dd) :=
    { lg := fun i => un1 (Y.lg i), ex := fun i => un1 (Y.ex i), h := Y.h, k := 0, u := fun _ => p.e,
      ty := fun _ => p.ty0, n := 0, j := 0, j' := 0, big := fun _ _ => True }
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp)]
    simp
  have hex : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  have hh : MvPowerSeries.constantCoeff X.h = 0 := by
    have := coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl (by
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' _ _ hg']
      rfl) Y.gauge.ax0 0 (by simp)
    simpa using this
  have blk : ∀ M M' : Matrix (Fin dd) (Fin dd) C, M + M' = 1 →
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M x.2 y.2 else 0) +
        (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M' x.2 y.2 else 0) = 1 := by
    intro M M' h
    ext ⟨a, i⟩ ⟨b, j⟩
    have := congrFun (congrFun h i) j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Prod.mk.injEq] at this ⊢
    by_cases hab : a = b
    · simp [hab, this]
    · simp [hab]
  have hone : (1 : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C) =
      fun x y => if x.1 = y.1 then (1 : Matrix (Fin dd) (Fin dd) C) x.2 y.2 else 0 := by
    rw [← blk 1 0 (add_zero _)]
    ext x y
    simp
  refine ⟨_, _, teichSelf_double C V dd d d _ _ X (Y.rawSelf p) hlg hex hh rfl rfl rfl _ _
    (isEnd_act_raw Y X rfl rfl rfl Y.w0), blk _ _ (linear_parts_w0_sum_one Y), fun v x => ?_, ?_⟩
  · show _ = (dLin (Y.B.A.act Y.w0)).mulVec (fun i => v (x.1, i)) x.2
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
      fun i => by simp
    have hX' : ∀ i : Fin 2 × Fin dd,
        MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun i => by simp
    have hlg' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).lg i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hlg _)
    have hex' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).ex i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hex _)
    unfold hEnd
    rw [hone]
    refine Eq.trans ?_ (teichSelf_hAt_col X (Y.rawSelf p) rfl _ _ (teichSelf_cc_endP _ hlg' hex' _ _ hX')
      (teichSelf_cc_endP _ hlg' hex' _ _ hX')).symm
    refine Finset.sum_congr rfl fun col _ => ?_
    have c : ∀ y : Fin dd, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (col, y) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun _ => hX' _
    rw [gauge_at_linearPart_action_eq_hermitianLift Y X rfl rfl rfl, inCol, teichSelf_subst_hAt X _ _ (teichSelf_cc_endP X hlg hex _ _ hX)
      (teichSelf_cc_endP X hlg hex _ _ hX) _ c]
    simp only [teichSelf_subst_endP X hlg _ _ hX _ c,
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero c)]
    congr 1 <;> funext y <;> exact (teichSelf_endP_col X (Y.rawSelf p) hlg rfl rfl _ _ hX' (col, y)).symm

end GlobalTheory.ActionEndSelf
