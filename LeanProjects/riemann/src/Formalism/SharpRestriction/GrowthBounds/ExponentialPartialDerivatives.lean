import Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives.UnshiftEvalEqSubstRawUnit

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace CEqGen

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq RowTiePCEqSum RowTiePCEqDer ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

def colU (col : Fin 2) : RawChart C d (fun _ => I0) (Fin dd) :=
  rawU Y d (fun g c i => (Y.rawSelf p).u g c (col, i))

theorem linW_const {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} (X : RawChart C d I κ) (g : Fin 2) (j : κ) :
    MvPowerSeries.constantCoeff
      (∑ c : I g, X.u g c j • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X, mul_zero]

theorem expPt_col (g col : Fin 2) (j : Fin dd) :
    (Y.rawSelf p).expPt g (col, j) = (colU Y p col).expPt g j := by
  show MvPowerSeries.subst _ (inCol col (un1 (Y.ex j))) = _
  rw [subst_inCol (linW_const (Y.rawSelf p) g)]
  rfl

theorem expPt_self0 (q : Fin 2 × (Fin 2 × Fin dd)) :
    MvPowerSeries.constantCoeff ((Y.rawSelf p).expPt q.1 q.2) = 0 :=
  constantCoeff_subst_zero (linW_const (Y.rawSelf p) q.1) (Y.self_chart_exp_constantCoeff p q.2)

theorem subst_hCol {τ : Type} {a : Fin 2 × (Fin 2 × Fin dd) → MvPowerSeries τ C}
    (ha : ∀ x, MvPowerSeries.constantCoeff (a x) = 0) (col : Fin 2) (f : PS C 2 dd) :
    MvPowerSeries.subst a (hCol col f) = MvPowerSeries.subst (fun q : Fin 2 × Fin dd => a (q.1, (col, q.2))) f := by
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold hCol
  rw [MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _) hS]
  congr 1
  funext q
  rw [MvPowerSeries.subst_X hS]

theorem subst_E_hCol (col : Fin 2) (f : PS C 2 dd) :
    MvPowerSeries.subst (fun q : Fin 2 × (Fin 2 × Fin dd) => (Y.rawSelf p).expPt q.1 q.2) (hCol col f) =
      MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (colU Y p col).expPt q.1 q.2) f := by
  rw [subst_hCol (expPt_self0 Y p)]
  congr 1
  funext q
  exact expPt_col Y p q.1 col q.2

theorem hRow_self : (Y.rawSelf p).hRow = ∑ col, (colU Y p col).hRow := by
  have hES := MvPowerSeries.hasSubst_of_constantCoeff_zero (expPt_self0 Y p)
  show ((Y.k : ℕ) : C) • MvPowerSeries.subst (fun q : Fin 2 × (Fin 2 × Fin dd) => (Y.rawSelf p).expPt q.1 q.2)
    (∑ col, hCol col Y.h) = ∑ col, ((Y.k : ℕ) : C) •
      MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (colU Y p col).expPt q.1 q.2) Y.h
  rw [← MvPowerSeries.coe_substAlgHom hES, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [MvPowerSeries.coe_substAlgHom, subst_E_hCol]

theorem subst_sg_self {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ x, MvPowerSeries.constantCoeff (a x) = 0) (v : Fin 2 × Fin dd → C) :
    MvPowerSeries.subst a ((Y.rawSelf p).sg v) =
      ∑ col, MvPowerSeries.subst (fun i => a (col, i)) ((colU Y p col).sg fun i => v (col, i)) := by
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [Y.rawSelf_sg p v, ← MvPowerSeries.coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [MvPowerSeries.coe_substAlgHom, subst_inCol ha]
  rfl

theorem derAt_self : DerAt V (Y.rawSelf p) := by
  intro g k
  have hES := MvPowerSeries.hasSubst_of_constantCoeff_zero (expPt_self0 Y p)
  have hcol := fun col : Fin 2 => derAt_rawU Y d (fun g c i => (Y.rawSelf p).u g c (col, i))
    (fun g c i => Y.rawSelf_u_integral p g c (col, i)) g k
  choose J hJI hJ using hcol
  refine ⟨∑ col, hCol col (J col), intS_sum _ fun col _ =>
    IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) (hJI col), ?_⟩
  have e1 : MvPowerSeries.subst (fun q : Fin 2 × (Fin 2 × Fin dd) => (Y.rawSelf p).expPt q.1 q.2)
      (∑ col, hCol col (J col)) =
      ∑ col, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (colU Y p col).expPt q.1 q.2) (J col) := by
    rw [← MvPowerSeries.coe_substAlgHom hES, map_sum]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [MvPowerSeries.coe_substAlgHom, subst_E_hCol]
  have e2 : MvPowerSeries.subst ((Y.rawSelf p).expPt g) ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) k)) =
      ∑ col, MvPowerSeries.subst ((colU Y p col).expPt g) ((colU Y p col).sg ((colU Y p col).u (1 - g) k)) := by
    rw [subst_sg_self Y p (fun x => expPt_self0 Y p (g, x))]
    refine Finset.sum_congr rfl fun col _ => ?_
    congr 1
    funext i
    exact expPt_col Y p g col i
  have e3 : dVar (⟨1 - g, k⟩ : WV fun _ : Fin 2 => I0) (Y.rawSelf p).hRow =
      ∑ col, dVar (⟨1 - g, k⟩ : WV fun _ : Fin 2 => I0) (colU Y p col).hRow := by
    rw [hRow_self, dVar_eq, map_sum]
    simp only [dVar_eq]
  rw [e3, e1, e2, ← Finset.sum_sub_distrib, Finset.smul_sum]
  exact Finset.sum_congr rfl fun col _ => hJ col

theorem addM_self : AddM V (Y.rawSelf p) := by
  intro τ _ γ γ' hγ hγ'
  have hcol := fun col : Fin 2 => addM_rawU Y d (fun g c i => (Y.rawSelf p).u g c (col, i)) τ
    (fun i => γ (col, i)) (fun i => γ' (col, i)) (fun i => hγ (col, i)) (fun i => hγ' (col, i))
  choose G hG hGlg hGsg using hcol
  have hG0 : ∀ x : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (G x.1 x.2) = 0 := fun x => (hG x.1 x.2).1
  refine ⟨fun x => G x.1 x.2, fun x => hG x.1 x.2, ?_, ?_⟩
  · rintro ⟨col, i⟩
    show MvPowerSeries.subst _ (inCol col (un1 (Y.lg i))) =
      MvPowerSeries.subst γ (inCol col (un1 (Y.lg i))) + MvPowerSeries.subst γ' (inCol col (un1 (Y.lg i)))
    rw [subst_inCol hG0, subst_inCol (fun x => (hγ x).1), subst_inCol (fun x => (hγ' x).1)]
    exact hGlg col i
  · intro v hv
    rw [subst_sg_self Y p hG0, subst_sg_self Y p (fun x => (hγ x).1), subst_sg_self Y p (fun x => (hγ' x).1),
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact intS_sum _ fun col _ => hGsg col _ fun i => hv (col, i)

end CEqGen

open CEqGen in

theorem cEqSelf_holds : CEqSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p _ H
  exact cEq_of (Y.rawSelf p) H
    (sumAt_of (Y.rawSelf p) (addM_self Y p) (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) (Y.rawSelf_exlg p)
      (Y.rawSelf_u_integral p))
    (derAt_self Y p)

end Formalism.L2.FormalSeriesBounds
