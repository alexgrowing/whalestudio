import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEq2
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
import Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives.SumAtOf

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace CEqGen

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq RowTiePCEqSum RowTiePCEqDer ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) (d : ℕ) {I : Fin 2 → Type} [∀ g, Fintype (I g)] (u : ∀ g, I g → Fin dd → C)

def rawU : RawChart C d I (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := Y.k
  u := u
  ty := fun _ _ => 0
  n := 0
  j := 0
  j' := 0
  big := fun _ _ => False

theorem rawU_sg (v : Fin dd → C) : (rawU Y d u).sg v = un1 (Y.sgP v) := Y.rawCol_sg v

theorem constantCoeff_rawUnit_exp (i : Fin dd) : MvPowerSeries.constantCoeff ((rawU Y d u).ex i) = 0 := by
  show MvPowerSeries.constantCoeff (un1 (Y.ex i)) = 0
  rw [constantCoeff_uncurry, Y.ex_const i]

theorem unshift_eval_eq_subst_rawUnit (f : PS C 1 dd) :
    un1 (ev (n := 1) ![Y.ex] f) = MvPowerSeries.subst (rawU Y d u).ex (un1 f) := by
  show _ = MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 f)
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun q : Fin 1 × Fin dd => Y.ex q.2) (fun q => Y.ex_const q.2),
    subst_singlePointUncurry (fun j => by rw [constantCoeff_uncurry, Y.ex_const j])]

theorem pderiv_expG_U (hE : ExDerSt Y) (g : Fin 2) (k : I g)
    (j : Fin dd) :
    MvPowerSeries.pderiv C k ((rawU Y d u).expG g j) =
      MvPowerSeries.subst ((rawU Y d u).expG g) (un1 (Y.dF ((rawU Y d u).u g k) j)) := by
  have hlin0 := lin_const (rawU Y d u) g
  have hL := MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0
  have hx0 : ∀ i, MvPowerSeries.constantCoeff ((rawU Y d u).ex i) = 0 := constantCoeff_rawUnit_exp Y d u
  have e1 : MvPowerSeries.subst (rawU Y d u).ex (un1 (Y.dF ((rawU Y d u).u g k) j)) =
      ∑ i, MvPowerSeries.C ((rawU Y d u).u g k i) * MvPowerSeries.pderiv C i ((rawU Y d u).ex j) := by
    rw [← unshift_eval_eq_subst_rawUnit Y d u, ← hE, uncurry_linear_combination]
    simp only [← pderiv_uncurry]
    rfl
  unfold RawChart.expG
  rw [Formalism.G.LogCR.pderiv_subst hlin0,
    ← MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hx0) hL]
  simp only [pderiv_lin]
  rw [e1, ← MvPowerSeries.coe_substAlgHom hL, map_sum, MvPowerSeries.coe_substAlgHom]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.subst_mul hL, MvPowerSeries.subst_C, mul_comm]

theorem derAt_rawU (hu : ∀ g c i, V.Ge 0 (u g c i)) : DerAt V (rawU Y d u) := by
  intro g k
  have hvI : ∀ i, V.Ge 0 ((rawU Y d u).u (1 - g) k i) := fun i => hu (1 - g) k i
  have hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff ((rawU Y d u).expPt q.1 q.2) = 0 := fun q => by
    rw [expPt_eq]
    exact upG_const _ (constantCoeff_subst_zero (lin_const (rawU Y d u) q.1) (constantCoeff_rawUnit_exp Y d u q.2))
  have hES := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  have hd : ∀ (g' : Fin 2) (j : Fin dd), MvPowerSeries.pderiv C (⟨1 - g, k⟩ : WV I) ((rawU Y d u).expPt g' j) =
      if g' = 1 - g then MvPowerSeries.subst ((rawU Y d u).expPt (1 - g)) (un1 (Y.dF ((rawU Y d u).u (1 - g) k) j))
      else 0 := by
    intro g' j
    split_ifs with hg
    · rw [hg, expPt_eq, pderiv_upG_same, pderiv_expG_U Y d u (exDer_holds Y) (1 - g) k j,
        upG_subst (1 - g) (a := (rawU Y d u).expG (1 - g))
          (fun i => constantCoeff_subst_zero (lin_const (rawU Y d u) (1 - g)) (constantCoeff_rawUnit_exp Y d u i))]
      congr 1
      funext i
      exact (expPt_eq _ _ _).symm
    · rw [expPt_eq, pderiv_upG_ne (1 - g) g' hg k]
  have hch : MvPowerSeries.pderiv C (⟨1 - g, k⟩ : WV I)
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2)
          (MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((rawU Y d u).expPt (1 - g)) (un1 (Y.dF ((rawU Y d u).u (1 - g) k) j)) := by
    rw [Formalism.G.LogCR.pderiv_subst hE0, Fintype.sum_prod_type, Finset.sum_eq_single (1 - g)]
    · simp only [hd, if_true]
    · intro g' _ hg'
      simp only [hd, if_neg hg', mul_zero, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set J : PS C 2 dd := (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((rawU Y d u).u (1 - g) k) j) *
      MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd g] (Y.sgP ((rawU Y d u).u (1 - g) k))
    with hJd
  have hsubD : MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2)
      (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((rawU Y d u).u (1 - g) k) j) *
        MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2)
          (MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((rawU Y d u).expPt (1 - g)) (un1 (Y.dF ((rawU Y d u).u (1 - g) k) j)) := by
    rw [← MvPowerSeries.coe_substAlgHom hES, map_sum, MvPowerSeries.coe_substAlgHom]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.subst_mul hES, subst_exp_eval_two _ hE0, mul_comm]
  have hJ : IntS V J := by
    have hg2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hg2 g with rfl | rfl
    · have h := germII_holds Y _ hvI
      convert h using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_pt_dF]
      rfl
    · have h := germIIM_holds Y _ hvI
      convert h using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_pt_dF]
      rfl
  refine ⟨J, hJ, ?_⟩
  rw [dVar_eq]
  show MvPowerSeries.pderiv C _ (((Y.k : ℕ) : C) •
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (rawU Y d u).expPt q.1 q.2) Y.h) = _
  rw [Derivation.map_smul, hch, ← hsubD, hJd, MvPowerSeries.subst_add hES, subst_exp_eval_two _ hE0, rawU_sg Y d u,
    add_sub_cancel_right]
  rfl

theorem addM_rawU : AddM V (rawU Y d u) := by
  intro τ _ γ γ' hγ hγ'
  set ρ : Fin 2 × Fin dd → MvPowerSeries τ C := fun q => ![γ, γ'] q.1 q.2 with hρ
  have hρ0 : ∀ q, MvPowerSeries.constantCoeff (ρ q) = 0 := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).1
    · exact (hγ' j).1
  have hρI : ∀ q, IntS V (ρ q) := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).2
    · exact (hγ' j).2
  have hρS := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  set γ'' : Fin dd → MvPowerSeries τ C := fun j => MvPowerSeries.subst ρ (Y.B.G.F j) with hγ''
  have hγ''0 : ∀ j, MvPowerSeries.constantCoeff (γ'' j) = 0 := fun j =>
    constantCoeff_subst_zero hρ0 (Y.B.G.const j)
  have hev : ∀ (a : Pt C 2 dd), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f : PS C 1 dd,
      MvPowerSeries.subst ρ (ev ![a] f) = MvPowerSeries.subst (fun j => MvPowerSeries.subst ρ (a j)) (un1 f) := by
    intro a ha f
    rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) hρS,
      subst_singlePointUncurry (fun j => constantCoeff_subst_zero hρ0 (ha j))]
  have hp0 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 0 j)) = γ := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((0 : Fin 2), j)) = γ j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hp1 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 1 j)) = γ' := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((1 : Fin 2), j)) = γ' j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hpa : (fun j => MvPowerSeries.subst ρ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j)) = γ'' := by
    funext j
    rw [addOf_pts]
  have hc0 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 0 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hc1 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 1 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hca : ∀ j, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => by rw [addOf_pts]; exact Y.B.G.const j
  refine ⟨γ'', fun j => ⟨hγ''0 j, IntS.subst hρ0 hρI (Y.intF j)⟩, ?_, ?_⟩
  · intro i
    have h := congrArg (MvPowerSeries.subst ρ) (Y.lg_add i)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_add, MvPowerSeries.coe_substAlgHom hρS, hev _ hca, hev _ hc0,
      hev _ hc1, hpa, hp0, hp1] at h
    exact h
  · intro v hv
    have h := IntS.subst hρ0 hρI (germI_holds Y v hv)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hρS, hev _ hca,
      hev _ hc0, hev _ hc1, hpa, hp0, hp1, ← rawU_sg Y d u v] at h
    exact h

end CEqGen
end Formalism.L2.FormalSeriesBounds
