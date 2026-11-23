import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqSum2

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Defs

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.dF (Y : FBChart C V O dd) (v : Fin dd → C) (j : Fin dd) : PS C 1 dd :=
  ∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j))

def ExDerSt (Y : FBChart C V O dd) : Prop :=
  ∀ (v : Fin dd → C) (j : Fin dd),
    ∑ i, MvPowerSeries.C (v i) * MvPowerSeries.pderiv C ((0 : Fin 1), i) (Y.ex j) = ev (n := 1) ![Y.ex] (Y.dF v j)

def GermIIMSt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V ((∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) *
          MvPowerSeries.pderiv C ((0 : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd 1] (Y.sgP v))

end Defs

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) : dVar w F = MvPowerSeries.pderiv C w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem pderiv_upG_same (g : Fin 2) (k : I g) (F : MvPowerSeries (I g) C) :
    MvPowerSeries.pderiv C (⟨g, k⟩ : WV I) (upG g F) = upG g (MvPowerSeries.pderiv C k F) := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _), Finset.sum_eq_single k]
  · rw [MvPowerSeries.pderiv_X_self, mul_one]
  · intro c _ hc
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hc (eq_of_heq (Sigma.mk.inj h).2)
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem pderiv_upG_ne (g g' : Fin 2) (h : g' ≠ g) (k : I g) (F : MvPowerSeries (I g') C) :
    MvPowerSeries.pderiv C (⟨g, k⟩ : WV I) (upG g' F) = 0 := by
  unfold upG
  rw [Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _)]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
  intro he
  exact h (Sigma.mk.inj he).1

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem pderiv_uncurry (f : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.pderiv C i (un1 f) = un1 (MvPowerSeries.pderiv C ((0 : Fin 1), i) f) := by
  rw [uncurry_eq_subst, Formalism.G.LogCR.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _),
    Finset.sum_eq_single ((0 : Fin 1), i), uncurry_eq_subst]
  · rw [show (((0 : Fin 1), i) : Fin 1 × Fin dd).2 = i from rfl, MvPowerSeries.pderiv_X_self, mul_one]
  · intro q _ hq
    rw [MvPowerSeries.pderiv_X_of_ne, mul_zero]
    intro h
    exact hq (Prod.ext (Subsingleton.elim _ _) h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uncurry_linear_combination (r : Fin dd → C) (f : Fin dd → PS C 1 dd) :
    un1 (∑ i, MvPowerSeries.C (r i) * f i) = ∑ i, MvPowerSeries.C (r i) * un1 (f i) := by
  simp only [uncurry_eq_subst]
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_snd, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]

theorem uncurry_eval_exp_raw (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (f : PS C 1 dd) : un1 (ev (n := 1) ![Y.ex] f) = MvPowerSeries.subst (Y.raw p).ex (un1 f) := by
  show _ = MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 f)
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun q : Fin 1 × Fin dd => Y.ex q.2) (fun q => Y.ex_const q.2),
    subst_singlePointUncurry (fun j => by rw [constantCoeff_uncurry, Y.ex_const j])]

theorem ev_pt_dF (Y : FBChart C V O dd) (v : Fin dd → C) (g' : Fin 2) (j : Fin dd) :
    ev (n := 2) ![pt C dd g'] (Y.dF v j) =
      ∑ i, MvPowerSeries.C (v i) * ev (n := 2) ![pt C dd g', 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) := by
  have hZ := z0_1 (pt C (n := 2) dd g') (z0_pt g')
  have hZ' : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  unfold FBChart.dF
  rw [ev_sum hZ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZ, ev_C, ev_ev hZ' hZ]
  congr 2
  funext k j'
  fin_cases k
  · exact ev_X hZ 0 j'
  · exact ev_zero hZ

theorem pderiv_lin {κ : Type} [Fintype κ] (X : RawChart C d I κ) (g : Fin 2) (k : I g) (i : κ) :
    MvPowerSeries.pderiv C k (∑ c : I g, X.u g c i • (MvPowerSeries.X c : MvPowerSeries (I g) C)) =
      MvPowerSeries.C (X.u g k i) := by
  rw [map_sum, Finset.sum_eq_single k]
  · rw [Derivation.map_smul, MvPowerSeries.pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro c _ hc
    rw [Derivation.map_smul, MvPowerSeries.pderiv_X_of_ne hc, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem pderiv_expG (Y : FBChart C V O dd) (p : PairData Y d I) (hE : ExDerSt Y) (g : Fin 2) (k : I g)
    (j : Fin dd) :
    MvPowerSeries.pderiv C k ((Y.raw p).expG g j) =
      MvPowerSeries.subst ((Y.raw p).expG g) (un1 (Y.dF ((Y.raw p).u g k) j)) := by
  have hlin0 := lin_const (Y.raw p) g
  have hL := MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0
  have hx0 : ∀ i, MvPowerSeries.constantCoeff ((Y.raw p).ex i) = 0 := Y.chart_exp_constantCoeff p
  have e1 : MvPowerSeries.subst (Y.raw p).ex (un1 (Y.dF ((Y.raw p).u g k) j)) =
      ∑ i, MvPowerSeries.C ((Y.raw p).u g k i) * MvPowerSeries.pderiv C i ((Y.raw p).ex j) := by
    rw [← uncurry_eval_exp_raw Y p, ← hE, uncurry_linear_combination]
    simp only [← pderiv_uncurry]
    rfl
  unfold RawChart.expG
  rw [Formalism.G.LogCR.pderiv_subst hlin0,
    ← MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hx0) hL]
  simp only [pderiv_lin]
  rw [e1, ← MvPowerSeries.coe_substAlgHom hL, map_sum, MvPowerSeries.coe_substAlgHom]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPowerSeries.subst_mul hL, MvPowerSeries.subst_C, mul_comm]

end RowTiePCEqDer

namespace RowTiePCEqDer

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem subst_exp_eval_two {dd : ℕ} (X : RawChart C d I (Fin dd))
    (hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (X.expPt q.1 q.2) = 0) (g' : Fin 2) (f : PS C 1 dd) :
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => X.expPt q.1 q.2) (ev (n := 2) ![pt C dd g'] f) =
      MvPowerSeries.subst (X.expPt g') (un1 f) := by
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 1 × Fin dd => pt C (n := 2) dd g' q.2)
      fun q => MvPowerSeries.constantCoeff_X _) hS,
    subst_singlePointUncurry (fun j => hE0 (g', j))]
  congr 1
  funext q
  rw [show (pt C (n := 2) dd g' q.2) = MvPowerSeries.X (g', q.2) from rfl, MvPowerSeries.subst_X hS]

end RowTiePCEqDer

open RowTiePCEqDer in

theorem cEqDer_of
    (hE : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
      (Y : FBChart C V O dd), ExDerSt Y)
    (hM : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
      (Y : FBChart C V O dd), GermIIMSt Y) : CEqDerSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g k
  have hvI : ∀ i, V.Ge 0 ((Y.raw p).u (1 - g) k i) := fun i => p.u_int (1 - g) k i
  have hE0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff ((Y.raw p).expPt q.1 q.2) = 0 := fun q => by
    rw [expPt_eq]
    exact upG_const _ (constantCoeff_subst_zero (lin_const (Y.raw p) q.1) (Y.chart_exp_constantCoeff p q.2))
  have hES := MvPowerSeries.hasSubst_of_constantCoeff_zero hE0
  have hd : ∀ (g' : Fin 2) (j : Fin dd), MvPowerSeries.pderiv C (⟨1 - g, k⟩ : WV I) ((Y.raw p).expPt g' j) =
      if g' = 1 - g then MvPowerSeries.subst ((Y.raw p).expPt (1 - g)) (un1 (Y.dF ((Y.raw p).u (1 - g) k) j))
      else 0 := by
    intro g' j
    split_ifs with hg
    · rw [hg, expPt_eq, pderiv_upG_same, pderiv_expG Y p (hE C V O dd Y) (1 - g) k j,
        upG_subst (1 - g) (a := (Y.raw p).expG (1 - g))
          (fun i => constantCoeff_subst_zero (lin_const (Y.raw p) (1 - g)) (Y.chart_exp_constantCoeff p i))]
      congr 1
      funext i
      exact (expPt_eq _ _ _).symm
    · rw [expPt_eq, pderiv_upG_ne (1 - g) g' hg k]
  have hch : MvPowerSeries.pderiv C (⟨1 - g, k⟩ : WV I)
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2)
          (MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((Y.raw p).expPt (1 - g)) (un1 (Y.dF ((Y.raw p).u (1 - g) k) j)) := by
    rw [Formalism.G.LogCR.pderiv_subst hE0, Fintype.sum_prod_type, Finset.sum_eq_single (1 - g)]
    · simp only [hd, if_true]
    · intro g' _ hg'
      simp only [hd, if_neg hg', mul_zero, Finset.sum_const_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set J : PS C 2 dd := (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((Y.raw p).u (1 - g) k) j) *
      MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd g] (Y.sgP ((Y.raw p).u (1 - g) k))
    with hJd
  have hsubD : MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2)
      (∑ j, ev (n := 2) ![pt C dd (1 - g)] (Y.dF ((Y.raw p).u (1 - g) k) j) *
        MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) =
      ∑ j, MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2)
          (MvPowerSeries.pderiv C ((1 - g : Fin 2), j) Y.h) *
        MvPowerSeries.subst ((Y.raw p).expPt (1 - g)) (un1 (Y.dF ((Y.raw p).u (1 - g) k) j)) := by
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
    · have h := hM C V O dd Y _ hvI
      convert h using 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ev_pt_dF]
      rfl
  refine ⟨J, hJ, ?_⟩
  rw [dVar_eq]
  show MvPowerSeries.pderiv C _ (((Y.k : ℕ) : C) •
    MvPowerSeries.subst (fun q : Fin 2 × Fin dd => (Y.raw p).expPt q.1 q.2) Y.h) = _
  rw [Derivation.map_smul, hch, ← hsubD, hJd, MvPowerSeries.subst_add hES, subst_exp_eval_two _ hE0, Y.raw_sg p,
    add_sub_cancel_right]
  rfl

end Formalism.L2.FormalSeriesBounds
