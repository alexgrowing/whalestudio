import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermLinearPartCoordinatePointZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ActionConvergesLadicCauchyAndStarStatement

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

variable {C : Type} [Field C]

theorem eq_zero_of_forall_ge (V : VF C) (x : C) (h : ∀ N : ℕ, V.Ge N x) : x = 0 := by
  by_contra hx
  have ht : V.v x ≠ ⊤ := (AddValuation.ne_top_iff V.v).2 hx
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt r
  have := h N
  rw [VF.Ge, ← hr, WithTop.coe_le_coe] at this
  exact absurd hN (not_lt.2 this)

theorem exists_nat_ge_neg (V : VF C) (x : C) : ∃ K : ℕ, V.Ge (-(K : ℝ)) x := by
  by_cases ht : V.v x = ⊤
  · exact ⟨0, by rw [VF.Ge, ht]; exact le_top⟩
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt (-r)
  refine ⟨N, ?_⟩
  rw [VF.Ge, ← hr, WithTop.coe_le_coe]
  linarith

theorem limit_unique (V : VF C) (s : ℕ → C) (x y : C) (hx : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (x - s n))
    (hy : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (y - s n)) : x = y := by
  refine sub_eq_zero.1 (eq_zero_of_forall_ge V _ fun N => ?_)
  obtain ⟨a, ha⟩ := hx N
  obtain ⟨b, hb⟩ := hy N
  have := (ha _ (le_max_left a b)).sub (hb _ (le_max_right a b))
  rwa [sub_sub_sub_cancel_right] at this

theorem linear_limit (V : VF C) {dd : ℕ} (e : Pt C 1 dd) (s : ℕ → Pt C 1 dd)
    (h : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (s n i)))
    (N : ℕ) (v : Fin dd → C) (i : Fin dd) :
    ∃ n0, ∀ n ≥ n0, V.Ge N ((dLin e).mulVec v i - linAct (s n) v i) := by
  choose K hK using fun j => exists_nat_ge_neg V (v j)
  choose m hm using fun j => h (N + K j) i (Finsupp.single ((0 : Fin 1), j) 1)
  refine ⟨Finset.univ.sup m, fun n hn => ?_⟩
  have e1 : (dLin e).mulVec v i - linAct (s n) v i =
      ∑ j, (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (e i) -
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (s n i)) * v j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rfl
  rw [e1]
  refine VF.Ge.sum fun j _ => ?_
  have := (hm j n (le_trans (Finset.le_sup (f := m) (Finset.mem_univ j)) hn)).mul (hK j)
  refine this.mono ?_
  push_cast
  linarith

theorem subst_singlePointUncurry {dd : ℕ} {τ : Type} (a : Fin dd → MvPowerSeries τ C)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  let ι : Fin dd ≃ Fin 1 × Fin dd :=
    { toFun := fun x => (0, x)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl }
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin dd => ha p.2),
    ← finsum_comp_equiv (Finsupp.equivCongrLeft ι)]
  refine finsum_congr fun e => ?_
  rw [Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain, Finsupp.equivMapDomain_eq_mapDomain]
  rfl

theorem germComp1_eq_subst {dd n : ℕ} (e : Pt C 1 dd) (a : Pt C n dd) (i : Fin dd) :
    comp1 e a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (![a] : Fin 1 → Pt C n dd) q.1 q.2) (e i) = _
  congr 1
  funext ⟨s, x⟩
  obtain rfl : s = 0 := Subsingleton.elim _ _
  rfl

theorem subst_exp_eq_mvExp [CharZero C] {σ : Type} (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst f (PowerSeries.exp C) = mvExp f := by
  ext m
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro k hk
    by_contra hc
    apply hk
    have hlt : m.degree < k := by simpa using hc
    have : MvPowerSeries.coeff m (f ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf)
      exact_mod_cast hlt
    simp [this]

section Chart

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

theorem gp_lg : GP Y.lg := fun i => by
  have := Y.lg_lin i 0 (by simp)
  simpa using this

theorem dLin_lg : dLin Y.lg = 1 := by
  rw [← germLinearPart_coordinatePoint_zero]
  ext i j
  exact Y.lg_lin i _ (by simp)

theorem eq_exp_lin_log (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1))) :
    e = comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap (dLin e)) Y.lg) := by
  have h0 := gp_lg Y
  have hF := Y.B.G.const
  have hi : IsInvPair Y.lg Y.ex := ⟨h0, Y.ex_const, Y.lg_ex, Y.ex_lg⟩
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have hl : comp1 Y.lg (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      comp1 Y.lg (pt C (n := 2) dd 0) + comp1 Y.lg (pt C (n := 2) dd 1) := funext Y.lg_add
  have e1 := additive_eq_lin _ hF Y.lg Y.ex (comp1 Y.lg e) (dLin_lg Y) hl hi (gp_comp1 _ _ h0 he) (by
    rw [gt_comp1_comp1 _ _ he _ (gp_addOf _ hF _ _ p0 p1), hhom,
      additive_at _ hF _ hl _ _ (gp_comp1 _ _ he p0) (gp_comp1 _ _ he p1),
      gt_comp1_comp1 _ _ he _ p0, gt_comp1_comp1 _ _ he _ p1])
  rw [dLin_comp _ _ he, dLin_lg, one_mul] at e1
  rw [← e1, gt_comp_inv' hi _ he]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

omit [CharZero C] in
theorem subst_linMap (M : Matrix (Fin dd) (Fin dd) C) (L : Pt C 1 dd) (h0 : GP L)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (x : Fin dd) :
    ∑ y, M x y • MvPowerSeries.subst a (un1 (L y)) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 (LogExpAdaptedGauge.linMap M) L x) := by
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  rw [germComp_matrixLinearMap_apply _ _ h0, ← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [subst_singlePointUncurry a ha, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_smul hs]

theorem matrixEnd_linearMap (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP (Y.raw p) M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := rfl
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

theorem matrixEnd_eq_subst (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap Y p _ a ha, ← eq_exp_lin_log Y e he hhom]

theorem matrixEnd_eq_comp (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP (Y.raw p) (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst Y p e he hhom a ha, germComp1_eq_subst]

theorem hAt_eq_ev {n : ℕ} (a b : Pt C n dd) : hAt (Y.raw p) a b = ev ![a, b] Y.h := by
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

theorem isEnd_of_hom (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd (Y.raw p) V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst Y p e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst Y p e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp Y p e he hhom _ (gp_pt 0), matrixEnd_eq_comp Y p e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev, hAt_eq_ev, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V M M' ∧ IsEnd (Y.raw p) V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d _ I _ p a ha
  obtain ⟨c1, c2⟩ := GlobalTheory.T.actionConverges_ladic_cauchy_and_star C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom Y p fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom Y p f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
