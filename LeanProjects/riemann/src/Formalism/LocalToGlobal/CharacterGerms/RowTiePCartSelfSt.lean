import Formalism.LocalToGlobal.CharacterGerms.RowTiePAxesSelfSt
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Col

variable {dd : ℕ}

theorem hasSubst_col (col : Fin 2) :
    HasSubst (fun x : Fin dd => (X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem col_inj (col : Fin 2) : Function.Injective (fun x : Fin dd => (col, x)) :=
  fun _ _ h => (Prod.ext_iff.1 h).2

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun i => a (col, i)) f := by
  have hS := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_col col) hS]
  congr 1
  funext i
  rw [subst_X hS]

theorem inCol_X (col : Fin 2) (i : Fin dd) : inCol col (X i : MvPowerSeries (Fin dd) C) = X (col, i) := by
  unfold inCol
  rw [subst_X (hasSubst_col col)]

theorem coeff_subst_rename_out {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (e : τ →₀ ℕ)
    (he : ∀ e' : σ →₀ ℕ, e'.mapDomain φ ≠ e) :
    coeff e (subst (fun s => (X (φ s) : MvPowerSeries τ C)) F) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e'
  rw [prod_X_rename, coeff_monomial, if_neg (fun h => he e' h.symm), smul_zero]

theorem coeff_inCol_lin (col : Fin 2) (f f' : MvPowerSeries (Fin dd) C)
    (h : ∀ μ : Fin dd →₀ ℕ, μ.degree ≤ 1 → coeff μ f = coeff μ f') (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ (inCol col f) = coeff μ (inCol col f') := by
  unfold inCol
  by_cases hr : ∃ μ' : Fin dd →₀ ℕ, μ'.mapDomain (fun x => (col, x)) = μ
  · obtain ⟨μ', rfl⟩ := hr
    rw [coeff_subst_rename_inj _ (col_inj col), coeff_subst_rename_inj _ (col_inj col)]
    exact h μ' (by rw [Finsupp.degree_mapDomain] at hμ; exact hμ)
  · push_neg at hr
    rw [coeff_subst_rename_out _ _ _ hr, coeff_subst_rename_out _ _ _ hr]

end Col

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem FBChart.self_chart_log_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).lg x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.lg x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.lg_const x.2

theorem FBChart.self_chart_exp_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).ex x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.ex_const x.2

theorem FBChart.rawSelf_axis0 (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    coeff e (Y.rawSelf p).h = 0 := by
  show coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 0 Y.h (gauge_axes Y 0)) e he

theorem FBChart.rawSelf_exlg (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).lg (inCol col (un1 (Y.ex i))) = _
  rw [subst_inCol (Y.self_chart_log_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.lg j))) (un1 (Y.ex i)) = _
  have hL : HasSubst (fun j => un1 (Y.lg j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.lg_const]
  have hx : un1 (comp1 Y.ex Y.lg i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.ex_lg]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.lg_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lgex (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).ex ((Y.rawSelf p).lg x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).ex (inCol col (un1 (Y.lg i))) = _
  rw [subst_inCol (Y.self_chart_exp_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.ex j))) (un1 (Y.lg i)) = _
  have hL : HasSubst (fun j => un1 (Y.ex j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.ex_const]
  have hx : un1 (comp1 Y.lg Y.ex i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.lg_ex]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.ex_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lin (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ ((Y.rawSelf p).lg x) = coeff μ (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show coeff μ (inCol col (un1 (Y.lg i))) = _
  rw [← inCol_X col i]
  refine coeff_inCol_lin col _ _ (fun ν hν => ?_) μ hμ
  show coeff (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hν), ← uncurry_X i]
  rfl

theorem SelfData.gm_int (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h := hM a r s
  rw [Nat.cast_zero] at h
  have e : p.gm a r s = (p.gm a r s - p.em a (M r s)) + p.em a (M r s) := by ring
  rw [e]
  exact h.add (p.em_int a _)

theorem FBChart.rawSelf_u_integral (g : Fin 2) (c : I0) (x : Fin 2 × Fin dd) : V.Ge 0 ((Y.rawSelf p).u g c x) :=
  VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (p.e_int c x.2)

theorem SelfData.gm_pair (a : ZMod d) (g : Fin 2) :
    ∑ col, p.gm a col g * p.gm (a + p.hd) col (1 - g) = 1 := by
  have h := p.gm_hyp (a + p.hd) g (1 - g)
  rw [add_assoc, p.hd_two, add_zero, if_neg (by fin_cases g <;> decide)] at h
  exact h

theorem FBChart.exists_integral_right_inverse (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  obtain ⟨w0, hw0, huw⟩ := p.e_sat
  refine ⟨fun x c' => p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c',
    fun x c' => VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (hw0 _ _), fun c c' => ?_⟩
  show ∑ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') = _
  have e1 : ∀ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') =
      (p.gm (p.ty0 c) x.1 g * p.gm (p.ty0 c' + p.hd) x.1 (1 - g)) * (p.e c x.2 * w0 x.2 c') := fun x => by ring
  simp_rw [e1]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, huw c c']
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl]
    simp only [mul_one]
    exact SelfData.gm_pair Y p _ g
  · simp [hc]

def PTSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

def AddCvSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => X.AddCvSt V

def HStabSelfSt : Prop :=
  AllSelf fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

theorem cartSelf_of (hPT : PTSelfSt) (hAdd : AddCvSelfSt) (hStab : HStabSelfSt) : CartSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g
  have := Y.algClosed
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have h0 := (Y.rawSelf p).zero_mem (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
  have hadd := (Y.rawSelf p).add_mem V g (hAdd C V O dd Y d I0 p) (fun g c x => Y.rawSelf_u_integral p g c x)
  exact
    { zero := h0
      add := hadd
      neg := (Y.rawSelf p).neg_mem V g Y.l_odd
      teich := (Y.rawSelf p).teich_mem V g
      Vm := (Y.rawSelf p).V_mem V g
      Fm := (Y.rawSelf p).F_mem V g (Y.self_chart_log_constantCoeff p) (Y.rawSelf_exlg p) hζ h0 hadd
      sumV := (Y.rawSelf p).sumV_mem V g (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_exlg p) (Y.rawSelf_lgex p) h0 hadd
      t2 := (Y.rawSelf p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.rawSelf_lin p) (Y.rawSelf_axis0 p) (Y.exists_integral_right_inverse p g) (hStab C V O dd Y d I0 p g)
      t3 := (Y.rawSelf p).const_mem_type_set_of_nonneg (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
      t4 := hPT C V O dd Y d I0 p g }

end Formalism.L2.FormalSeriesBounds
