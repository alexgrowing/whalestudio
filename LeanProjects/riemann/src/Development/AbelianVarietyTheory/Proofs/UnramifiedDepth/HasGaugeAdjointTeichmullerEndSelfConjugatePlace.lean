import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimitStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusLiftEmbeddingsUnitStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

section Double

open MvPowerSeries

variable {C : Type} [Field C]

theorem teichSelf_intS_mul {V : VF C} {τ : Type} {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) :
    IntS V (f * g) := by
  classical
  intro μ
  rw [coeff_mul]
  exact VF.Ge.sum fun p _ => (hf _).mul_int (hg _)

theorem teichSelf_intS_one {V : VF C} {τ : Type} : IntS V (1 : MvPowerSeries τ C) := by
  classical
  intro μ
  rw [coeff_one]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem teichSelf_intS_X {V : VF C} {τ : Type} (t : τ) : IntS V (X t : MvPowerSeries τ C) := by
  classical
  intro μ
  rw [coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem teichSelf_intS_pow {V : VF C} {τ : Type} {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) :
    IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact teichSelf_intS_one
  | succ n ih => rw [pow_succ]; exact teichSelf_intS_mul ih hf

theorem teichSelf_intS_subst {V : VF C} {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (h0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C} (hF : IntS V F) :
    IntS V (subst a F) := by
  intro μ
  rw [coeff_subst (hasSubst_of_constantCoeff_zero h0)]
  refine finsum_induction (fun x => V.Ge 0 x) (VF.Ge.zero 0) (fun _ _ => VF.Ge.add) fun e => ?_
  rw [smul_eq_mul]
  refine (hF e).mul_int ((?_ : IntS V (e.prod fun s n => a s ^ n)) μ)
  exact Finset.prod_induction _ (IntS V) (fun _ _ => teichSelf_intS_mul) teichSelf_intS_one
    fun s _ => teichSelf_intS_pow (ha s) _

theorem teichSelf_mvExp_eq [CharZero C] {τ : Type} {f : MvPowerSeries τ C} (hf : constantCoeff f = 0) :
    mvExp f = PowerSeries.subst f (PowerSeries.exp C) := by
  ext m
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · show ∑ k ∈ Finset.range (m.degree + 1), coeff m (f ^ k) / (k.factorial : C) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    apply hk
    rw [coeff_of_lt_order, smul_zero]
    refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero k hf)
    exact_mod_cast (by omega : m.degree < k)

theorem teichSelf_subst_mvExp [CharZero C] {σ τ : Type} (b : σ → MvPowerSeries τ C) [Finite σ]
    (hb : ∀ s, constantCoeff (b s) = 0) {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    subst b (mvExp f) = mvExp (subst b f) := by
  rw [teichSelf_mvExp_eq hf, teichSelf_mvExp_eq (constantCoeff_subst_zero hb hf)]
  simp only [PowerSeries.subst_def]
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hf) (hasSubst_of_constantCoeff_zero hb)]

theorem teichSelf_mvExp_add [CharZero C] {τ : Type} {x y : MvPowerSeries τ C} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : mvExp (x + y) = mvExp x * mvExp y := by
  have h0 : ∀ s, constantCoeff ((![x, y] : Fin 2 → MvPowerSeries τ C) s) = 0 := by
    intro s; fin_cases s <;> simp [hx, hy]
  have hb := hasSubst_of_constantCoeff_zero h0
  have c01 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) C) = 0 := by simp
  have c0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) C) = 0 := by simp
  have c1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) C) = 0 := by simp
  have := congrArg (subst (![x, y] : Fin 2 → MvPowerSeries τ C)) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars C)
  rw [← teichSelf_mvExp_eq c01, ← teichSelf_mvExp_eq c0, ← teichSelf_mvExp_eq c1, subst_mul hb,
    teichSelf_subst_mvExp _ h0 c01, teichSelf_subst_mvExp _ h0 c0, teichSelf_subst_mvExp _ h0 c1,
    subst_add hb, subst_X hb, subst_X hb] at this
  simpa using this

variable {d d' dd : ℕ} {I I' : Fin 2 → Type}

theorem teichSelf_cc_lin {κ τ : Type} [Fintype κ] (X : RawChart C d I κ) (hlg : ∀ i, constantCoeff (X.lg i) = 0)
    (M : Matrix κ κ C) (a : κ → MvPowerSeries τ C) (ha : ∀ i, constantCoeff (a i) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_subst_zero ha (hlg y), mul_zero]

theorem teichSelf_cc_endP {κ τ : Type} [Fintype κ] (X : RawChart C d I κ) (hlg : ∀ i, constantCoeff (X.lg i) = 0)
    (hex : ∀ i, constantCoeff (X.ex i) = 0)
    (M : Matrix κ κ C) (a : κ → MvPowerSeries τ C) (ha : ∀ i, constantCoeff (a i) = 0) (x : κ) :
    constantCoeff (endP X M a x) = 0 :=
  constantCoeff_subst_zero (teichSelf_cc_lin X hlg M a ha) (hex x)

theorem teichSelf_subst_endP {κ τ υ : Type} [Fintype κ] [Finite τ] (X : RawChart C d I κ)
    (hlg : ∀ i, constantCoeff (X.lg i) = 0)
    (M : Matrix κ κ C) (a : κ → MvPowerSeries τ C) (ha : ∀ i, constantCoeff (a i) = 0)
    (b : τ → MvPowerSeries υ C) (hb : ∀ i, constantCoeff (b i) = 0) (x : κ) :
    subst b (endP X M a x) = endP X M (fun y => subst b (a y)) x := by
  have hB := hasSubst_of_constantCoeff_zero hb
  unfold endP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (teichSelf_cc_lin X hlg M a ha)) hB]
  congr 1
  funext z
  rw [← coe_substAlgHom hB, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul, coe_substAlgHom hB, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hB]

theorem teichSelf_cc_pair {κ τ : Type} (a b : κ → MvPowerSeries τ C) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  · exact ha _
  · exact hb _

theorem teichSelf_subst_hAt {κ τ υ : Type} [Fintype κ] [Finite τ] (X : RawChart C d I κ)
    (a a' : κ → MvPowerSeries τ C) (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ i, constantCoeff (a' i) = 0)
    (b : τ → MvPowerSeries υ C) (hb : ∀ i, constantCoeff (b i) = 0) :
    subst b (hAt X a a') = hAt X (fun y => subst b (a y)) (fun y => subst b (a' y)) := by
  have hB := hasSubst_of_constantCoeff_zero hb
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (teichSelf_cc_pair a a' ha ha')) hB]
  congr 1
  funext z
  split_ifs <;> rfl

theorem teichSelf_subst_inCol [CharZero C] {τ : Type} (a : Fin 2 × Fin dd → MvPowerSeries τ C)
    (ha : ∀ i, constantCoeff (a i) = 0) (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun y => a (col, y)) f := by
  have hA := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext z
  rw [subst_X hA]

theorem teichSelf_endP_col [CharZero C] {τ : Type} (X : RawChart C d I (Fin dd)) (X' : RawChart C d' I' (Fin 2 × Fin dd))
    (hlg : ∀ i, constantCoeff (X.lg i) = 0)
    (e1 : X'.lg = fun x => inCol x.1 (X.lg x.2)) (e2 : X'.ex = fun x => inCol x.1 (X.ex x.2))
    (M : Matrix (Fin dd) (Fin dd) C) (a : Fin 2 × Fin dd → MvPowerSeries τ C) (ha : ∀ i, constantCoeff (a i) = 0)
    (x : Fin 2 × Fin dd) :
    endP X' (fun x y => if x.1 = y.1 then M x.2 y.2 else 0) a x = endP X M (fun y => a (x.1, y)) x.2 := by
  have hlg' : ∀ i, constantCoeff (X'.lg i) = 0 := by
    intro i
    rw [e1]
    exact constantCoeff_subst_zero (fun _ => constantCoeff_X _) (hlg _)
  have h := teichSelf_cc_lin X' hlg' (fun x y => if x.1 = y.1 then M x.2 y.2 else 0) a ha
  unfold endP
  rw [e2]
  show subst _ (inCol x.1 (X.ex x.2)) = _
  rw [teichSelf_subst_inCol _ h]
  congr 1
  funext z
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [e1]
    show (if x.1 = x.1 then M z y else 0) • subst a (inCol x.1 (X.lg y)) = _
    rw [if_pos rfl, teichSelf_subst_inCol _ ha]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem teichSelf_hAt_col [CharZero C] {τ : Type} (X : RawChart C d I (Fin dd)) (X' : RawChart C d' I' (Fin 2 × Fin dd))
    (e3 : X'.h = ∑ col, hCol col X.h) (a b : Fin 2 × Fin dd → MvPowerSeries τ C)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    hAt X' a b = ∑ col : Fin 2, hAt X (fun y => a (col, y)) (fun y => b (col, y)) := by
  have hA := hasSubst_of_constantCoeff_zero (teichSelf_cc_pair a b ha hb)
  unfold hAt
  rw [e3, ← coe_substAlgHom hA, map_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [coe_substAlgHom hA]
  unfold hCol
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext z
  rw [subst_X hA]

end Double

theorem teichSelf_double : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (dd d d' : ℕ) (I I' : Fin 2 → Type) (X : RawChart C d I (Fin dd)) (X' : RawChart C d' I' (Fin 2 × Fin dd)), (∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0) → (∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0) → MvPowerSeries.constantCoeff X.h = 0 → (X'.lg = fun x => inCol x.1 (X.lg x.2)) → (X'.ex = fun x => inCol x.1 (X.ex x.2)) → X'.h = ∑ col, hCol col X.h → ∀ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' → IsEnd X' V (fun x y => if x.1 = y.1 then M x.2 y.2 else 0) (fun x y => if x.1 = y.1 then M' x.2 y.2 else 0) := by
  intro C _ _ V dd d d' I I' X X' hlg hex hh e1 e2 e3 M M' ⟨h1, h2, h3⟩
  have one : ∀ T : Matrix (Fin dd) (Fin dd) C,
      (∀ i, IntS V (endP X T (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) i)) →
      ∀ x, IntS V (endP X' (fun x y => if x.1 = y.1 then T x.2 y.2 else 0)
        (MvPowerSeries.X : _ → MvPowerSeries (Fin 2 × Fin dd) C) x) := by
    intro T hT x
    rw [teichSelf_endP_col X X' hlg e1 e2 T _ (fun _ => MvPowerSeries.constantCoeff_X _)]
    have c : ∀ y : Fin dd, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (x.1, y) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun _ => MvPowerSeries.constantCoeff_X _
    have := teichSelf_intS_subst _ c (fun _ => teichSelf_intS_X _) (hT x.2)
    rw [teichSelf_subst_endP X hlg T _ (fun _ => MvPowerSeries.constantCoeff_X _) _ c] at this
    simpa only [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero c)] using this
  refine ⟨one M h1, one M' h2, ?_⟩
  have cg : ∀ (κ : Type) (j : Fin 2) (i : κ), MvPowerSeries.constantCoeff (gp C κ j i) = 0 :=
    fun _ _ _ => MvPowerSeries.constantCoeff_X _
  have hlg' : ∀ i, MvPowerSeries.constantCoeff (X'.lg i) = 0 := by
    intro i
    rw [e1]
    exact constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hlg _)
  have hex' : ∀ i, MvPowerSeries.constantCoeff (X'.ex i) = 0 := by
    intro i
    rw [e2]
    exact constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hex _)
  set D := hAt X (endP X M (gp C (Fin dd) (0 : Fin 2))) (gp C (Fin dd) 1) -
    hAt X (gp C (Fin dd) 0) (endP X M' (gp C (Fin dd) 1)) with hD
  have c1 := teichSelf_cc_endP X hlg hex M _ (cg (Fin dd) 0)
  have c2 := teichSelf_cc_endP X hlg hex M' _ (cg (Fin dd) 1)
  have cD : MvPowerSeries.constantCoeff D = 0 := by
    rw [hD, map_sub]
    unfold hAt
    rw [constantCoeff_subst_zero (teichSelf_cc_pair _ _ c1 (cg _ 1)) hh,
      constantCoeff_subst_zero (teichSelf_cc_pair _ _ (cg _ 0) c2) hh, sub_zero]
  let φ : Fin 2 → Fin 2 × Fin dd → MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C :=
    fun col p => MvPowerSeries.X (p.1, (col, p.2))
  have cφ : ∀ col p, MvPowerSeries.constantCoeff (φ col p) = 0 := fun _ _ => MvPowerSeries.constantCoeff_X _
  have key : hAt X' (endP X' (fun x y => if x.1 = y.1 then M x.2 y.2 else 0) (gp C (Fin 2 × Fin dd) (0 : Fin 2)))
        (gp C (Fin 2 × Fin dd) 1) -
      hAt X' (gp C (Fin 2 × Fin dd) 0)
        (endP X' (fun x y => if x.1 = y.1 then M' x.2 y.2 else 0) (gp C (Fin 2 × Fin dd) 1)) =
      ∑ col, MvPowerSeries.subst (φ col) D := by
    rw [teichSelf_hAt_col X X' e3 _ _ (teichSelf_cc_endP X' hlg' hex' (fun x y => if x.1 = y.1 then M x.2 y.2 else 0) _ (cg _ 0)) (cg _ 1),
      teichSelf_hAt_col X X' e3 _ _ (cg _ 0) (teichSelf_cc_endP X' hlg' hex' (fun x y => if x.1 = y.1 then M' x.2 y.2 else 0) _ (cg _ 1)),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun col _ => ?_
    have hφ := MvPowerSeries.hasSubst_of_constantCoeff_zero (cφ col)
    have eg : ∀ (j : Fin 2) (y : Fin dd), MvPowerSeries.subst (φ col) (gp C (Fin dd) j y) =
        gp C (Fin 2 × Fin dd) j (col, y) := fun j y => MvPowerSeries.subst_X hφ _
    rw [hD, ← MvPowerSeries.coe_substAlgHom hφ, map_sub, MvPowerSeries.coe_substAlgHom hφ,
      teichSelf_subst_hAt X _ _ c1 (cg _ 1) _ (cφ col), teichSelf_subst_hAt X _ _ (cg _ 0) c2 _ (cφ col)]
    simp only [teichSelf_subst_endP X hlg _ _ (cg _ _) _ (cφ col), eg,
      teichSelf_endP_col X X' hlg e1 e2 _ _ (cg _ _)]
  rw [key, Fin.sum_univ_two, teichSelf_mvExp_add (constantCoeff_subst_zero (cφ 0) cD)
    (constantCoeff_subst_zero (cφ 1) cD), ← teichSelf_subst_mvExp _ (cφ 0) cD, ← teichSelf_subst_mvExp _ (cφ 1) cD]
  exact teichSelf_intS_mul (teichSelf_intS_subst _ (cφ 0) (fun _ => teichSelf_intS_X _) h3)
    (teichSelf_intS_subst _ (cφ 1) (fun _ => teichSelf_intS_X _) h3)

theorem teichSelf_eq_zero {C : Type} [Field C] {V : VF C} {x : C} (h : ∀ K : ℕ, V.Ge K x) : x = 0 := by
  by_contra hx
  have h1 : V.v x ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]; exact hx
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h1
  obtain ⟨K, hK⟩ := exists_nat_gt t
  have := h K
  unfold VF.Ge at this
  rw [← ht] at this
  have : (K : ℝ) ≤ t := by exact_mod_cast this
  linarith

theorem teichSelf_eig {C : Type} [Field C] {V : VF C} {dd : ℕ} (w e : Fin dd → C) (he : ∀ i, V.Ge 0 (e i))
    (z : C) (s : ℕ → C) (hs : ∀ K : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge K (z - s n))
    (hw : ∀ (K : ℕ) i, ∃ n0, ∀ n ≥ n0, V.Ge K (w i - s n * e i)) (i : Fin dd) : w i = z * e i := by
  rw [← sub_eq_zero]
  refine teichSelf_eq_zero (V := V) fun K => ?_
  obtain ⟨n0, h0⟩ := hs K
  obtain ⟨n1, h1⟩ := hw K i
  have := (h1 (max n0 n1) (le_max_right _ _)).sub ((he i).mul_int (h0 (max n0 n1) (le_max_left _ _)))
  convert this using 1
  ring

theorem teichSelf_mulVec {C : Type} [Field C] {dd : ℕ} (M : Matrix (Fin dd) (Fin dd) C) (c : Fin 2 → C)
    (e : Fin dd → C) (z : C) (h : ∀ i, M.mulVec e i = z * e i) :
    Matrix.mulVec (fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M x.2 y.2 else 0) (fun x => c x.1 * e x.2) =
      z • fun x : Fin 2 × Fin dd => c x.1 * e x.2 := by
  funext x
  have h1 := h x.2
  simp only [Matrix.mulVec, dotProduct] at h1 ⊢
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
  · simp only [if_true, Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, ← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem hasTeich_selfData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∀ g, HasTeich (Y.rawSelf p) V g := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g
  obtain ⟨N, ζ, s, hN, hζ, hinj, hfr, hs, hlim⟩ := GlobalTheory.T.frobenius_lift_embeddings_unit C V Y.cpl O d p.em p.em_int p.em_frob p.em_sep p.em_unr
  let X : RawChart C d (fun _ => I0) (Fin dd) :=
    { lg := fun i => un1 (Y.lg i), ex := fun i => un1 (Y.ex i), h := Y.h, k := 0, u := fun _ => p.e,
      ty := fun _ => p.ty0, n := 0, j := 0, j' := 0, big := fun _ _ => True }
  obtain ⟨M, M', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_integralEnd_of_ladic_action_limit C V O dd Y d _ X rfl rfl rfl s hs
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
  have e1 := teichSelf_double C V dd d d _ _ X (Y.rawSelf p) hlg hex hh rfl rfl rfl M M' h1
  have e2 := teichSelf_double C V dd d d _ _ X (Y.rawSelf p) hlg hex hh rfl rfl rfl M' M h2
  have m1 : ∀ c i, M.mulVec (p.e c) i = ζ (p.ty0 c) * p.e c i := fun c =>
    teichSelf_eig _ _ (p.e_int c) _ _ (hlim (p.ty0 c)) fun K i => by
      simpa only [p.e_eig, Pi.smul_apply, smul_eq_mul] using h3 K (p.e c) i
  have m2 : ∀ c i, M'.mulVec (p.e c) i = ζ (p.ty0 c + p.hd) * p.e c i := fun c =>
    teichSelf_eig _ _ (p.e_int c) _ _ (hlim (p.ty0 c + p.hd)) fun K i => by
      simpa only [p.e_eig, Pi.smul_apply, smul_eq_mul, p.em_conj] using h4 K (p.e c) i
  fin_cases g
  · exact ⟨N, ζ, _, _, hN, hζ, hinj, hfr, e1,
      fun c => teichSelf_mulVec M (fun r => p.gm (p.ty0 c) r 0) (p.e c) _ (m1 c),
      fun c => teichSelf_mulVec M' (fun r => p.gm (p.ty0 c) r 1) (p.e c) _ (m2 c)⟩
  · exact ⟨N, ζ, _, _, hN, hζ, hinj, hfr, e2,
      fun c => teichSelf_mulVec M' (fun r => p.gm (p.ty0 c) r 1) (p.e c) _ (m2 c),
      fun c => teichSelf_mulVec M (fun r => p.gm (p.ty0 c) r 0) (p.e c) _ (m1 c)⟩

end GlobalTheory
