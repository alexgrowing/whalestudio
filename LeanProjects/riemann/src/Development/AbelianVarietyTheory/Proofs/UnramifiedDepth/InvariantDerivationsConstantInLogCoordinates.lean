import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InvDerivLog

open MvPowerSeries GlobalTheory.RowLawSquare ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {C : Type} [Field C] {dd : ℕ} {τ : Type}

theorem pderiv_substPointsPowerSeries_one {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (f : PS C 1 dd) (t : τ) :
    pderiv C t (sb ![a] f) = ∑ l, sb ![a] (pderiv C ((0 : Fin 1), l) f) * pderiv C t (a l) := by
  unfold sb
  rw [pderiv_subst (fun p : Fin 1 × Fin dd => zc1 ha p.1 p.2), Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem pderiv_substPointsPowerSeries_two {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (f : PS C 2 dd) (t : τ) :
    pderiv C t (sb ![a, b] f) = ∑ l, sb ![a, b] (pderiv C ((0 : Fin 2), l) f) * pderiv C t (a l) +
      ∑ l, sb ![a, b] (pderiv C ((1 : Fin 2), l) f) * pderiv C t (b l) := by
  unfold sb
  rw [pderiv_subst (fun p : Fin 2 × Fin dd => zc2 ha hb p.1 p.2), Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

theorem sb_mul {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) (f g : PS C n dd) :
    sb a (f * g) = sb a f * sb a g := subst_mul (hasSubst_sb ha) f g

theorem sb_sum {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) {α : Type} (s : Finset α)
    (f : α → PS C n dd) : sb a (∑ x ∈ s, f x) = ∑ x ∈ s, sb a (f x) := by
  unfold sb
  simp only [← coe_substAlgHom (hasSubst_sb ha), map_sum]

theorem sb_zero {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j)) :
    sb a (0 : PS C n dd) = 0 := by
  unfold sb
  simp only [← coe_substAlgHom (hasSubst_sb ha), map_zero]

theorem sb_C {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (c : C) :
    sb a (MvPowerSeries.C c : PS C n dd) = MvPowerSeries.C c := by
  unfold sb
  rw [subst_C]

theorem zc_zero : Zc (0 : Fin dd → MvPowerSeries τ C) := fun _ => map_zero _

theorem sb_zeroPt (f : PS C 1 dd) :
    sb ![(0 : Fin dd → MvPowerSeries τ C)] f = MvPowerSeries.C (constantCoeff f) := by
  classical
  have hz := hasSubst_sb (zc1 (zc_zero (C := C) (dd := dd) (τ := τ)))
  ext e
  unfold sb
  rw [coeff_subst hz, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp), map_zero, smul_zero]
    obtain ⟨j, i⟩ := p
    fin_cases j
    exact zero_pow hp

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

theorem zc_ex {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) : Zc (fun x => sb ![a] (Y.ex x)) :=
  fun x => cc_sb (zc1 ha) (Y.ex_const x)

theorem law_ex {a b : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (j : Fin dd) :
    sb ![fun x => sb ![a] (Y.ex x), fun x => sb ![b] (Y.ex x)] (Y.B.G.F j) = sb ![a + b] (Y.ex j) := by
  have h1 := ex_lg Y (zc_law Y (zc_ex Y ha) (zc_ex Y hb)) j
  simp only [← lg_law Y (zc_ex Y ha) (zc_ex Y hb), lg_ex Y ha, lg_ex Y hb] at h1
  exact h1.symm

theorem cc_pderiv_lg (i l : Fin dd) :
    constantCoeff (pderiv C ((0 : Fin 1), i) (Y.lg l)) = if l = i then 1 else 0 := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, Y.lg_lin l _ (by simp), coeff_X]
  by_cases h : l = i
  · subst h; simp
  · rw [if_neg h, if_neg, zero_mul]
    intro h2
    rw [zero_add, Finsupp.single_left_inj one_ne_zero] at h2
    exact h (Prod.ext_iff.1 h2).2.symm

theorem cc_pderiv_ex (i l : Fin dd) :
    constantCoeff (pderiv C ((0 : Fin 1), i) (Y.ex l)) = if l = i then 1 else 0 := by
  classical
  have e : sb ![Y.ex] (Y.lg l) = X ((0 : Fin 1), l) := congrFun Y.lg_ex l
  have e2 := congrArg (fun f => constantCoeff (pderiv C ((0 : Fin 1), i) f)) e
  have hz : Zc Y.ex := Y.ex_const
  simp only [pderiv_substPointsPowerSeries_one hz, map_sum, map_mul] at e2
  have h3 : ∀ x, constantCoeff (sb ![Y.ex] (pderiv C ((0 : Fin 1), x) (Y.lg l))) = if l = x then 1 else 0 :=
    fun x => by
      unfold sb
      rw [cc_subst (fun p : Fin 1 × Fin dd => zc1 hz p.1 p.2), cc_pderiv_lg]
  simp only [h3, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at e2
  rw [e2]
  by_cases h : l = i
  · subst h; simp
  · rw [if_neg h, pderiv_X_of_ne (by simpa using h), map_zero]

theorem inv_field_ex {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (i j : Fin dd) :
    sb ![fun x => sb ![a] (Y.ex x), 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) =
      sb ![a] (pderiv C ((0 : Fin 1), i) (Y.ex j)) := by
  classical
  have z0 : Zc (pt C (n := 2) dd 0) := zc_pt 0
  have z1 : Zc (pt C (n := 2) dd 1) := zc_pt 1
  have zs : Zc (pt C (n := 2) dd 0 + pt C (n := 2) dd 1) := fun x => by
    rw [Pi.add_apply, map_add, z0 x, z1 x, add_zero]
  have d0 : ∀ l, pderiv C ((1 : Fin 2), i) (pt C (n := 2) dd 0 l) = 0 := fun l =>
    pderiv_X_of_ne (by simp)
  have d1 : ∀ l, pderiv C ((1 : Fin 2), i) (pt C (n := 2) dd 1 l) = if l = i then 1 else 0 := fun l => by
    by_cases h : l = i
    · subst h; rw [if_pos rfl]; exact pderiv_X_self
    · rw [if_neg h]; exact pderiv_X_of_ne (by simpa using h)
  have e := congrArg (pderiv C ((1 : Fin 2), i)) (law_ex Y z0 z1 j)
  rw [pderiv_substPointsPowerSeries_two (zc_ex Y z0) (zc_ex Y z1), pderiv_substPointsPowerSeries_one zs] at e
  simp only [pderiv_substPointsPowerSeries_one z0, pderiv_substPointsPowerSeries_one z1, Pi.add_apply, map_add, d0, d1, mul_zero, Finset.sum_const_zero,
    zero_add, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  have h2 := zc2 ha (zc_zero (C := C) (dd := dd) (τ := τ))
  have s1 : ∀ {b : Pt C 2 dd} (_ : Zc b) (f : PS C 1 dd),
      sb ![a, 0] (sb ![b] f) = sb ![fun i => sb ![a, 0] (b i)] f := fun hb f => substPointsPowerSeries_eval_one h2 hb f
  have s2 : ∀ {b c : Pt C 2 dd} (_ : Zc b) (_ : Zc c) (f : PS C 2 dd),
      sb ![a, 0] (sb ![b, c] f) = sb ![fun i => sb ![a, 0] (b i), fun i => sb ![a, 0] (c i)] f :=
    fun hb hc f => substPointsPowerSeries_eval_two h2 hb hc f
  have e2 := congrArg (sb ![a, 0]) e
  have p0 : (fun i => sb ![a, 0] (pt C dd 0 i)) = a := sb_pt' h2 0
  have p1 : (fun i => sb ![a, 0] (pt C dd 1 i)) = 0 := sb_pt' h2 1
  have ps : (fun i => sb ![a, 0] ((pt C (n := 2) dd 0 + pt C (n := 2) dd 1) i)) = a := by
    funext x
    rw [Pi.add_apply, sb_add h2, congrFun p0 x, congrFun p1 x, Pi.zero_apply, add_zero]
  have c0 : (fun x => (MvPowerSeries.C (constantCoeff (Y.ex x)) : MvPowerSeries τ C)) = 0 := by
    funext x
    rw [Y.ex_const, map_zero, Pi.zero_apply]
  rw [sb_sum h2, s1 zs, ps] at e2
  simp only [sb_mul h2, s2 (zc_ex Y z0) (zc_ex Y z1), s1 z0, s1 z1, p0, p1, sb_zeroPt, c0, cc_pderiv_ex,
    apply_ite MvPowerSeries.C, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at e2
  exact e2

theorem subst_ex_DofN : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv C w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv C w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  classical
  intro C _ _ V O _ _ dd Y n W _ Z hZ b u co hco G
  have hz : ∀ b' : Fin n, Zc (fun j => Z (b', j)) := fun b' j => hZ _
  let E : Fin n → Fin dd → MvPowerSeries W C := fun b' x => sb ![fun j => Z (b', j)] (Y.ex x)
  have hE : ∀ b', Zc (E b') := fun b' => zc_ex Y (hz b')
  have eE : (fun s : Fin n × Fin dd => subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) =
      fun s => E s.1 s.2 := by
    funext s
    rw [subst_singlePointUncurry (hz s.1)]
    show _ = sb _ _
    unfold sb
    congr 1
    funext ⟨j, i⟩
    fin_cases j
    rfl
  rw [eE]
  show sb E _ = ∑ w, co w • pderiv C w (sb E G)
  have hD : ∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • pderiv C w (E b' j) = if b' = b then
      ∑ i, MvPowerSeries.C (u i) * sb ![fun j => Z (b, j)] (pderiv C ((0 : Fin 1), i) (Y.ex j)) else 0 := by
    intro b' j
    simp only [E, pderiv_substPointsPowerSeries_one (hz b'), Finset.smul_sum, ← mul_smul_comm]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hco]
    split_ifs with h
    · subst h
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  have hR : ∑ w, co w • pderiv C w (sb E G) =
      ∑ p : Fin n × Fin dd, sb E (pderiv C p G) * ∑ w, co w • pderiv C w (E p.1 p.2) := by
    unfold sb
    simp only [pderiv_subst (a := fun p : Fin n × Fin dd => E p.1 p.2) (fun p => hE p.1 p.2), Finset.smul_sum,
      ← mul_smul_comm, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hR, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · unfold DofN
    rw [sb_sum hE]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hD, if_pos rfl, sb_mul hE, mul_comm, sb_sum hE]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sb_mul hE, sb_C, substPointsPowerSeries_eval_two hE (zc_pt b) zc_zero, sb_pt' hE, FK_self, ← inv_field_ex Y (hz b)]
    have : (fun i : Fin dd => sb E ((0 : Pt C n dd) i)) = 0 := funext fun _ => sb_zero hE
    rw [this]
  · intro b' _ h
    simp [hD, h]
  · simp

end GlobalTheory.InvDerivLog
