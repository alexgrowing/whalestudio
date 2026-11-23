import Formalism.LocalToGlobal.CharacterGerms.CoeffOneSubstCurve
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroCompCoordinate
import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace PairPointEvaluation

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence FirstVanishing SelfAdjointCongruence MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constant_zero_pair_points {a b : Pt C 1 dd} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0) :
    Z0 (![a, b] : Fin 2 → Pt C 1 dd) := by
  intro k i
  fin_cases k
  · simpa using ha i
  · simpa using hb i

theorem eval_single_comp {a b : Pt C 1 dd} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0)
    (f : PS C 1 dd) : ev (n := 1) ![a] (ev (n := 1) ![b] f) = ev (n := 1) ![comp1 b a] f := by
  rw [ev_ev (z0_1 b hb) (z0_1 a ha)]
  congr 1
  funext k i
  fin_cases k
  rfl

theorem hom_at (G : FGLaw C dd) {e : Pt C 1 dd} (he0 : ∀ j, constantCoeff (e j) = 0)
    (hhom : comp1 e (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {a b : Pt C 1 dd} (ha : ∀ j, constantCoeff (a j) = 0) (hb : ∀ j, constantCoeff (b j) = 0) :
    comp1 e (addOf G.F a b) = addOf G.F (comp1 e a) (comp1 e b) := by
  funext i
  have hab := constant_zero_pair_points ha hb
  have h := congrArg (ev (n := 1) ![a, b]) (congrFun hhom i)
  have hadd0 : ∀ j, constantCoeff (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => const_ev (z0_pp 0 1) (G.const j)
  have hc : ∀ (k : Fin 2) j, constantCoeff (comp1 e (pt C (n := 2) dd k) j) = 0 :=
    fun k j => const_ev (z0_1 _ (z0_pt k)) (he0 j)
  have hcc : Z0 (![comp1 e (pt C (n := 2) dd 0), comp1 e (pt C (n := 2) dd 1)] : Fin 2 → Pt C 2 dd) := fun k j => by
    fin_cases k
    · exact hc 0 j
    · exact hc 1 j
  have hL : ev (n := 1) ![a, b] (comp1 e (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) i) =
      comp1 e (addOf G.F a b) i := by
    show ev (n := 1) ![a, b] (ev ![addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] (e i)) =
      ev ![addOf G.F a b] (e i)
    rw [ev_ev (z0_1 _ hadd0) hab]
    congr 1
    funext k j
    fin_cases k
    show ev (n := 1) ![a, b] (ev (n := 2) ![pt C dd 0, pt C dd 1] (G.F j)) = ev ![a, b] (G.F j)
    rw [PartialDerivEval.eval_points_two]
  have hR : ev (n := 1) ![a, b] (addOf G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)) i) =
      addOf G.F (comp1 e a) (comp1 e b) i := by
    show ev (n := 1) ![a, b] (ev ![comp1 e (pt C (n := 2) dd 0), comp1 e (pt C (n := 2) dd 1)] (G.F i)) =
      ev ![comp1 e a, comp1 e b] (G.F i)
    rw [ev_ev hcc hab]
    congr 1
    funext k j
    fin_cases k
    · show ev (n := 1) ![a, b] (ev ![pt C (n := 2) dd 0] (e j)) = ev ![a] (e j)
      rw [ev_ev (z0_1 _ (z0_pt 0)) hab]
      congr 1
      funext k' j'
      fin_cases k'
      exact ev_X hab 0 j'
    · show ev (n := 1) ![a, b] (ev ![pt C (n := 2) dd 1] (e j)) = ev ![b] (e j)
      rw [ev_ev (z0_1 _ (z0_pt 1)) hab]
      congr 1
      funext k' j'
      fin_cases k'
      exact ev_X hab 1 j'
  rw [← hL, ← hR]
  exact h

theorem mulL_comm (G : FGLaw C dd) {e : Pt C 1 dd} (he0 : ∀ j, constantCoeff (e j) = 0)
    (hhom : comp1 e (addOf G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1))) (n : ℕ) :
    comp1 (mulL G.F n) e = comp1 e (mulL G.F n) := by
  induction n with
  | zero =>
    funext i
    show ev ![e] (0 : PS C 1 dd) = ev ![(0 : Pt C 1 dd)] (e i)
    rw [MulLFrob.ev_zero_pt, he0 i, map_zero, ev_zero (z0_1 e he0)]
  | succ n ih =>
    have hm0 := FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero G n
    have h1 : comp1 (mulL G.F (n + 1)) e = addOf G.F (comp1 (mulL G.F n) e) e := by
      funext i
      show ev ![e] (ev ![mulL G.F n, pt C dd 0] (G.F i)) = ev ![comp1 (mulL G.F n) e, e] (G.F i)
      rw [ev_ev (constant_zero_pair_points hm0 (z0_pt 0)) (z0_1 e he0)]
      congr 1
      funext k j
      fin_cases k
      · rfl
      · exact ev_X (z0_1 e he0) 0 j
    have h2 : comp1 e (mulL G.F (n + 1)) = addOf G.F (comp1 e (mulL G.F n)) e := by
      show comp1 e (addOf G.F (mulL G.F n) (pt C dd 0)) = _
      rw [hom_at G he0 hhom hm0 (z0_pt 0)]
      congr 1
      funext i
      exact MulLFrob.germEval_oneStandardPoint_self (e i)
    rw [h1, h2, ih]

theorem idx_apply (μ : Fin 1 × Fin dd →₀ ℕ) (i j : Fin dd) :
    (μ.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) + Finsupp.single ((1 : Fin 2), j) 1 :
      Fin 2 × Fin dd →₀ ℕ) ((0 : Fin 2), i) = μ ((0 : Fin 1), i) := by
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) := by
    intro p q h
    have h' : ((0 : Fin 2), p.2) = ((0 : Fin 2), q.2) := h
    exact Prod.ext (Subsingleton.elim _ _) (Prod.mk.inj h').2
  have hne : ((1 : Fin 2), j) ≠ ((0 : Fin 2), i) := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    intro h
    exact h10 (congrArg Prod.fst h)
  rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hne, add_zero]
  exact Finsupp.mapDomain_apply hinj μ ((0 : Fin 1), i)

theorem aLin_eq (Y : FBChart C V O dd) (u w : Fin dd → C) :
    Y.aLin u w = ∑ i, coeff (Finsupp.single ((0 : Fin 1), i) V.l) (zl w Y.u1) * u i ^ V.l := by
  simp only [coeff_zl, Finsupp.mapDomain_single]
  unfold FBChart.aLin
  have h : ∀ j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.aOf u) =
      ∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l + Finsupp.single ((1 : Fin 2), j) 1) Y.u1 := by
    intro j
    show ∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l +
      (Finsupp.single ((0 : Fin 1), j) 1).mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1 = _
    rw [Finsupp.mapDomain_single]
  simp only [h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem intS_zl {w : Fin dd → C} (hw : ∀ i, V.Ge 0 (w i)) {F : PS C 2 dd} (hF : IntS V F) : IntS V (zl w F) := by
  intro ν
  rw [coeff_zl]
  exact VF.Ge.sum fun j _ => VF.Ge.mul_int (hw j) (hF _)

theorem linear_part_unit_frobenius (Y : FBChart C V O dd) {w : Fin dd → C} (hw : ∀ i, V.Ge 0 (w i)) : FrobX V (zl w Y.u1) := by
  intro μ hμ
  obtain ⟨i, hi⟩ := hμ
  rw [coeff_zl]
  refine mm_sum _ _ fun j _ => mm_mul_ge' (hw j) (first_unit_series_frobenius C V O dd Y _ ⟨i, ?_⟩)
  rw [idx_apply]
  exact hi

end PairPointEvaluation

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence FirstVanishing SelfAdjointCongruence PairPointEvaluation MvPowerSeries in

theorem aLinAdj_holds : ALinAdjSt := by
  intro C _ _ V O _ _ dd Y e eb heI hebI he0 heb0 hhom hW u hu hV1 v hv
  have hl := V.l_prime.two_le
  obtain ⟨M, hMdef⟩ : ∃ M : Pt C 1 dd, M = mulL Y.B.G.F V.l := ⟨_, rfl⟩
  have hM0 : ∀ j, constantCoeff (M j) = 0 := fun j => by rw [hMdef]; exact FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l j
  have hMI : ∀ j, IntS V (M j) := fun j => by rw [hMdef]; exact FirstUnitSeriesIntegrality.mulL_int Y.B.G Y.intF V.l j
  have hMF : ∀ k, FrobX V (M k) := fun k μ hμ => by rw [hMdef]; exact mulLFrob_holds C V O dd Y k μ hμ
  obtain ⟨v', hv'def⟩ : ∃ v' : Fin dd → C, v' = linAct eb v := ⟨_, rfl⟩
  have hv' : ∀ i, V.Ge 0 (v' i) := fun i => by
    rw [hv'def]
    exact VF.Ge.sum fun j _ => VF.Ge.mul_int (hebI i _) (hv j)
  obtain ⟨T, hTdef⟩ : ∃ T : PS C 1 dd, T = zl v (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) := ⟨_, rfl⟩
  have hS : ∀ w, zl w Y.u1 = MvPowerSeries.C (V.l : C) * Y.sgP w - ev (n := 1) ![M] (Y.sgP w) := fun w => by
    rw [linear_part_first_unit, hMdef, MvPowerSeries.smul_eq_C_mul]
  have hT : T = Y.sgP v' - ev (n := 1) ![e] (Y.sgP v) := by
    rw [hTdef, constant_zero_first_zero_self Y e eb he0 heb0 v, hv'def]
  have hTI : IntS V T := by rw [hTdef]; exact intS_zl hv hW
  have hsg0 : ∀ w, constantCoeff (Y.sgP w) = 0 := fun w => OActSelf.cc_sgP Y w
  have hT0 : constantCoeff T = 0 := by
    rw [hT, map_sub, hsg0, const_ev (z0_1 e he0) (hsg0 v), sub_zero]
  have hS0 : ∀ w, constantCoeff (zl w Y.u1) = 0 := fun w => by
    rw [hS, map_sub, map_mul, hsg0, const_ev (z0_1 M hM0) (hsg0 w), mul_zero, sub_zero]
  have hSI : ∀ w, (∀ i, V.Ge 0 (w i)) → IntS V (zl w Y.u1) := fun w hw => intS_zl hw (first_unit_series_integral C V O dd Y)

  have key : ev (n := 1) ![e] (zl v Y.u1) + MvPowerSeries.C (V.l : C) * T = zl v' Y.u1 + ev (n := 1) ![M] T := by
    rw [hS, hS, hT, ev_sub (z0_1 e he0), ev_mul (z0_1 e he0), ev_C, ev_sub (z0_1 M hM0), eval_single_comp he0 hM0,
      eval_single_comp hM0 he0, hMdef, mulL_comm Y.B.G he0 hhom]
    ring

  obtain ⟨γ0, hγ0def⟩ : ∃ γ0 : Fin dd → PowerSeries C, γ0 = fun i => u i • (MvPowerSeries.X () : PowerSeries C) :=
    ⟨_, rfl⟩
  have hc : ∀ i n, PowerSeries.coeff n (γ0 i) = if n = 1 then u i else 0 := fun i n => by
    rw [hγ0def]
    show PowerSeries.coeff n (u i • (MvPowerSeries.X () : PowerSeries C)) = _
    rw [map_smul, coeffX', smul_eq_mul]
    split_ifs <;> simp
  have hcv0 : IsCv V γ0 := fun i => ⟨by
      have := hc i 0
      rw [if_neg (by omega)] at this
      rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this, fun n => by
      rw [hc]
      split_ifs
      · exact hu i
      · exact VF.Ge.zero 0⟩
  have hγz : ∀ j, constantCoeff (γ0 j) = 0 := fun j => (hcv0 j).1
  have hγI : ∀ j, IntS V (γ0 j) := fun j => intS_cv (hcv0 j).2
  have hG : HasSubst (fun q : Fin 1 × Fin dd => γ0 q.2) := hasSubst_of_constantCoeff_zero fun q => hγz q.2
  have hδ0 : ∀ φ : Pt C 1 dd, (∀ j, constantCoeff (φ j) = 0) →
      ∀ k, constantCoeff (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ k)) = 0 :=
    fun φ hφ k => constantCoeff_subst_eq_zero hG (fun q => hγz q.2) (hφ k)
  have hδI : ∀ φ : Pt C 1 dd, (∀ j, IntS V (φ j)) →
      ∀ k, IntS V (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ k)) :=
    fun φ hφ k => intS_subst (a := fun q : Fin 1 × Fin dd => γ0 q.2) (fun q => hγz q.2) (fun q => hγI q.2) (hφ k)
  have hδcv : ∀ φ : Pt C 1 dd, (∀ j, constantCoeff (φ j) = 0) → (∀ j, IntS V (φ j)) →
      IsCv V (fun k => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ k)) :=
    fun φ h0 hI k => ⟨hδ0 φ h0 k, fun n => hδI φ hI k (Finsupp.single () n)⟩
  have hcomp : ∀ φ : Pt C 1 dd, (∀ j, constantCoeff (φ j) = 0) → ∀ f : PS C 1 dd,
      subst (fun q : Fin 1 × Fin dd => γ0 q.2) (ev (n := 1) ![φ] f) =
        subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (φ q.2)) f := by
    intro φ hφ f
    have hφS : HasSubst (fun q : Fin 1 × Fin dd => φ q.2) := hasSubst_of_constantCoeff_zero fun q => hφ q.2
    rw [eval_single_eq_subst, subst_comp_subst_apply hφS hG]
  have k2 := congrArg (subst (fun q : Fin 1 × Fin dd => γ0 q.2)) key
  rw [subst_add hG, subst_add hG, ← MvPowerSeries.smul_eq_C_mul, subst_smul hG, hcomp e he0, hcomp M hM0] at k2
  have k3 := congrArg (PowerSeries.coeff V.l) k2
  rw [map_add, map_add, map_smul, smul_eq_mul] at k3

  have hA1 := coeff_l_frob (hSI v hv) (hS0 v) (linear_part_unit_frobenius Y hv) (hδcv e he0 heI)
  have hlin : ∀ i, PowerSeries.coeff 1 (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (e i)) = linAct e u i := fun i => by
    rw [coeff_one_subst_curve (he0 i) hγz]
    unfold linAct
    exact Finset.sum_congr rfl fun j _ => by rw [hc, if_pos rfl]
  simp only [hlin] at hA1
  rw [← aLin_eq] at hA1
  have hA3 := coeff_l_frob (hSI v' hv') (hS0 v') (linear_part_unit_frobenius Y hv') hcv0
  simp only [hc, if_pos] at hA3
  rw [← aLin_eq] at hA3
  have hA2 : V.MM ((V.l : C) * PowerSeries.coeff V.l (subst (fun q : Fin 1 × Fin dd => γ0 q.2) T)) :=
    mm_l_mul (intS_subst (a := fun q : Fin 1 × Fin dd => γ0 q.2) (fun q => hγz q.2) (fun q => hγI q.2) hTI
      (Finsupp.single () V.l))
  have hLow : ∀ k, LowMM V (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M k)) := by
    intro k n hn
    rcases Nat.lt_or_ge n V.l with h | h
    · exact coeff_lt_frob (hM0 k) (hMF k) hcv0 n h
    · have hnl : n = V.l := le_antisymm hn h
      subst hnl
      have h1 := coeff_l_frob (hMI k) (hM0 k) (hMF k) hcv0
      simp only [hc, if_pos] at h1
      have h2 := hV1 k
      rw [← hMdef] at h2
      have h3 := mm_add h1 h2
      rwa [sub_add_cancel] at h3
  have hA4 : V.MM (PowerSeries.coeff V.l
      (subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M q.2)) T)) :=
    lowMM_subst (a := fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M q.2))
      (fun q => hδ0 M hM0 q.2) (fun q => hδI M hMI q.2) (fun q => hLow q.2) hTI hT0 V.l le_rfl
  rw [← hv'def]
  obtain ⟨A1, hA1d⟩ : ∃ A1, A1 = PowerSeries.coeff V.l
    (subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (e q.2)) (zl v Y.u1)) := ⟨_, rfl⟩
  obtain ⟨A3, hA3d⟩ : ∃ A3, A3 = PowerSeries.coeff V.l (subst (fun q : Fin 1 × Fin dd => γ0 q.2) (zl v' Y.u1)) :=
    ⟨_, rfl⟩
  rw [← hA1d, ← hA3d] at k3
  rw [← hA1d] at hA1
  rw [← hA3d] at hA3
  have efin : Y.aLin (linAct e u) v - Y.aLin u v' =
      (A3 - Y.aLin u v') - (A1 - Y.aLin (linAct e u) v) + (A1 - A3) := by ring
  have e13 : A1 - A3 = PowerSeries.coeff V.l
      (subst (fun q : Fin 1 × Fin dd => subst (fun q : Fin 1 × Fin dd => γ0 q.2) (M q.2)) T) -
        (V.l : C) * PowerSeries.coeff V.l (subst (fun q : Fin 1 × Fin dd => γ0 q.2) T) := by
    linear_combination k3
  rw [efin, e13]
  exact mm_add (mm_sub hA3 hA1) (mm_sub hA4 hA2)

end Formalism.L2.FormalSeriesBounds
