import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaWeightedNorm
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CfwMOfExtraBounds
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BasePsiLeviLowerBound

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
open GlobalTheory.FrameThetaCompare (transfer curv_lin diagForm chart_smooth smooth_of_chart mem_SS_iff lower_iff
  upper_iff bdd_of_upper curvDe_eq_omRh curvDe_nonneg card_pos)

namespace GlobalTheory.ThetaRecordCompare

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem isInv_iff (X : Data E r) (u : Frame X.Ψ r → ℝ) : IsInv X u ↔ IsInvFn X u :=
  GlobalTheory.FrameThetaCompare.isInv_iff X u

theorem levi_eq (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : levi X x0 u z ξ = leviM X u x0 z ξ := rfl

theorem levi_rh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    levi X x0 (rh X) z ξ = leviRh X x0 z ξ := rfl

theorem levi_phK (X : Data E r) (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) : levi X x0 (phK X) z ξ = leviDens X x0 z ξ := by
  have hev : (fun w => ((phK X (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((Real.log (densF X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [IW.log_densF_eq X x0 hw]
    simp only [phK, IW.Lm, Finset.mul_sum]
  unfold levi leviDens
  rw [leviV_congr hev]

theorem cuspDecay_iff (X : Data E r) (ps : Frame X.Ψ r → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    CuspDecay X ps a ↔ cfwM X ps a := by
  rw [← GlobalTheory.FlatCompare.extraBounds_iff X ps ha]
  exact exists_congr fun _ => and_comm

theorem isExtra_iff (X : Data E r) (ps : Frame X.Ψ r → ℝ) {a : ℝ} (ha : 0 < a) :
    IsExtra X ps a ↔ IsInvFn X ps ∧
      (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}) ∧
      cfwM X ps a := by
  constructor
  · rintro ⟨-, h1, h2, -, h3⟩
    exact ⟨(isInv_iff X ps).1 h1, fun x0 _ => chart_smooth X h2 x0, (cuspDecay_iff X ps ha.le).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨ha.le, (isInv_iff X ps).2 h1, smooth_of_chart X ((isInv_iff X ps).2 h1).1 h2, ?_,
      (cuspDecay_iff X ps ha.le).2 h3⟩
    obtain ⟨B, hB⟩ := GlobalTheory.FlatCompare.bdd_add_log X h3 ha 0
    exact ⟨B, fun x hx => by simpa using hB x hx⟩

theorem pos_iff (X : Data E r) (la : Wt X.Ψ r) :
    (EverywhereNe X fun Lv => 0 < Lv (phla X la)) ↔
      ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
        0 < leviM X (phla X la) x0 z ξ := by
  constructor
  · intro h x0 _ z hz ξ hξ
    obtain ⟨x1, D, ho, hD, h1, -, -⟩ := transfer X x0 z hz
    exact (h x1 ho 0 (IW.zero_mem_OmF X x1 ho) _
      fun k => hξ (hD (k.trans (map_zero D).symm))).trans_eq (h1 la ξ).symm
  · exact fun h x0 ho z hz ξ hξ => h x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ

theorem pos_sub_iff (X : Data E r) (L de : Wt X.Ψ r) :
    (EverywhereNe X fun Lv => 1 / 2 * Lv (phla X de) < Lv (phla X L)) ↔
      EverywhereNe X fun Lv => 0 < Lv (phla X (2 • L - de)) := by
  refine forall₂_congr fun x0 _ => forall₂_congr fun z hz => forall₂_congr fun ξ _ => ?_
  have h := curv_lin X hz 2 (-1) L de ξ
  have e : (2 : ℤ) • L + (-1 : ℤ) • de = 2 • L - de := by module
  rw [e] at h
  change levi X x0 (phla X (2 • L - de)) z ξ =
    _ * levi X x0 (phla X L) z ξ + _ * levi X x0 (phla X de) z ξ at h
  beta_reduce
  rw [h]
  push_cast
  constructor <;> intro h <;> linarith

theorem lower_levi_iff (X : Data E r) (de : Wt X.Ψ r) (k : ℝ) {ps : Frame X.Ψ r → ℝ} (h1 : IsInv X ps)
    (h2 : ContDiffOn ℝ ∞ ps X.dom) :
    (Everywhere X fun Lv => -(k * Lv (phla X de)) ≤ Lv ps) ↔
      ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
        -(k * leviM X (phla X de) x0 z ξ) ≤ leviM X ps x0 z ξ := by
  constructor
  · intro h x0 _ z hz ξ
    obtain ⟨x1, D, ho, -, k1, -, k2⟩ := transfer X x0 z hz
    have a := h x1 ho 0 (IW.zero_mem_OmF X x1 ho) (D ξ)
    have b : leviM X (phla X de) x0 z ξ = levi X x1 (phla X de) 0 (D ξ) := k1 de ξ
    have c : leviM X ps x0 z ξ = levi X x1 ps 0 (D ξ) := k2 ps h1.1 h2 ξ
    rw [b, c]
    exact a
  · exact fun h x0 ho z hz ξ => h x0 (IW.orth_mem_dom X x0 ho) z hz ξ

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma twoDelta_sub_eq_two_mul_blockWt_sub {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {de : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X de) (τ : X.Ψ) (a b : Fin r) :
    ((de τ a : ℤ) : ℝ) - ((de τ b : ℤ) : ℝ) =
      2 * (((_root_.GlobalTheory.CurvMargin.blockWt X τ a : ℤ) : ℝ) -
        ((_root_.GlobalTheory.CurvMargin.blockWt X τ b : ℤ) : ℝ)) := by
  have key : de τ a - de τ b =
      2 * (_root_.GlobalTheory.CurvMargin.blockWt X τ a - _root_.GlobalTheory.CurvMargin.blockWt X τ b) := by
    by_cases ha : (a : ℕ) < X.p0 <;> by_cases hb : (b : ℕ) < X.p0
    · have := (h τ a b).1 (iff_of_true ha hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ a b).2 ha (not_lt.1 hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ b a).2 hb (not_lt.1 ha)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ a b).1 (iff_of_false ha hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
  exact_mod_cast key

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.ThetaRecordCompare.levi_twoDelta {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {de : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X de) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) {z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)} (hz : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0)
    (ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.levi X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X de) z ξ = 2 * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviRh X x0 z ξ := by
  rw [_root_.GlobalTheory.CurvMargin.leviRh_eq X x0 ho hz ξ]
  obtain ⟨x1, D, -, -, -, hdiag, -⟩ := _root_.GlobalTheory.FrameThetaCompare.transfer X x0 z hz
  change _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 de z ξ =
    2 * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 (_root_.GlobalTheory.CurvMargin.blockWt X) z ξ
  rw [hdiag, hdiag]
  unfold _root_.GlobalTheory.FrameThetaCompare.diagForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [twoDelta_sub_eq_two_mul_blockWt_sub h]
  ring

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThetaRecordCompare.leviRh_nonneg (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) {z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)}
    (hz : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0) (ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviRh X x0 z ξ := by
  have h0 := _root_.GlobalTheory.FrameThetaCompare.curvDe_nonneg X (x0 := x0) hz ξ
  rw [_root_.GlobalTheory.FrameThetaCompare.curvDe_eq_omRh X ho hz ξ] at h0
  exact h0

theorem orth_x0F (X : Data E r) : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2

theorem levi_single (X : Data E r) (τ : X.Ψ) {i j : Fin r} (h : i < j) :
    ∃ ξ : Fin (nd X) → ℂ, ξ ≠ 0 ∧ ∀ la : Wt X.Ψ r, leviM X (phla X la) (x0F X) 0 ξ =
      sgn X.p0 j * sgn X.p0 i * ((la τ i : ℝ) - la τ j) := by
  classical
  let e0 : Ent X := ⟨τ, ⟨(j, i), h⟩⟩
  obtain ⟨ξ, a, b⟩ : ∃ ξ : Fin (nd X) → ℂ, ξ (Fintype.equivFin (Ent X) e0) = 1 ∧
      ∀ e, e ≠ e0 → ξ (Fintype.equivFin (Ent X) e) = 0 :=
    ⟨fun k : Fin (Fintype.card (Ent X)) => if k = Fintype.equivFin (Ent X) e0 then 1 else 0, if_pos rfl,
      fun e he => if_neg ((Fintype.equivFin (Ent X)).injective.ne he)⟩
  refine ⟨ξ, fun k => ?_, fun la => ?_⟩
  · rw [k] at a
    exact zero_ne_one a
  have h1 : leviM X (phla X la) (x0F X) 0 ξ = diagForm X la ξ :=
    GlobalTheory.LeviZero.levi_phla_zero r X la _ (orth_x0F X) _
  rw [h1, diagForm, Finset.sum_eq_single e0]
  · rw [a]; simp [e0]
  · intro e _ he
    rw [b e he]
    simp
  · simp

theorem levi_gap (X : Data E r) (τ : X.Ψ) {i j : Fin r} (h : (j : ℕ) = i + 1) (h' : (j : ℕ) ≠ X.p0) :
    ∃ ξ : Fin (nd X) → ℂ, ξ ≠ 0 ∧ ∀ la : Wt X.Ψ r, leviM X (phla X la) (x0F X) 0 ξ =
      ((la τ i - la τ j : ℤ) : ℝ) := by
  obtain ⟨ξ, h0, k⟩ := levi_single X τ (show i < j by rw [Fin.lt_def]; omega)
  refine ⟨ξ, h0, fun la => ?_⟩
  rw [k]
  unfold sgn
  split_ifs <;> first | omega | (push_cast; ring)

theorem levi_pair (X : Data E r) (h0 : 0 < X.p0) (hr : X.p0 < r) (τ : X.Ψ) {i j : Fin r}
    (h : (i : ℕ) = 0) (h' : (j : ℕ) = r - 1) :
    ∃ ξ : Fin (nd X) → ℂ, ξ ≠ 0 ∧ ∀ la : Wt X.Ψ r, leviM X (phla X la) (x0F X) 0 ξ =
      ((la τ j - la τ i : ℤ) : ℝ) := by
  obtain ⟨ξ, h0, k⟩ := levi_single X τ (show i < j by rw [Fin.lt_def]; omega)
  refine ⟨ξ, h0, fun la => ?_⟩
  rw [k]
  unfold sgn
  split_ifs <;> first | omega | (push_cast; ring)

theorem one_le_of_pos {n : ℤ} (h : (0 : ℝ) < n) : (1 : ℝ) ≤ n := by
  have : 0 < n := by exact_mod_cast h
  exact_mod_cast this

theorem gaps_of_pos {X : Data E r} {la : Wt X.Ψ r} (h : EverywhereNe X fun Lv => 0 < Lv (phla X la)) :
    GapsGe X la 1 ∧ (0 < X.p0 → X.p0 < r → PairingGe X la 1) := by
  have hz := IW.zero_mem_OmF X _ (orth_x0F X)
  refine ⟨fun τ i j a b => ?_, fun h0 hr τ i j a b => ?_⟩
  · obtain ⟨ξ, h0, k⟩ := levi_gap X τ a b
    exact one_le_of_pos ((h _ (orth_x0F X) 0 hz ξ h0).trans_eq (k la))
  · obtain ⟨ξ, h0, k⟩ := levi_pair X h0 hr τ a b
    exact one_le_of_pos ((h _ (orth_x0F X) 0 hz ξ h0).trans_eq (k la))

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThetaRecordCompare.gapsGe_mono {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {g g' : ℝ}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la g) (hg : g' ≤ g) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la g' :=
  fun τ i j hij hne => hg.trans (h τ i j hij hne)

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.ThetaRecordCompare.cusp_of_gaps {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} (hn : 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)
    (h0 : 0 < X.p0) (hr : X.p0 < r) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (hg : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la 0) (hp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la 1) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) :
    P ∈ X.SS la := by
  obtain ⟨τ0, hτ0⟩ := Finset.card_pos.1 (_root_.GlobalTheory.FrameThetaCompare.card_pos hn)
  have key := @_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.cuspStatement_holds E _ _ _
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.CuspStatement at key
  refine key r X la ⟨τ0, hτ0⟩ h0 hr (fun i j hij hne => ?_) (fun i0 i1 hi0 hi1 => ?_) P hP
  · have h1 : (0 : ℤ) ≤ la ⟨τ0, hτ0⟩ i - la ⟨τ0, hτ0⟩ j := by exact_mod_cast hg _ i j hij hne
    omega
  · have h1 : (1 : ℤ) ≤ la ⟨τ0, hτ0⟩ i1 - la ⟨τ0, hτ0⟩ i0 := by
      exact_mod_cast hp _ i0 i1 hi0 hi1
    omega

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThetaRecordCompare.two_le_r {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} (hn : 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) : 2 ≤ r := by
  by_contra hlt
  push_neg at hlt
  have hempty : IsEmpty (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent
    refine ⟨fun ⟨_, ⟨p, hp⟩⟩ => ?_⟩
    have h1 := p.1.isLt
    have h2 : (p.2 : ℕ) < p.1 := hp
    omega
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd at hn
  rw [Fintype.card_eq_zero_iff.2 hempty] at hn
  omega

theorem indefinite {X : Data E r} (hn : 2 ≤ nd X) {la : Wt X.Ψ r}
    (h : EverywhereNe X fun Lv => 0 < Lv (phla X la)) (hp : PairingGe X la 1) :
    0 < X.p0 ∧ X.p0 < r := by
  have h2 := two_le_r hn
  obtain ⟨τ, hτ⟩ := Finset.card_pos.1 (card_pos hn)
  by_contra hc
  have hle := X.p0_le
  obtain ⟨ξ, h0, k⟩ := levi_single X ⟨τ, hτ⟩
    (show (⟨0, by omega⟩ : Fin r) < ⟨r - 1, by omega⟩ by rw [Fin.lt_def]; simp only; omega)
  have a := (h _ (orth_x0F X) 0 (IW.zero_mem_OmF X _ (orth_x0F X)) ξ h0).trans_eq (k la)
  have b := hp ⟨τ, hτ⟩ ⟨0, by omega⟩ ⟨r - 1, by omega⟩ rfl rfl
  push_cast at b
  unfold sgn at a
  simp only at a
  split_ifs at a <;> first | omega | linarith

section Records

variable {X : Data E r}

theorem T_pos {T : ℕ} (hn : 2 ≤ nd X) (hT : 11 * nd X ^ 2 ≤ T) : (0 : ℝ) < T := by
  have : 0 < T := lt_of_lt_of_le (by positivity) hT
  exact_mod_cast this

theorem half (k : ℕ) : 2 * k / 2 = k := by omega

theorem indef (I : ThetaIn X) : 0 < X.p0 ∧ X.p0 < r := indefinite I.two_le_D I.L_curv I.L_pair

theorem w_cusp (I : ThetaIn X) (j : Fin I.N) : I.w j ∈ X.SS I.L :=
  cusp_of_gaps I.two_le_D (indef I).1 (indef I).2 I.L_gaps I.L_pair (I.w_bdd j)

theorem th1_mem_SS (I : ThetaIn X) : I.th1 ∈ X.SS (2 • I.L - I.de2) :=
  have h := gaps_of_pos ((pos_sub_iff X _ _).1 I.Lde_curv)
  cusp_of_gaps I.two_le_D (indef I).1 (indef I).2 (gapsGe_mono h.1 zero_le_one)
    (h.2 (indef I).1 (indef I).2) I.firstTheta_bounded

theorem thp_cusp (I : ThetaIn X) : I.thp ∈ X.SS I.Fp :=
  cusp_of_gaps I.two_le_D (indef I).1 (indef I).2 I.Fp_gaps I.Fp_pair I.thp_bdd

def CuspTwo (I : ThetaIn X) : Prop := I.th2 ∈ X.SS ((nd X + 4) • I.L - I.Fp)

theorem cuspTwo_of_gaps (I : ThetaIn X) (hg : GapsGe X ((nd X + 4) • I.L - I.Fp) 0)
    (hp : PairingGe X ((nd X + 4) • I.L - I.Fp) 1) : CuspTwo I :=
  cusp_of_gaps I.two_le_D (indef I).1 (indef I).2 hg hp I.secondTheta_bounded

theorem w_nz (I : ThetaIn X) (x : Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ k, I.w k x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := I.w_lower
  have := (Real.exp_pos _).trans_le (hC x hx)
  simp [wnorm, Data.pnorm, h] at this

theorem frame_theta_const_pos (I : ThetaIn X) : 0 < I.c1 := by
  have h1 := T_pos I.two_le_D I.T_ge
  have h2 := I.c_pos
  have h3 : 0 < I.RR := one_pos.trans_le I.one_le_RR
  have h4 := I.dp_pos
  have h5 := I.qp_pos
  unfold ThetaIn.c1
  positivity

theorem mul_ph_le (I : ThetaIn X) (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    (I.T : ℝ) * I.c * I.ph x ≤ I.c1 / X.la1 x ^ 2 := by
  have h2 := I.c_pos
  have h5 := I.qp_pos
  have hb : 0 ≤ (I.T : ℝ) * I.c * (I.qp * I.dp ^ 2 / (2 * X.la1 x ^ 2)) := by positivity
  calc (I.T : ℝ) * I.c * I.ph x
      ≤ (I.T : ℝ) * I.c * (I.qp * I.dp ^ 2 / (2 * X.la1 x ^ 2)) :=
        mul_le_mul_of_nonneg_left (I.ph_upper x hx) (by positivity)
    _ ≤ I.RR * ((I.T : ℝ) * I.c * (I.qp * I.dp ^ 2 / (2 * X.la1 x ^ 2))) :=
        le_mul_of_one_le_left hb I.one_le_RR
    _ = I.c1 / X.la1 x ^ 2 := by
        unfold ThetaIn.c1
        ring

def MarginCut (X : Data E r) (L Fp : Wt X.Ψ r) (η m : ℝ) : Prop :=
  ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    2 * η * leviO X x0 (phla X L) z ξ + m * leviRh X x0 z ξ ≤
      leviO X x0 (phla X Fp) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X L) z ξ

def MarginOnto (X : Data E r) (Fp : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Fp) z ξ - leviDens X x0 z ξ

theorem everywhere_iff_marginCut (X : Data E r) (L Fp : Wt X.Ψ r) (η m : ℝ) :
    (Everywhere X fun Lv => 2 * η * Lv (phla X L) + m * Lv (rh X) ≤
      Lv (phla X Fp) - Lv (phK X) - (nd X : ℝ) * Lv (phla X L)) ↔ MarginCut X L Fp η m := by
  refine forall₂_congr fun x0 _ => forall₂_congr fun z hz => forall_congr' fun ξ => ?_
  beta_reduce
  rw [levi_phK X x0 hz]
  rfl

theorem marginOnto_iff (X : Data E r) (Fp : Wt X.Ψ r) (m : ℝ) :
    (Everywhere X fun Lv => m * Lv (rh X) ≤ Lv (phla X Fp) - Lv (phK X)) ↔ MarginOnto X Fp m := by
  refine forall₂_congr fun x0 _ => forall₂_congr fun z hz => forall_congr' fun ξ => ?_
  beta_reduce
  rw [levi_phK X x0 hz]
  rfl

theorem range_of_marginCut {L Fp de : Wt X.Ψ r} {η m u : ℝ} (hde : IsTwoDelta X de)
    (h : MarginCut X L Fp η m) (hu : u ≤ m) (x0 : Frame X.Ψ r) (z : V (nd X))
    (hz : cpt X x0 z ∈ X.dom) (ξ : Fin (nd X) → ℂ) :
    2 * η * leviM X (phla X L) x0 z ξ ≤
      leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - u / 2 * leviM X (phla X de) x0 z ξ := by
  obtain ⟨x1, D, ho, -, k, -, -⟩ := transfer X x0 z hz
  have h0 := IW.zero_mem_OmF X x1 ho
  have k' : ∀ la, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ) := fun la => k la ξ
  have a : leviM X (phla X de) x1 0 (D ξ) = 2 * leviRh X x1 0 (D ξ) := levi_twoDelta hde ho h0 _
  have b := h x1 ho 0 h0 (D ξ)
  have c := mul_le_mul_of_nonneg_right hu (leviRh_nonneg X ho h0 (D ξ))
  rw [k', k', k', IW.leviM_comb X x1 ho h0, a]
  unfold leviO at *
  linarith

def toArch (I : ThetaIn X) (h : CuspTwo I) : ArchInM X where
  L := I.L
  de := I.de2
  Fp := I.Fp
  T := I.T
  i := I.i
  g0 := I.g0
  N := I.N
  c := I.c
  c1 := I.c1
  a1 := I.a1
  rr := r
  n_ge := I.two_le_D
  T_ge := I.T_ge
  i_pos := I.i_pos
  genus_pos := by have := I.genusHeight_pos; unfold ThetaIn.g0; omega
  c_pos := I.c_pos
  frame_theta_const_pos := frame_theta_const_pos I
  frame_theta_weight_pos := I.frame_theta_weight_pos
  rr_nonneg := Nat.cast_nonneg _
  Tcg0 := by have := I.Tcg; unfold ThetaIn.g0; push_cast; exact this
  rr_le := by rw [mul_comm]; exact I.tr_le
  w := I.w
  w_van := fun k => (mem_SS_iff X _ _).1 (w_cusp I k)
  w_nz := w_nz I
  ph := I.ph
  ph_inv := (isInv_iff X _).1 I.ph_inv
  ph_nonneg := I.ph_nonneg
  p1 := by
    obtain ⟨ε, hε, k⟩ := I.ph_lower
    have h3 : 0 < I.RR := one_pos.trans_le I.one_le_RR
    have h4 := I.dp_pos
    exact ⟨1 / (4 * I.RR * I.dp ^ 2), ε, by positivity, hε, fun x hx hl => by
      rw [div_div]; exact k x hx hl⟩
  p2 := mul_ph_le I
  p3 := (lower_iff X _ _ _ _).1 I.w_lower
  et := I.et
  genus_even := even_two_mul _
  et_sec := by rw [ThetaIn.g0, half]; exact I.et_bdd.1
  et_ne := I.et_ne
  p4 := by rw [ThetaIn.g0, half]; exact (upper_iff X _ _ I.i_pos _).1 I.et_upper
  th1 := I.th1
  firstTheta_vanishes := (mem_SS_iff X _ _).1 (th1_mem_SS I)
  firstTheta_ne_zero := I.firstTheta_ne_zero
  th2 := I.th2
  secondTheta_vanishes := (mem_SS_iff X _ _).1 h
  secondTheta_ne_zero := I.secondTheta_ne_zero
  thp := I.thp
  thp_van := (mem_SS_iff X _ _).1 (thp_cusp I)
  thp_ne := I.thp_ne
  ps0 := I.ps0
  potential_invariant := ((isExtra_iff X _ I.frame_theta_weight_pos).1 I.extraDivisor_isExtra).1
  potential_smooth := ((isExtra_iff X _ I.frame_theta_weight_pos).1 I.extraDivisor_isExtra).2.1
  base_psi_levi_lower_bound := (lower_levi_iff X _ _ I.extraDivisor_isExtra.2.1 I.extraDivisor_isExtra.2.2.1).1 I.curvature_lower_bound
  base_psi_weighted_cf := ((isExtra_iff X _ I.frame_theta_weight_pos).1 I.extraDivisor_isExtra).2.2
  posL := (pos_iff X _).1 I.L_curv
  posLde := (pos_iff X _).1 ((pos_sub_iff X _ _).1 I.Lde_curv)
  posF := ⟨I.η, I.η_pos, fun t _ ht x0 _ z hz ξ => by
    have hT := T_pos I.two_le_D I.T_ge
    rw [← mul_div_assoc]
    exact range_of_marginCut I.twoDelta_spec ((everywhere_iff_marginCut X _ _ _ _).1 I.curvA) (by linarith) x0 z hz ξ⟩

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma cpt_zero_jet_harmonics (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 = x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.mat]
  funext τ a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp only [Matrix.of_apply]
    split_ifs <;> first | exact mul_zero _ | simp_all
  · simp

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma exists_surjective_diagForm_leviM (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) :
    ∃ x0 ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 ∈ X.dom ∧
      ∃ D : (Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) →ₗ[ℂ] Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ, Function.Surjective D ∧
        ∀ la ξ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviM X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la) x0 0 ξ = _root_.GlobalTheory.FrameThetaCompare.diagForm X la (D ξ) := by
  obtain ⟨x0, hx0, -⟩ := A.et_ne
  have hd : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 ∈ X.dom := by rw [cpt_zero_jet_harmonics]; exact hx0
  obtain ⟨x1, D, -, hD, -, hdiag, -⟩ := _root_.GlobalTheory.FrameThetaCompare.transfer X x0 0 hd
  exact ⟨x0, hx0, hd, D, LinearMap.injective_iff_surjective.1 hD, fun la ξ => hdiag la ξ⟩

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma diagForm_L_pos (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) {η : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ} (hη : η ≠ 0) :
    0 < _root_.GlobalTheory.FrameThetaCompare.diagForm X A.L η := by
  obtain ⟨x0, hx0, hd, D, hD, hdiag⟩ := exists_surjective_diagForm_leviM A
  obtain ⟨ξ, rfl⟩ := hD η
  have hξ : ξ ≠ 0 := by rintro rfl; exact hη (map_zero D)
  rw [← hdiag]
  exact A.posL x0 hx0 0 hd ξ hξ

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma single_ne_zero_jet_harmonics (τ : X.Ψ) (i j : Fin r) (h : i < j) :
    (fun k : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) =>
      if (k : ℕ) = (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) then (1 : ℂ) else 0 :
      Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) ≠ 0 := fun hz => by
  have := congrFun hz (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩))
  simp only [if_pos rfl] at this
  exact one_ne_zero this

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma diagForm_single' (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (τ : X.Ψ) (i j : Fin r) (h : i < j) :
    _root_.GlobalTheory.FrameThetaCompare.diagForm X la
        (fun k : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) =>
          if (k : ℕ) = (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) then 1 else 0) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i * (((la τ i : ℤ) : ℝ) - ((la τ j : ℤ) : ℝ)) := by
  unfold _root_.GlobalTheory.FrameThetaCompare.diagForm
  rw [Finset.sum_eq_single (τ, ⟨(j, i), h⟩)]
  · simp
  · intro e _ he
    have hne : ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) e : Fin _) : ℕ) ≠
        (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) := fun h' =>
      he ((Fintype.equivFin _).injective (Fin.ext h'))
    simp only [hne, if_false]
    simp
  · simp

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
private lemma diagForm_Fp_sub_pos (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) {η : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ} (hη : η ≠ 0) :
    0 < _root_.GlobalTheory.FrameThetaCompare.diagForm X (A.Fp - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X • A.L) η := by
  obtain ⟨x0, hx0, hd, D, hD, hdiag⟩ := exists_surjective_diagForm_leviM A
  obtain ⟨ξ, rfl⟩ := hD η
  have hξ : ξ ≠ 0 := by rintro rfl; exact hη (map_zero D)
  obtain ⟨c, hc, hF⟩ := A.posF
  have h1 := A.posL x0 hx0 0 hd ξ hξ
  have h2 := hF 0 le_rfl (by rw [zero_mul]; positivity) x0 hx0 0 hd ξ
  rw [← hdiag]
  have h3 := mul_pos (mul_pos two_pos hc) h1
  linarith

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in

theorem _root_.GlobalTheory.ThetaRecordCompare.arch_gaps (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) (h0 : 0 < X.p0)
    (hr : X.p0 < r) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X A.L 1 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X A.L 1 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X A.Fp 0 ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X A.Fp 1 := by
  have hn : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) := by exact_mod_cast A.n_ge
  have gL : ∀ (τ : X.Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 →
      1 ≤ A.L τ i - A.L τ j := by
    intro τ i j hij hne
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i = 1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      by_cases hj : (j : ℕ) < X.p0
      · rw [if_pos hj, if_pos (by omega)]; norm_num
      · rw [if_neg hj, if_neg (by omega)]; norm_num
    have h1 := diagForm_L_pos A (single_ne_zero_jet_harmonics τ i j hlt)
    rw [diagForm_single' A.L τ i j hlt, hs, one_mul] at h1
    have h2 : (0 : ℤ) < A.L τ i - A.L τ j := by
      exact_mod_cast (by linarith : (0 : ℝ) < ((A.L τ i : ℤ) : ℝ) - ((A.L τ j : ℤ) : ℝ))
    omega
  have pL : ∀ (τ : X.Ψ) (i0 i1 : Fin r), (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 →
      1 ≤ A.L τ i1 - A.L τ i0 := by
    intro τ i0 i1 hi0 hi1
    have hlt : i0 < i1 := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i0 = -1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      rw [if_neg (by omega), if_pos (by omega)]; norm_num
    have h1 := diagForm_L_pos A (single_ne_zero_jet_harmonics τ i0 i1 hlt)
    rw [diagForm_single' A.L τ i0 i1 hlt, hs] at h1
    have h2 : (0 : ℤ) < A.L τ i1 - A.L τ i0 := by
      exact_mod_cast (by linarith : (0 : ℝ) < ((A.L τ i1 : ℤ) : ℝ) - ((A.L τ i0 : ℤ) : ℝ))
    omega
  refine ⟨fun τ i j hij hne => by exact_mod_cast gL τ i j hij hne,
    fun τ i0 i1 hi0 hi1 => by exact_mod_cast pL τ i0 i1 hi0 hi1, ?_, ?_⟩
  · intro τ i j hij hne
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i = 1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      by_cases hj : (j : ℕ) < X.p0
      · rw [if_pos hj, if_pos (by omega)]; norm_num
      · rw [if_neg hj, if_neg (by omega)]; norm_num
    have h1 := diagForm_Fp_sub_pos A (single_ne_zero_jet_harmonics τ i j hlt)
    rw [diagForm_single' _ τ i j hlt, hs, one_mul] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW] at h1
    push_cast at h1
    have hR : (0 : ℝ) < ((A.Fp τ i - A.Fp τ j + 2 * ((j : ℤ) - i) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) : ℤ) : ℝ) := by
      push_cast; linarith
    have hZ : (0 : ℤ) < A.Fp τ i - A.Fp τ j + 2 * ((j : ℤ) - i) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) := by exact_mod_cast hR
    have hg := gL τ i j hij hne
    have hji : (j : ℤ) - i = 1 := by omega
    have hm : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) := by nlinarith
    have : (0 : ℤ) ≤ A.Fp τ i - A.Fp τ j := by linarith
    exact_mod_cast this
  · intro τ i0 i1 hi0 hi1
    have hlt : i0 < i1 := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i0 = -1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      rw [if_neg (by omega), if_pos (by omega)]; norm_num
    have h1 := diagForm_Fp_sub_pos A (single_ne_zero_jet_harmonics τ i0 i1 hlt)
    rw [diagForm_single' _ τ i0 i1 hlt, hs] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW] at h1
    push_cast at h1
    have hR : (0 : ℝ) < ((A.Fp τ i1 - A.Fp τ i0 - 2 * ((i1 : ℤ) - i0) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) : ℤ) : ℝ) := by
      push_cast; linarith
    have hZ : (0 : ℤ) < A.Fp τ i1 - A.Fp τ i0 - 2 * ((i1 : ℤ) - i0) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) := by exact_mod_cast hR
    have hg := pL τ i0 i1 hi0 hi1
    have hji : (0 : ℤ) ≤ (i1 : ℤ) - i0 := by omega
    have hm : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) := by nlinarith
    have : (1 : ℤ) ≤ A.Fp τ i1 - A.Fp τ i0 := by linarith
    exact_mod_cast this

structure Explicit (A : ArchInM X) (RR dp qp η : ℝ) : Prop where
  p0_pos : 0 < X.p0
  p0_lt : X.p0 < r
  de : IsTwoDelta X A.de
  rr : A.rr = r
  marginA : bb X < 19 / 5 * (A.T : ℝ) - 2 * A.T
  marginB : bb X ^ 2 * Crh X + bb X < 19 / 10 * ((nd X : ℝ) + 2) * A.T
  η_pos : 0 < η
  cut : MarginCut X A.L A.Fp η (19 / 5 * (A.T : ℝ))
  onto : MarginOnto X A.Fp (19 / 10 * ((nd X : ℝ) + 2) * A.T)
  one_le_RR : 1 ≤ RR
  dp_pos : 0 < dp
  qp_pos : 0 < qp
  c1 : A.c1 = RR * A.T * A.c * dp ^ 2 * qp / 2
  lower : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, X.la1 x < ε → 1 / (4 * RR * dp ^ 2 * X.la1 x ^ 2) ≤ A.ph x
  upper : ∀ x ∈ X.dom, A.ph x ≤ qp * dp ^ 2 / (2 * X.la1 x ^ 2)

theorem two_mul_half (A : ArchInM X) : 2 * (A.g0 / 2) = A.g0 := Nat.two_mul_div_two_of_even A.genus_even

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.ThetaRecordCompare.arch_extra (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsExtra X A.ps0 A.a1 := by
  have hinv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsInv X A.ps0 :=
    (_root_.GlobalTheory.FrameThetaCompare.isInv_iff X _).2 A.potential_invariant
  refine ⟨A.frame_theta_weight_pos.le, hinv, ?_, ?_, ?_⟩
  · exact _root_.GlobalTheory.FrameThetaCompare.smooth_of_chart X hinv.1 A.potential_smooth
  · obtain ⟨B, hB⟩ := _root_.GlobalTheory.FlatCompare.bdd_add_log X A.base_psi_weighted_cf A.frame_theta_weight_pos 0
    exact ⟨B, fun x hx => by simpa using hB x hx⟩
  · obtain ⟨A', hdec, C, hC⟩ := (_root_.GlobalTheory.FlatCompare.extraBounds_iff X A.ps0 A.frame_theta_weight_pos.le).2 A.base_psi_weighted_cf
    exact ⟨A', ⟨C, hC⟩, fun η hη => hdec η hη⟩

def ofArch (A : ArchInM X) (RR dp qp η : ℝ) (h : Explicit A RR dp qp η) : ThetaIn X where
  L := A.L
  Fp := A.Fp
  de2 := A.de
  twoDelta_spec := h.de
  L_gaps := gapsGe_mono (arch_gaps A h.p0_pos h.p0_lt).1 zero_le_one
  L_pair := (arch_gaps A h.p0_pos h.p0_lt).2.1
  Fp_gaps := (arch_gaps A h.p0_pos h.p0_lt).2.2.1
  Fp_pair := (arch_gaps A h.p0_pos h.p0_lt).2.2.2
  T := A.T
  i := A.i
  g0h := A.g0 / 2
  c := A.c
  RR := RR
  dp := dp
  qp := qp
  a1 := A.a1
  η := η
  two_le_D := A.n_ge
  T_ge := A.T_ge
  i_pos := A.i_pos
  genusHeight_pos := by have := two_mul_half A; have := A.genus_pos; omega
  c_pos := A.c_pos
  one_le_RR := h.one_le_RR
  dp_pos := h.dp_pos
  qp_pos := h.qp_pos
  frame_theta_weight_pos := A.frame_theta_weight_pos
  η_pos := h.η_pos
  Tcg := by
    have e : (2 : ℝ) * ((A.g0 / 2 : ℕ) : ℝ) = A.g0 := by exact_mod_cast two_mul_half A
    rw [e]; exact A.Tcg0
  tr_le := by rw [← h.c1, ← h.rr, mul_comm]; exact A.rr_le
  marginA := h.marginA
  marginB := h.marginB
  N := A.N
  w := A.w
  et := A.et
  th1 := A.th1
  th2 := A.th2
  thp := A.thp
  w_bdd := fun j => (A.w_van j).1.1
  et_bdd := ⟨A.et_sec, bdd_of_upper X _ _ _ A.ph_nonneg ((upper_iff X _ _ A.i_pos _).2 A.p4)⟩
  firstTheta_bounded := A.firstTheta_vanishes.1.1
  secondTheta_bounded := A.secondTheta_vanishes.1.1
  thp_bdd := A.thp_van.1.1
  et_ne := A.et_ne
  firstTheta_ne_zero := A.firstTheta_ne_zero
  secondTheta_ne_zero := A.secondTheta_ne_zero
  thp_ne := A.thp_ne
  ph := A.ph
  ph_inv := (isInv_iff X _).2 A.ph_inv
  ph_nonneg := A.ph_nonneg
  w_lower := (lower_iff X _ _ _ _).2 A.p3
  et_upper := (upper_iff X _ _ A.i_pos _).2 A.p4
  ph_lower := h.lower
  ph_upper := h.upper
  ps0 := A.ps0
  extraDivisor_isExtra := arch_extra A
  curvature_lower_bound := (lower_levi_iff X _ _ (arch_extra A).2.1 (arch_extra A).2.2.1).2
    (by rw [← h.rr]; exact A.base_psi_levi_lower_bound)
  L_curv := (pos_iff X _).2 A.posL
  Lde_curv := (pos_sub_iff X _ _).2 ((pos_iff X _).2 A.posLde)
  curvA := (everywhere_iff_marginCut X _ _ _ _).2 h.cut
  curvB := (marginOnto_iff X _ _).2 h.onto

def Agree (I : ThetaIn X) (A : ArchInM X) : Prop :=
  A.L = I.L ∧ A.de = I.de2 ∧ A.Fp = I.Fp ∧ A.T = I.T ∧ A.i = I.i ∧
    A.g0 = I.g0 ∧ A.c = I.c ∧ A.c1 = I.c1 ∧ A.a1 = I.a1 ∧ A.rr = r ∧
    (⟨A.N, A.w⟩ : Σ N : ℕ, Fin N → Frame X.Ψ r → ℂ) = ⟨I.N, I.w⟩ ∧
    A.ph = I.ph ∧ A.et = I.et ∧ A.th1 = I.th1 ∧ A.th2 = I.th2 ∧ A.thp = I.thp ∧ A.ps0 = I.ps0

theorem agree_toArch (I : ThetaIn X) (h : CuspTwo I) : Agree I (toArch I h) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem explicit_toArch (I : ThetaIn X) (h : CuspTwo I) : Explicit (toArch I h) I.RR I.dp I.qp I.η :=
  ⟨(indef I).1, (indef I).2, I.twoDelta_spec, rfl, I.marginA, I.marginB, I.η_pos,
    (everywhere_iff_marginCut X _ _ _ _).1 I.curvA, (marginOnto_iff X _ _).1 I.curvB, I.one_le_RR, I.dp_pos,
    I.qp_pos, rfl, I.ph_lower, I.ph_upper⟩

theorem agree_ofArch (A : ArchInM X) (RR dp qp η : ℝ) (h : Explicit A RR dp qp η) :
    Agree (ofArch A RR dp qp η h) A :=
  ⟨rfl, rfl, rfl, rfl, rfl, (two_mul_half A).symm, rfl, h.c1, rfl, h.rr, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cuspTwo_ofArch (A : ArchInM X) (RR dp qp η : ℝ) (h : Explicit A RR dp qp η) :
    CuspTwo (ofArch A RR dp qp η h) := A.secondTheta_vanishes.1

theorem Agree.cuspTwo {I : ThetaIn X} {A : ArchInM X} (h : Agree I A) : CuspTwo I := by
  obtain ⟨h1, -, h3, -, -, -, -, -, -, -, -, -, -, -, h15, -, -⟩ := h
  unfold CuspTwo
  rw [← h1, ← h3, ← h15]
  exact A.secondTheta_vanishes.1

theorem Agree.unique {I : ThetaIn X} {A A' : ArchInM X} (h : Agree I A) (h' : Agree I A') :
    A = A' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17⟩ := h'
  have e11 := h11.trans k11.symm
  cases A; cases A'
  dsimp only at *
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13 h14 h15 h16 h17
  subst k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k12 k13 k14 k15 k16 k17
  cases e11
  rfl

theorem Agree.unique_left {I I' : ThetaIn X} {A : ArchInM X} (h : Agree I A) (h' : Agree I' A)
    (e1 : I.RR = I'.RR) (e2 : I.dp = I'.dp) (e3 : I.qp = I'.qp) (e4 : I.η = I'.η) : I = I' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9, -, h11, h12, h13, h14, h15, h16, h17⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, -, k9, -, k11, k12, k13, k14, k15, k16, k17⟩ := h'
  have e11 := h11.symm.trans k11
  have e6 : I.g0h = I'.g0h := by
    have := h6.symm.trans k6
    unfold ThetaIn.g0 at this
    omega
  clear h6 k6 h11 k11
  cases I; cases I'
  dsimp only at *
  subst h1 h2 h3 h4 h5 h7 h9 h12 h13 h14 h15 h16 h17
  subst k1 k2 k3 k4 k5 k7 k9 k12 k13 k14 k15 k16 k17 e1 e2 e3 e4 e6
  cases e11
  rfl

def thetaEquiv (X : Data E r) :
    {I : ThetaIn X // CuspTwo I} ≃
      {q : ArchInM X × ℝ × ℝ × ℝ × ℝ // Explicit q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2} where
  toFun I := ⟨(toArch I.1 I.2, I.1.RR, I.1.dp, I.1.qp, I.1.η), explicit_toArch I.1 I.2⟩
  invFun q := ⟨ofArch q.1.1 _ _ _ _ q.2, cuspTwo_ofArch _ _ _ _ _ q.2⟩
  left_inv I := Subtype.ext ((agree_ofArch _ _ _ _ _ (explicit_toArch I.1 I.2)).unique_left
    (agree_toArch I.1 I.2) rfl rfl rfl rfl)
  right_inv q := Subtype.ext (Prod.ext
    ((agree_toArch _ (cuspTwo_ofArch _ _ _ _ _ q.2)).unique (agree_ofArch _ _ _ _ _ q.2)) rfl)

def Side (A : ArchInM X) : Prop :=
  0 < X.p0 ∧ X.p0 < r ∧ IsTwoDelta X A.de ∧ A.rr = r ∧ bb X < 19 / 5 * (A.T : ℝ) - 2 * A.T ∧
    bb X ^ 2 * Crh X + bb X < 19 / 10 * ((nd X : ℝ) + 2) * A.T ∧
    (∃ η : ℝ, 0 < η ∧ MarginCut X A.L A.Fp η (19 / 5 * (A.T : ℝ))) ∧
    MarginOnto X A.Fp (19 / 10 * ((nd X : ℝ) + 2) * A.T)

theorem side_iff (A : ArchInM X) : Side A ↔ ∃ RR dp qp η, Explicit A RR dp qp η := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, ⟨η, h7, h8⟩, h9⟩
    obtain ⟨ca, ε, hca, hε, hl⟩ := A.p1
    have hT := T_pos A.n_ge A.T_ge
    have hc := A.c_pos
    have hc1 := A.frame_theta_const_pos
    obtain ⟨d, hd, hd2⟩ : ∃ d : ℝ, 0 < d ∧ d ^ 2 = 1 / (4 * ca) :=
      ⟨Real.sqrt (1 / (4 * ca)), by positivity, Real.sq_sqrt (by positivity)⟩
    refine ⟨1, d, 2 * A.c1 / (A.T * A.c * d ^ 2), η, h1, h2, h3, h4, h5, h6, h7, h8, h9, le_rfl, hd,
      by positivity, by field_simp, ⟨ε, hε, fun x hx hlt => (le_of_eq ?_).trans (hl x hx hlt)⟩,
      fun x hx => ?_⟩
    · rw [hd2, ← div_div]
      congr 1
      field_simp
    · have e : 2 * A.c1 / (A.T * A.c * d ^ 2) * d ^ 2 / (2 * X.la1 x ^ 2) =
          A.c1 / X.la1 x ^ 2 / (A.T * A.c) := by
        rw [← div_div, div_right_comm A.c1]
        congr 1
        field_simp
      rw [e, le_div_iff₀ (by positivity), mul_comm]
      exact A.p2 x hx
  · rintro ⟨RR, dp, qp, η, h⟩
    exact ⟨h.p0_pos, h.p0_lt, h.de, h.rr, h.marginA, h.marginB, ⟨η, h.η_pos, h.cut⟩, h.onto⟩

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.ThetaRecordCompare.gaps_add {la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la 0)
    (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la' 0) (k : ℕ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X (la + k • la') 0 := by
  intro τ i j hij hne
  have a1 : (0 : ℤ) ≤ la τ i - la τ j := by exact_mod_cast h τ i j hij hne
  have a2 : (0 : ℤ) ≤ la' τ i - la' τ j := by exact_mod_cast h' τ i j hij hne
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have : (0 : ℤ) ≤ (la + k • la') τ i - (la + k • la') τ j := by
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    nlinarith
  exact_mod_cast this

open NumberField Topology in
open scoped ContDiff in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
variable {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} in
theorem _root_.GlobalTheory.ThetaRecordCompare.pair_add {la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la 1)
    (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la' 1) (k : ℕ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X (la + k • la') 1 := by
  intro τ i0 i1 hi0 hi1
  have a1 : (1 : ℤ) ≤ la τ i1 - la τ i0 := by exact_mod_cast h τ i0 i1 hi0 hi1
  have a2 : (1 : ℤ) ≤ la' τ i1 - la' τ i0 := by exact_mod_cast h' τ i0 i1 hi0 hi1
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have : (1 : ℤ) ≤ (la + k • la') τ i1 - (la + k • la') τ i0 := by
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    nlinarith
  exact_mod_cast this

theorem premises (A : ArchInM X) (h : Side A) :
    (∃ b m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < b ∧ b < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X A.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X A.L) z ξ) ∧
    (∃ b m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < b ∧ b < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X A.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X A.L) z ξ + (1 + A.c1 / A.a1) * leviO X x0 A.ps0 z ξ) ∧
    (∃ b m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < b ∧
      b ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + b < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X A.Fp) z ξ - leviDens X x0 z ξ) ∧
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X A.L) z ξ) ∧
    (∃ C : ℝ, ∀ x ∈ X.dom, A.ps0 x ≤ C) ∧
    (∀ P, X.IsBddSec A.Fp P → P ∈ X.SS A.Fp) ∧
    ∀ (k : ℕ) P, X.IsBddSec (A.Fp + k • A.L) P → P ∈ X.SS (A.Fp + k • A.L) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, ⟨η, h7, h8⟩, h9⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := arch_gaps A h1 h2
  have hT := T_pos A.n_ge A.T_ge
  have hb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb X := by
    have a : (0 : ℝ) < X.Ψ.card := by exact_mod_cast card_pos A.n_ge
    have b : (0 : ℝ) < r := by exact_mod_cast h1.trans h2
    have : 0 < (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
    unfold bb
    linarith
  have hL : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ leviO X x0 (phla X A.L) z ξ := fun x0 ho z hz ξ => by
    by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (A.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le
  have hA : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      19 / 5 * (A.T : ℝ) * leviRh X x0 z ξ ≤ leviO X x0 (phla X A.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X A.L) z ξ := fun x0 ho z hz ξ => by
    have := h8 x0 ho z hz ξ
    have := mul_nonneg h7.le (hL x0 ho z hz ξ)
    linarith
  refine ⟨⟨bb X, _, hb, by linarith, hA⟩, ⟨bb X, _, hb, h5, fun x0 ho z hz ξ => ?_⟩,
    ⟨bb X, _, hb, h6, h9⟩, hL, (arch_extra A).2.2.2.1,
    fun P => cusp_of_gaps A.n_ge h1 h2 g3 g4,
    fun k P => cusp_of_gaps A.n_ge h1 h2 (gaps_add g3 (gapsGe_mono g1 zero_le_one) k) (pair_add g4 g2 k)⟩
  have a := hA x0 ho z hz ξ
  have b := A.base_psi_levi_lower_bound x0 (IW.orth_mem_dom X x0 ho) z hz ξ
  have c : leviM X (phla X A.de) x0 z ξ = 2 * leviRh X x0 z ξ := levi_twoDelta h3 ho hz ξ
  have ht : 0 ≤ 1 + A.c1 / A.a1 := by have := A.frame_theta_const_pos; have := A.frame_theta_weight_pos; positivity
  have d := mul_le_mul_of_nonneg_left b ht
  have e := mul_le_mul_of_nonneg_right A.rr_le (leviRh_nonneg X ho hz ξ)
  rw [c] at d
  unfold leviO at *
  nlinarith

theorem be_eq_monoM {I : ThetaIn X} {A : ArchInM X} (h : Agree I A) :
    I.be = monoM X ![A.et, A.th1] ![2, A.i * A.g0] := by
  obtain ⟨-, -, -, -, h5, h6, -, -, -, -, -, -, h13, h14, -⟩ := h
  funext x
  simp [monoM, ThetaIn.be, ThetaIn.n1, h5, h6, h13, h14]

end Records

theorem typings_equiv (X : Data E r) :
    (∀ u, IsInv X u ↔ IsInvFn X u) ∧
    (∀ x0 u z ξ, levi X x0 u z ξ = leviM X u x0 z ξ) ∧
    (∀ ps a, 0 ≤ a → (CuspDecay X ps a ↔ cfwM X ps a)) ∧
    (∃ e : {I : ThetaIn X // CuspTwo I} ≃
        {q : ArchInM X × ℝ × ℝ × ℝ × ℝ // Explicit q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2},
      ∀ I, Agree I.1 (e I).1.1 ∧ (e I).1.2 = (I.1.RR, I.1.dp, I.1.qp, I.1.η)) ∧
    (∀ I : ThetaIn X, (∃ A : ArchInM X, Agree I A) ↔ CuspTwo I) ∧
    (∀ A : ArchInM X, (∃ I : ThetaIn X, Agree I A) ↔ Side A) ∧
    ∀ (I : ThetaIn X) (A : ArchInM X), Agree I A → I.be = monoM X ![A.et, A.th1] ![2, A.i * A.g0] :=
  ⟨isInv_iff X, levi_eq X, fun ps _ ha => cuspDecay_iff X ps ha,
    ⟨thetaEquiv X, fun I => ⟨agree_toArch I.1 I.2, rfl⟩⟩,
    fun I => ⟨fun ⟨_, h⟩ => h.cuspTwo, fun h => ⟨_, agree_toArch I h⟩⟩,
    fun A => ⟨fun ⟨I, h⟩ => (side_iff A).2 ⟨I.RR, I.dp, I.qp, I.η,
        h.unique (agree_toArch I h.cuspTwo) ▸ explicit_toArch I h.cuspTwo⟩,
      fun h => have ⟨RR, dp, qp, η, k⟩ := (side_iff A).1 h; ⟨_, agree_ofArch A RR dp qp η k⟩⟩,
    fun _ _ => be_eq_monoM⟩

end

end GlobalTheory.ThetaRecordCompare
