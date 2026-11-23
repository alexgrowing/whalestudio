import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

open GlobalTheory.Points

namespace GlobalTheory.ThetaRR

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def tateDefect (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p) (w : LB.Iso (L.pull f hf).B (L.pow 4).B)
    (σ : k →+* ℂ) (a : (L.pow 4).B.ι) (b : (L.pull f hf).B.ι) (y : CxPts p σ) : ℝ :=
  ((L.pow 4).φ σ).φ a y - ((L.pull f hf).φ σ).φ b y - Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)

theorem tateDefect_eq {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) {σ : k →+* ℂ}
    {a a' : (L.pow 4).B.ι} {b b' : (L.pull f hf).B.ι} {y : CxPts p σ}
    (ha : y ∈ ptsIn p σ ((L.pow 4).B.U a)) (ha' : y ∈ ptsIn p σ ((L.pow 4).B.U a'))
    (hb : y ∈ ptsIn p σ ((L.pull f hf).B.U b)) (hb' : y ∈ ptsIn p σ ((L.pull f hf).B.U b')) :
    tateDefect f hf L w σ a' b' y = tateDefect f hf L w σ a b y := by
  have t4 := ((L.pow 4).φ σ).trans a a' y ha ha'
  have tP := ((L.pull f hf).φ σ).trans b b' y hb hb'
  have r := ev_iso_rel hw hb hb' ha ha'
  have e := congrArg (fun z : ℂ => Real.log (‖z‖ ^ 2)) r
  rw [log_normSq_mul (ev_iso_ne_zero w hb ha) (gv_ne_zero hb hb'),
    log_normSq_mul (gv_ne_zero ha ha') (ev_iso_ne_zero w hb' ha')] at e
  unfold tateDefect
  linarith

def tateFn (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p) (w : LB.Iso (L.pull f hf).B (L.pow 4).B)
    (σ : k →+* ℂ) (y : CxPts p σ) : ℝ :=
  tateDefect f hf L w σ (pick (L.pow 4).isLB y) (pick (L.pull f hf).isLB y) y

theorem tateFn_eq {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) {σ : k →+* ℂ}
    {a : (L.pow 4).B.ι} {b : (L.pull f hf).B.ι} {y : CxPts p σ}
    (ha : y ∈ ptsIn p σ ((L.pow 4).B.U a)) (hb : y ∈ ptsIn p σ ((L.pull f hf).B.U b)) :
    tateFn f hf L w σ y = tateDefect f hf L w σ a b y :=
  tateDefect_eq hw ha (mem_pick _ y) hb (mem_pick _ y)

theorem continuousAt_tateDefect (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p)
    (w : LB.Iso (L.pull f hf).B (L.pow 4).B) {σ : k →+* ℂ}
    {a : (L.pow 4).B.ι} {b : (L.pull f hf).B.ι} {y : CxPts p σ}
    (ha : y ∈ ptsIn p σ ((L.pow 4).B.U a)) (hb : y ∈ ptsIn p σ ((L.pull f hf).B.U b)) :
    ContinuousAt (tateDefect f hf L w σ a b) y := by
  have hab : y ∈ ptsIn p σ ((L.pow 4).B.U a ⊓ (L.pull f hf).B.U b) := mem_ptsIn_inf.2 ⟨ha, hb⟩
  have hev : ContinuousAt (fun z => ev p σ _ (w.s (a, b)).val z) y :=
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hab)
  have hne : ‖ev p σ _ (w.s (a, b)).val y‖ ^ 2 ≠ 0 := by
    have := ev_iso_ne_zero w hb ha
    positivity
  exact ((((L.pow 4).cInf σ a y ha).continuousAt).sub
    (((L.pull f hf).cInf σ b y hb).continuousAt)).sub ((hev.norm.pow 2).log hne)

theorem continuous_tateFn {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) (σ : k →+* ℂ) :
    Continuous (tateFn f hf L w σ) := continuous_iff_continuousAt.2 fun y => by
  have ha := mem_pick (L.pow 4).isLB y
  have hb := mem_pick (L.pull f hf).isLB y
  refine (continuousAt_tateDefect f hf L w ha hb).congr ?_
  have ho : ptsIn p σ ((L.pow 4).B.U (pick (L.pow 4).isLB y)) ∩
      ptsIn p σ ((L.pull f hf).B.U (pick (L.pull f hf).isLB y)) ∈ 𝓝 y :=
    ((isOpen_ptsIn _).inter (isOpen_ptsIn _)).mem_nhds ⟨ha, hb⟩
  exact eventually_of_mem ho fun z hz => (tateFn_eq hw hz.1 hz.2).symm

theorem tateFn_conj {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) {σ σ' : k →+* ℂ}
    {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    tateFn f hf L w σ' y' = tateFn f hf L w σ y := by
  have ha := mem_pick (L.pow 4).isLB y
  have hb := mem_pick (L.pull f hf).isLB y
  rw [tateFn_eq hw ((mem_ptsIn_iff_of_conj h).2 ha) ((mem_ptsIn_iff_of_conj h).2 hb)]
  unfold tateFn tateDefect
  rw [(L.pow 4).conj σ σ' _ y y' h ha, (L.pull f hf).conj σ σ' _ y y' h hb, ev_conj' h, norm_star]

def tateSum (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p) (w : LB.Iso (L.pull f hf).B (L.pow 4).B)
    (σ : k →+* ℂ) (y : CxPts p σ) : ℝ :=
  ∑' n : ℕ, (1 / 4 : ℝ) ^ n * tateFn f hf L w σ ((PtsOver.map f hf (spMap σ))^[n] y)

theorem exists_bound_tateFn {D : ℕ} (hX : IsArithVar p D) {f : X ⟶ X} {hf : f ≫ p = p}
    {L : HermLB p} {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) (σ : k →+* ℂ) :
    ∃ C, ∀ y, ‖tateFn f hf L w σ y‖ ≤ C := by
  haveI := GlobalTheory.CxPts.compactSpace σ hX.isProjOver
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_tateFn hw σ).continuousOn
  exact ⟨C, fun y => hC y (mem_univ y)⟩

theorem tateSum_spec {D : ℕ} (hX : IsArithVar p D) {f : X ⟶ X} {hf : f ≫ p = p}
    {L : HermLB p} {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) (σ : k →+* ℂ) :
    Continuous (tateSum f hf L w σ) ∧ ∀ y, tateSum f hf L w σ y =
      tateFn f hf L w σ y + 1 / 4 * tateSum f hf L w σ (PtsOver.map f hf (spMap σ) y) := by
  obtain ⟨C, hC⟩ := exists_bound_tateFn hX hw σ
  set F := PtsOver.map f hf (spMap σ)
  have hF : Continuous F := PtsOver.continuous_map f hf _
  have hg : Summable fun n : ℕ => C * (1 / 4 : ℝ) ^ n :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hb : ∀ (n : ℕ) y, ‖(1 / 4 : ℝ) ^ n * tateFn f hf L w σ (F^[n] y)‖ ≤ C * (1 / 4 : ℝ) ^ n := by
    intro n y
    rw [norm_mul, norm_pow, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4), mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (by positivity)
  refine ⟨continuous_tsum (fun n => continuous_const.mul ((continuous_tateFn hw σ).comp
    (hF.iterate n))) hg hb, fun y => ?_⟩
  have hs : Summable fun n : ℕ => (1 / 4 : ℝ) ^ n * tateFn f hf L w σ (F^[n] y) :=
    Summable.of_norm_bounded hg fun n => hb n y
  unfold tateSum
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, Function.iterate_succ_apply]
  congr 1
  refine tsum_congr fun n => ?_
  ring

theorem tateSum_conj {f : X ⟶ X} {hf : f ≫ p = p} {L : HermLB p}
    {w : LB.Iso (L.pull f hf).B (L.pow 4).B} (hw : w.IsGen) {σ σ' : k →+* ℂ}
    {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    tateSum f hf L w σ' y' = tateSum f hf L w σ y := by
  have key : ∀ n : ℕ, ((PtsOver.map f hf (spMap σ'))^[n] y').1 =
      spMap (starRingEnd ℂ) ≫ ((PtsOver.map f hf (spMap σ))^[n] y).1 := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', PtsOver.map_val,
        PtsOver.map_val, ih, Category.assoc]
  unfold tateSum
  exact tsum_congr fun n => by rw [tateFn_conj hw (key n)]

theorem exists_isTate_continuous : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (f : X ⟶ X) (hf : f ≫ p = p) (L : HermLB p)
    (w : LB.Iso (L.pull f hf).B (L.pow 4).B), w.IsGen → ∃ u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ,
      (∀ σ, Continuous (u σ)) ∧ (∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) ∧
        IsTate f hf L w u := by
  intro k _ X p D hX f hf L w hw
  refine ⟨fun σ y => -(1 / 4) * tateSum f hf L w σ y, fun σ =>
    continuous_const.mul (tateSum_spec hX hw σ).1, fun σ σ' i y y' h _ => ?_, ?_⟩
  · change -(1 / 4) * tateSum f hf L w σ' y' = -(1 / 4) * tateSum f hf L w σ y
    rw [tateSum_conj hw h]
  · intro σ a b y ha hb
    have e := (tateSum_spec hX hw σ).2 y
    have d := tateFn_eq hw ha hb
    unfold tateDefect at d
    linarith

end GlobalTheory.ThetaRR
