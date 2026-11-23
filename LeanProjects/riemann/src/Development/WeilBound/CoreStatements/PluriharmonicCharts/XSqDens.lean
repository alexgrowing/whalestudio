import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.sq_dens

open scoped ComplexOrder ContDiff

def PH {D : ℕ} (z : Fin D → ℂ) (f g : (Fin D → ℂ) → ℝ) : Prop :=
  ∃ H : (Fin D → ℂ) → ℂ, AnalyticAt ℂ H z ∧ ∀ᶠ w in 𝓝 z, f w = g w + (H w).re

namespace PH

variable {D : ℕ} {z : Fin D → ℂ}

theorem of_ev {f g : (Fin D → ℂ) → ℝ} (h : ∀ᶠ w in 𝓝 z, f w = g w) : PH z f g :=
  ⟨fun _ => 0, analyticAt_const, h.mono fun w hw => by simp [hw]⟩

theorem refl' (f : (Fin D → ℂ) → ℝ) : PH z f f := of_ev (Eventually.of_forall fun _ => rfl)

theorem symm {f g : (Fin D → ℂ) → ℝ} (h : PH z f g) : PH z g f := by
  obtain ⟨H, hH, e⟩ := h
  refine ⟨fun w => -H w, hH.neg, e.mono fun w hw => ?_⟩
  rw [hw, Complex.neg_re]
  ring

theorem trans {f g h : (Fin D → ℂ) → ℝ} (h1 : PH z f g) (h2 : PH z g h) : PH z f h := by
  obtain ⟨H1, hH1, e1⟩ := h1
  obtain ⟨H2, hH2, e2⟩ := h2
  refine ⟨fun w => H1 w + H2 w, hH1.add hH2, (e1.and e2).mono fun w hw => ?_⟩
  dsimp only
  rw [hw.1, hw.2, Complex.add_re]
  ring

theorem add {f g f' g' : (Fin D → ℂ) → ℝ} (h1 : PH z f g) (h2 : PH z f' g') :
    PH z (fun w => f w + f' w) (fun w => g w + g' w) := by
  obtain ⟨H1, hH1, e1⟩ := h1
  obtain ⟨H2, hH2, e2⟩ := h2
  refine ⟨fun w => H1 w + H2 w, hH1.add hH2, (e1.and e2).mono fun w hw => ?_⟩
  dsimp only
  rw [hw.1, hw.2, Complex.add_re]
  ring

theorem sub {f g f' g' : (Fin D → ℂ) → ℝ} (h1 : PH z f g) (h2 : PH z f' g') :
    PH z (fun w => f w - f' w) (fun w => g w - g' w) := by
  obtain ⟨H1, hH1, e1⟩ := h1
  obtain ⟨H2, hH2, e2⟩ := h2
  refine ⟨fun w => H1 w - H2 w, hH1.sub hH2, (e1.and e2).mono fun w hw => ?_⟩
  dsimp only
  rw [hw.1, hw.2, Complex.sub_re]
  ring

theorem smul (c : ℝ) {f g : (Fin D → ℂ) → ℝ} (h : PH z f g) : PH z (fun w => c * f w) (fun w => c * g w) := by
  obtain ⟨H, hH, e⟩ := h
  refine ⟨fun w => (c : ℂ) * H w, analyticAt_const.mul hH, e.mono fun w hw => ?_⟩
  dsimp only
  rw [hw, Complex.re_ofReal_mul]
  ring

theorem sum {ι : Type*} (s : Finset ι) {f g : ι → (Fin D → ℂ) → ℝ} (h : ∀ i ∈ s, PH z (f i) (g i)) :
    PH z (fun w => ∑ i ∈ s, f i w) (fun w => ∑ i ∈ s, g i w) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact refl' _
  · intro a s ha ih h
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congr' {f g f' g' : (Fin D → ℂ) → ℝ} (h : PH z f g) (hf : ∀ w, f' w = f w) (hg : ∀ w, g' w = g w) :
    PH z f' g' := by
  obtain ⟨H, hH, e⟩ := h
  exact ⟨H, hH, e.mono fun w hw => by rw [hf, hg, hw]⟩

theorem comp {D' : ℕ} {L : (Fin D' → ℂ) → (Fin D → ℂ)} {y : Fin D' → ℂ} (hL : AnalyticAt ℂ L y)
    {f g : (Fin D → ℂ) → ℝ} (h : PH (L y) f g) : PH y (fun w => f (L w)) (fun w => g (L w)) := by
  obtain ⟨H, hH, e⟩ := h
  exact ⟨fun w => H (L w), hH.comp hL, hL.continuousAt.eventually e⟩

end PH

theorem maDens_eq {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (h : ∀ r, PH z (φ r) (ψ r))
    (hψ : ∀ r, ContDiffAt ℝ 2 (ψ r) z) : maDens φ z = maDens ψ z := by
  have e : ∀ r, hessC (φ r) z = hessC (ψ r) z := by
    intro r
    obtain ⟨H, hH, hev⟩ := h r
    have hev' : φ r =ᶠ[𝓝 z] fun w => ψ r w + (H w).re := hev
    have h2 : fderiv ℝ (fderiv ℝ (φ r)) z = fderiv ℝ (fderiv ℝ (fun w => ψ r w + (H w).re)) z :=
      hev'.fderiv.fderiv_eq
    have h1 : hessC (φ r) z = hessC (fun w => ψ r w + (H w).re) z := by
      unfold hessC
      rw [h2]
    rw [h1]
    exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic' _ _ _ (hψ r) hH
  have : (fun r => hessC (φ r) z) = fun r => hessC (ψ r) z := funext e
  simp only [maDens, this]

theorem holo_comp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {V : Set X} {G : X → ℂ}
    (hG : A.HoloOn V G) {Vp : Set (Fin e → ℂ)} {Φ : (Fin e → ℂ) → X} (hΦ : IsParam A Vp Φ) {z : Fin e → ℂ}
    (hz : z ∈ Vp) (hzV : Φ z ∈ V) : AnalyticAt ℂ (fun w => G (Φ w)) z := by
  obtain ⟨j, hj⟩ := A.cover (Φ z)
  have hcont : ContinuousAt Φ z := hΦ.2.1.continuousAt (hΦ.1.mem_nhds hz)
  have h1 : AnalyticAt ℂ (A.chart j ∘ Φ) z := hΦ.2.2.2 j z ⟨hz, hj⟩
  have h2 : AnalyticAt ℂ (G ∘ (A.chart j).symm) ((A.chart j ∘ Φ) z) :=
    hG j _ ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hzV]⟩
  refine (h2.comp h1).congr ?_
  filter_upwards [hcont.preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)] with w hw
  simp [Function.comp, (A.chart j).left_inv hw]

def lin {D D' : ℕ} (τ : Fin D' → Fin D) (z : Fin D → ℂ) : Fin D' → ℂ := fun j => z (τ j)

theorem lin_analyticAt {D D' : ℕ} (τ : Fin D' → Fin D) (z : Fin D → ℂ) : AnalyticAt ℂ (lin τ) z := by
  have : lin τ = ⇑(ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) (τ j)) := by
    funext w
    rfl
  rw [this]
  exact ContinuousLinearMap.analyticAt _ _

theorem lin_contDiff {D D' : ℕ} (τ : Fin D' → Fin D) : ContDiff ℝ 2 (lin τ) :=
  contDiff_pi.2 fun j => contDiff_apply ℝ ℂ (τ j)

theorem herm2_line_expand (G : Matrix (Fin 2) (Fin 2) ℂ) (b : ℂ) :
    herm2 G ![1, b] ![1, b] = G 0 0 + G 0 1 * b + (starRingEnd ℂ) b * G 1 0 + (starRingEnd ℂ) b * G 1 1 * b := by
  simp [herm2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem contDiffAt_xiPot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Matrix (Fin 2) (Fin 2) ℂ}
    {b : E → ℂ} {x : E} (hF : ∀ p q, ContDiffAt ℝ 2 (fun y => F y p q) x) (hb : ContDiffAt ℝ 2 b x)
    (hpos : (F x).PosDef) : ContDiffAt ℝ 2 (fun y => xiPot (F y) (b y)) x := by
  have e : (fun y => xiPot (F y) (b y)) = fun y =>
      -Real.log (F y 0 0 + F y 0 1 * b y + (starRingEnd ℂ) (b y) * F y 1 0 + (starRingEnd ℂ) (b y) * F y 1 1 * b y).re
        + (1 / 2) * Real.log (F y 0 0 * F y 1 1 - F y 0 1 * F y 1 0).re := by
    funext y
    rw [xiPot, herm2_line_expand, Matrix.det_fin_two]
  have hpos1 : 0 < (herm2 (F x) ![1, b x] ![1, b x]).re := by
    have hne : (![1, b x] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 0
    exact (Complex.lt_def.mp (hpos.dotProduct_mulVec_pos hne)).1
  have hpos2 : 0 < (F x).det.re := (Complex.lt_def.mp hpos.det_pos).1
  rw [herm2_line_expand] at hpos1
  rw [Matrix.det_fin_two] at hpos2
  rw [e]
  have hc : ContDiffAt ℝ 2 (fun y => (starRingEnd ℂ) (b y)) x :=
    Complex.conjCLE.contDiff.contDiffAt.comp x hb
  have hS := (((hF 0 0).add ((hF 0 1).mul hb)).add (hc.mul (hF 1 0))).add ((hc.mul (hF 1 1)).mul hb)
  have hD := ((hF 0 0).mul (hF 1 1)).sub ((hF 0 1).mul (hF 1 0))
  have hSr : ContDiffAt ℝ 2 (fun y => (F y 0 0 + F y 0 1 * b y + (starRingEnd ℂ) (b y) * F y 1 0 +
      (starRingEnd ℂ) (b y) * F y 1 1 * b y).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hS
  have hDr : ContDiffAt ℝ 2 (fun y => (F y 0 0 * F y 1 1 - F y 0 1 * F y 1 0).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hD
  exact (hSr.log hpos1.ne').neg.add (contDiffAt_const.mul (hDr.log hpos2.ne'))

section Sq

variable {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ} {ε : σ → ℤ} (Q : AnSq SY a₀ ε)

theorem G_cd (n : ℕ) (p q : Fin 2) {y : Fin d → ℂ} (hy : y ∈ Q.U n) :
    ContDiffAt ℝ 2 (fun y => Q.G n y p q) y :=
  ((Q.G_smooth n p q).contDiffAt ((Q.U_open n).mem_nhds hy)).of_le (WithTop.coe_le_coe.2 le_top)

theorem α_cd (n : ℕ) (a : σ) {y : Fin d → ℂ} (hy : y ∈ Q.U n) : ContDiffAt ℝ 2 (Q.α n a) y :=
  ((Q.α_smooth n a).contDiffAt ((Q.U_open n).mem_nhds hy)).of_le (WithTop.coe_le_coe.2 le_top)

theorem xi_cd {D : ℕ} (n : ℕ) (τ : Fin d → Fin D) (j : Fin D) {z : Fin D → ℂ} (hz : lin τ z ∈ Q.U n) :
    ContDiffAt ℝ 2 (fun z' => xiPot (Q.G n (lin τ z')) (z' j)) z :=
  contDiffAt_xiPot (fun p q => (G_cd Q n p q hz).comp z (lin_contDiff τ).contDiffAt)
    (contDiff_apply ℝ ℂ j).contDiffAt (Q.G_pos n _ hz)

theorem sumα_cd {D : ℕ} (n : ℕ) (c : σ → ℝ) (τ : Fin d → Fin D) {z : Fin D → ℂ} (hz : lin τ z ∈ Q.U n) :
    ContDiffAt ℝ 2 (fun z' => ∑ a, c a * Q.α n a (lin τ z')) z :=
  ContDiffAt.sum fun a _ => contDiffAt_const.mul ((α_cd Q n a hz).comp z (lin_contDiff τ).contDiffAt)

theorem part1 (c : σ → ℝ) (hc : c a₀ = 0) (n k : ℕ) (z : Fin (d + 1) → ℂ) (hz : Fin.tail z ∈ Q.U n) :
    paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
      maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then
        xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z := by
  unfold paramDens
  apply maDens_eq
  · intro r
    by_cases hr : (r : ℕ) < 2 * k - 1
    · simp only [sumPot, mix, hr, ↓reduceIte]
      obtain ⟨H, hH, hev⟩ := Q.xi_pot n z hz
      exact ⟨H, hH, hev⟩
    · simp only [sumPot, mix, hr, ↓reduceIte]
      refine PH.sum (f := fun a z' => c a * (SY.potH a).φ (Q.ΦY n z) (Q.ΦY n z'))
        (g := fun a z' => c a * Q.α n a (Fin.tail z')) Finset.univ fun a _ => ?_
      by_cases ha : a = a₀
      · subst ha
        simp only [hc, zero_mul]
        exact PH.refl' _
      · obtain ⟨H, hH, hev⟩ := Q.base_pot n a ha z hz
        exact PH.smul (c a) ⟨H, hH, hev⟩
  · intro r
    by_cases hr : (r : ℕ) < 2 * k - 1
    · simp only [hr, ↓reduceIte]
      exact xi_cd Q n Fin.succ 0 hz
    · simp only [hr, ↓reduceIte]
      exact sumα_cd Q n c Fin.succ hz

theorem potH_φ {e : ℕ} {τ : Type} (S : AnSys e τ) (a : τ) (x y : S.X) :
    (S.potH a).φ x y = (S.th a).φ x y + S.ph a y := rfl

def τ0 (d : ℕ) : Fin (d + 1) → Fin (d + 2) := Fin.cons 0 (fun m : Fin d => m.succ.succ)

theorem lin_τ0 (z : Fin (d + 2) → ℂ) : lin (τ0 d) z = (Fin.cons (z 0) (Fin.tail (Fin.tail z)) : Fin (d + 1) → ℂ) := by
  funext j
  refine Fin.cases ?_ (fun m => ?_) j
  · simp [lin, τ0]
  · simp [lin, τ0, Fin.tail]

theorem ev_U (n : ℕ) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    ∀ᶠ z' : Fin (d + 2) → ℂ in 𝓝 z, Fin.tail (Fin.tail z') ∈ Q.U n :=
  ((Q.coverW.1 n).1).mem_nhds hz

theorem M0 (n : ℕ) (a : σ) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => (Q.SW.potH (some a)).φ (Q.ΦW n z) (Q.ΦW n z'))
      (fun z' => (SY.potH a).φ (Q.ΦY n (lin (τ0 d) z)) (Q.ΦY n (lin (τ0 d) z'))) := by
  obtain ⟨V, hVo, hxV, G, hG, hid⟩ := Q.th0 a (Q.ΦW n z) (Set.mem_univ _)
  refine ⟨fun w => G (Q.ΦW n w), holo_comp Q.SW.A hG (Q.coverW.1 n) hz hxV, ?_⟩
  have hcont : ContinuousAt (Q.ΦW n) z := (Q.coverW.1 n).2.1.continuousAt (((Q.coverW.1 n).1).mem_nhds hz)
  filter_upwards [hcont.preimage_mem_nhds (hVo.mem_nhds hxV), ev_U Q n hz] with z' h1 h2
  have e1 := hid _ h1
  have e2 := Q.first_projection_chart_compat n z hz
  have e3 := Q.first_projection_chart_compat n z' h2
  change (Q.SW.th (some a)).φ (Q.ΦW n z) (Q.ΦW n z') - (SY.th a).φ (Q.q 0 (Q.ΦW n z)) (Q.q 0 (Q.ΦW n z')) = _ at e1
  rw [e2, e3] at e1
  rw [potH_φ, potH_φ, Q.ph0 a, Function.comp_apply, e3, lin_τ0, lin_τ0]
  linarith

theorem M1 (n : ℕ) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => (Q.SW.potH none).φ (Q.ΦW n z) (Q.ΦW n z'))
      (fun z' => (SY.potH a₀).φ (Q.ΦY n (lin Fin.succ z)) (Q.ΦY n (lin Fin.succ z'))) := by
  obtain ⟨V, hVo, hxV, G, hG, hid⟩ := Q.th1 (Q.ΦW n z) (Set.mem_univ _)
  refine ⟨fun w => G (Q.ΦW n w), holo_comp Q.SW.A hG (Q.coverW.1 n) hz hxV, ?_⟩
  have hcont : ContinuousAt (Q.ΦW n) z := (Q.coverW.1 n).2.1.continuousAt (((Q.coverW.1 n).1).mem_nhds hz)
  filter_upwards [hcont.preimage_mem_nhds (hVo.mem_nhds hxV), ev_U Q n hz] with z' h1 h2
  have e1 := hid _ h1
  have e2 := Q.second_projection_chart_compat n z hz
  have e3 := Q.second_projection_chart_compat n z' h2
  change (Q.SW.th none).φ (Q.ΦW n z) (Q.ΦW n z') - (SY.th a₀).φ (Q.q 1 (Q.ΦW n z)) (Q.q 1 (Q.ΦW n z')) = _ at e1
  rw [e2, e3] at e1
  rw [potH_φ, potH_φ, Q.ph1, Function.comp_apply, e3]
  change _ = (SY.th a₀).φ (Q.ΦY n (Fin.tail z)) (Q.ΦY n (Fin.tail z')) + SY.ph a₀ (Q.ΦY n (Fin.tail z')) + _
  linarith

theorem Y0 (n : ℕ) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => ∑ a, (ε a : ℝ) * (SY.potH a).φ (Q.ΦY n (lin (τ0 d) z)) (Q.ΦY n (lin (τ0 d) z')))
      (fun z' => xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0)) := by
  have hz0 : Fin.tail (lin (τ0 d) z) ∈ Q.U n := by rw [lin_τ0, Fin.tail_cons]; exact hz
  obtain ⟨H, hH, hev⟩ := Q.xi_pot n (lin (τ0 d) z) hz0
  refine (PH.comp (lin_analyticAt (τ0 d) z) (f := fun ζ => ∑ a, (ε a : ℝ) * (SY.potH a).φ (Q.ΦY n (lin (τ0 d) z)) (Q.ΦY n ζ))
    (g := fun ζ => xiPot (Q.G n (Fin.tail ζ)) (ζ 0)) ⟨H, hH, hev⟩).congr' (fun w => rfl) (fun w => ?_)
  rw [lin_τ0, Fin.tail_cons, Fin.cons_zero]

theorem Y1 (n : ℕ) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => ∑ a, (ε a : ℝ) * (SY.potH a).φ (Q.ΦY n (lin Fin.succ z)) (Q.ΦY n (lin Fin.succ z')))
      (fun z' => xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1)) := by
  obtain ⟨H, hH, hev⟩ := Q.xi_pot n (lin Fin.succ z) hz
  refine (PH.comp (lin_analyticAt Fin.succ z) (f := fun ζ => ∑ a, (ε a : ℝ) * (SY.potH a).φ (Q.ΦY n (lin Fin.succ z)) (Q.ΦY n ζ))
    (g := fun ζ => xiPot (Q.G n (Fin.tail ζ)) (ζ 0)) ⟨H, hH, hev⟩).congr' (fun w => rfl) (fun w => ?_)
  simp only [lin]
  rw [Fin.succ_zero_eq_one]
  rfl

theorem Ya0 (n : ℕ) (a : σ) (ha : a ≠ a₀) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => (SY.potH a).φ (Q.ΦY n (lin (τ0 d) z)) (Q.ΦY n (lin (τ0 d) z')))
      (fun z' => Q.α n a (Fin.tail (Fin.tail z'))) := by
  have hz0 : Fin.tail (lin (τ0 d) z) ∈ Q.U n := by rw [lin_τ0, Fin.tail_cons]; exact hz
  obtain ⟨H, hH, hev⟩ := Q.base_pot n a ha (lin (τ0 d) z) hz0
  refine (PH.comp (lin_analyticAt (τ0 d) z) (f := fun ζ => (SY.potH a).φ (Q.ΦY n (lin (τ0 d) z)) (Q.ΦY n ζ))
    (g := fun ζ => Q.α n a (Fin.tail ζ)) ⟨H, hH, hev⟩).congr' (fun w => rfl) (fun w => ?_)
  rw [lin_τ0, Fin.tail_cons]

theorem Ya1 (n : ℕ) (a : σ) (ha : a ≠ a₀) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => (SY.potH a).φ (Q.ΦY n (lin Fin.succ z)) (Q.ΦY n (lin Fin.succ z')))
      (fun z' => Q.α n a (Fin.tail (Fin.tail z'))) := by
  obtain ⟨H, hH, hev⟩ := Q.base_pot n a ha (lin Fin.succ z) hz
  exact (PH.comp (lin_analyticAt Fin.succ z) (f := fun ζ => (SY.potH a).φ (Q.ΦY n (lin Fin.succ z)) (Q.ΦY n ζ))
    (g := fun ζ => Q.α n a (Fin.tail ζ)) ⟨H, hH, hev⟩).congr' (fun w => rfl) (fun w => rfl)

theorem K0 (n : ℕ) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => ∑ o, Q.pull0 (fun a => (ε a : ℝ)) o * (Q.SW.potH o).φ (Q.ΦW n z) (Q.ΦW n z'))
      (fun z' => xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0)) := by
  refine ((PH.sum (f := fun a z' => (ε a : ℝ) * (Q.SW.potH (some a)).φ (Q.ΦW n z) (Q.ΦW n z'))
    (g := fun a z' => (ε a : ℝ) * (SY.potH a).φ (Q.ΦY n (lin (τ0 d) z)) (Q.ΦY n (lin (τ0 d) z')))
    Finset.univ fun a _ => (M0 Q n a hz).smul _).trans (Y0 Q n hz)).congr' (fun w => ?_) (fun w => rfl)
  rw [Fintype.sum_option]
  simp [AnSq.pull0]

theorem KA (n : ℕ) (c : σ → ℝ) (hc : c a₀ = 0) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => ∑ o, Q.pull0 c o * (Q.SW.potH o).φ (Q.ΦW n z) (Q.ΦW n z'))
      (fun z' => ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) := by
  refine (PH.sum (f := fun a z' => c a * (Q.SW.potH (some a)).φ (Q.ΦW n z) (Q.ΦW n z'))
    (g := fun a z' => c a * Q.α n a (Fin.tail (Fin.tail z'))) Finset.univ fun a _ => ?_).congr' (fun w => ?_)
    (fun w => rfl)
  · by_cases ha : a = a₀
    · subst ha
      simp only [hc, zero_mul]
      exact PH.refl' _
    · exact ((M0 Q n a hz).trans (Ya0 Q n a ha hz)).smul _
  · rw [Fintype.sum_option]
    simp [AnSq.pull0]

open Classical in
theorem sum_split (v f : σ → ℝ) :
    v a₀ * f a₀ + ∑ a, (if a = a₀ then 0 else v a) * f a = ∑ a, v a * f a := by
  classical
  have : ∀ a, (if a = a₀ then 0 else v a) * f a = v a * f a - (if a = a₀ then v a₀ * f a₀ else 0) := by
    intro a
    by_cases h : a = a₀ <;> simp [h]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem K1 (n : ℕ) {z : Fin (d + 2) → ℂ} (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    PH z (fun z' => ∑ o, Q.pull1 (fun a => (ε a : ℝ)) o * (Q.SW.potH o).φ (Q.ΦW n z) (Q.ΦW n z'))
      (fun z' => xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1)) := by
  classical
  have hs := PH.sum (z := z) (f := fun a z' => (if a = a₀ then 0 else (ε a : ℝ)) * (Q.SW.potH (some a)).φ (Q.ΦW n z) (Q.ΦW n z'))
    (g := fun a z' => (if a = a₀ then 0 else (ε a : ℝ)) * (SY.potH a).φ (Q.ΦY n (lin Fin.succ z)) (Q.ΦY n (lin Fin.succ z')))
    Finset.univ fun a _ => by
      by_cases ha : a = a₀
      · simp only [ha, if_true, zero_mul]
        exact PH.refl' _
      · simp only [ha, if_false]
        exact ((M0 Q n a hz).trans ((Ya0 Q n a ha hz).trans (Ya1 Q n a ha hz).symm)).smul _
  refine (((M1 Q n hz).smul (ε a₀ : ℝ)).add hs |>.trans (Y1 Q n hz |>.congr' (fun w => ?_) (fun w => rfl))).congr'
    (fun w => ?_) (fun w => rfl)
  · exact sum_split (a₀ := a₀) (fun a => (ε a : ℝ)) (fun a => (SY.potH a).φ (Q.ΦY n (lin Fin.succ z)) (Q.ΦY n (lin Fin.succ w)))
  · rw [Fintype.sum_option]
    simp only [AnSq.pull1, Option.elim]
    try congr 1
    try (refine Finset.sum_congr rfl fun a _ => ?_; by_cases ha : a = a₀ <;> simp [ha])

theorem wcoef_eq (c : σ → ℝ) (k i : ℕ) (hk : 1 ≤ k) (r : Fin (d + 2)) :
    Q.wcoef c k i r = if (r : ℕ) = 0 then Q.pull0 (fun a => (ε a : ℝ)) - Q.pull1 (fun a => (ε a : ℝ))
      else if (r : ℕ) = 1 then Q.pull1 (fun a => (ε a : ℝ))
      else if (r : ℕ) < 2 + 2 * i then Q.pull0 (fun a => (ε a : ℝ))
      else if (r : ℕ) < 2 * k then Q.pull1 (fun a => (ε a : ℝ)) else Q.pull0 c := by
  refine Fin.cases ?_ (fun j => ?_) r
  · simp [AnSq.wcoef]
  · have hj : ((j.succ : Fin (d + 2)) : ℕ) = (j : ℕ) + 1 := Fin.val_succ j
    simp only [AnSq.wcoef, Fin.cons_succ, ReciprocityTheory.ChartRestriction.G.AI.word]
    split_ifs <;> first | rfl | omega

theorem part2 (c : σ → ℝ) (hc : c a₀ = 0) (n k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i < k) (z : Fin (d + 2) → ℂ)
    (hz : Fin.tail (Fin.tail z) ∈ Q.U n) :
    paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  unfold paramDens
  refine (maDens_eq _ (fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) =>
    if (r : ℕ) = 0 then xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) - xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1)
    else if (r : ℕ) = 1 then xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1)
    else if (r : ℕ) < 2 + 2 * i then xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0)
    else if (r : ℕ) < 2 * k then xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1)
    else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z ?_ ?_).trans (congrArg (fun F => maDens F z) ?_)
  · intro r
    simp only [sumPot]
    rw [wcoef_eq Q c k i hk r]
    by_cases h0 : (r : ℕ) = 0
    · simp only [h0, ↓reduceIte, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact (K0 Q n hz).sub (K1 Q n hz)
    · by_cases h1 : (r : ℕ) = 1
      · simp only [h0, h1, ↓reduceIte]
        exact K1 Q n hz
      · by_cases h2 : (r : ℕ) < 2 + 2 * i
        · simp only [h0, h1, h2, ↓reduceIte]
          exact K0 Q n hz
        · by_cases h3 : (r : ℕ) < 2 * k
          · simp only [h0, h1, h2, h3, ↓reduceIte]
            exact K1 Q n hz
          · simp only [h0, h1, h2, h3, ↓reduceIte]
            exact KA Q n c hc hz
  · intro r
    have hx0 : ContDiffAt ℝ 2 (fun z' : Fin (d + 2) → ℂ => xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0)) z :=
      xi_cd Q n (fun m : Fin d => m.succ.succ) 0 hz
    have hx1 : ContDiffAt ℝ 2 (fun z' : Fin (d + 2) → ℂ => xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1)) z :=
      xi_cd Q n (fun m : Fin d => m.succ.succ) 1 hz
    have hA : ContDiffAt ℝ 2 (fun z' : Fin (d + 2) → ℂ => ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z :=
      sumα_cd Q n c (fun m : Fin d => m.succ.succ) hz
    by_cases h0 : (r : ℕ) = 0
    · simp only [h0, ↓reduceIte]
      exact hx0.sub hx1
    · by_cases h1 : (r : ℕ) = 1
      · simp only [h0, h1, ↓reduceIte]
        exact hx1
      · by_cases h2 : (r : ℕ) < 2 + 2 * i
        · simp only [h0, h1, h2, ↓reduceIte]
          exact hx0
        · by_cases h3 : (r : ℕ) < 2 * k
          · simp only [h0, h1, h2, h3, ↓reduceIte]
            exact hx1
          · simp only [h0, h1, h2, h3, ↓reduceIte]
            exact hA
  · funext r z'
    dsimp only
    by_cases h0 : (r : ℕ) = 0
    · have : 0 < k := by omega
      simp [h0, this]
      try ring
    · by_cases h1 : (r : ℕ) = 1
      · have : 1 < 2 * k := by omega
        simp [h1, this]
      · by_cases h2 : (r : ℕ) < 2 + 2 * i
        · have : (r : ℕ) < 2 * k := by omega
          simp [h0, h1, h2, this]
        · by_cases h3 : (r : ℕ) < 2 * k
          · simp [h0, h1, h2, h3]
          · simp [h0, h1, h2, h3]

end Sq

end PositivityTheory.Xgp.sq_dens
