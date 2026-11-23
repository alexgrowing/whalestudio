import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticSpaceNonempty
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointInMultiprojectivePoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionThirdStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicCompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietyFirstStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FamCh

section Matrices

variable {N j : ℕ} {ca cb : Fin N}

theorem one_add_single_mul (hne : ca ≠ cb) (s t : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca t) =
      1 + Matrix.single cb ca (s + t) := by
  have e : (Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) * Matrix.single cb ca t = 0 := by
    ext r c
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, Matrix.single_apply]
    split_ifs with h1 h2
    · exact absurd (h1.2.trans h2.1.symm) hne
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]
  rw [mul_add, add_mul, add_mul, e, one_mul, one_mul, mul_one, Matrix.single_add]
  abel

theorem det_transvection_ne (hne : ca ≠ cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := by
  intro h
  have e := congrArg Matrix.det (one_add_single_mul hne t (-t))
  rw [det_mul, h, zero_mul, add_neg_cancel, Matrix.single_zero, add_zero, det_one] at e
  exact zero_ne_one e

theorem blockDiag_transvection (hb : ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s h
  have hrs : r ≠ s := fun e => h (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne hrs, zero_add, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h hb

theorem same_block (hj : j ≤ N) {a b : Fin N} (hba : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) : ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) := by
  have h1 := a.2
  have h2 := b.2
  have h3 := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem flags_ok {Ψ : Type} [DecidableEq Ψ] {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) (τ : Ψ)
    (hb : ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)) (hne : ca ≠ cb) (t : ℂ) (τ' : Ψ) :
    IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') ∧
      (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ').det ≠ 0 := by
  by_cases e : τ' = τ
  · subst e
    rw [Function.update_self]
    exact ⟨(hh _).1.mul (blockDiag_transvection hb t),
      by rw [det_mul]; exact mul_ne_zero (hh _).2 (det_transvection_ne hne t)⟩
  · rw [Function.update_of_ne e]
    exact hh τ'

def hfam {Ψ : Type} [DecidableEq Ψ] {d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ)
    (ca cb : Fin N) (w : Fin d → ℂ) (t : ℂ) : Ψ → Matrix (Fin N) (Fin N) ℂ :=
  Function.update (fun τ' => H τ' w) τ (H τ w * (1 + Matrix.single cb ca t))

theorem hfam_update {Ψ : Type} [DecidableEq Ψ] {d : ℕ} (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ)
    (hne : ca ≠ cb) (w : Fin d → ℂ) (s t : ℂ) :
    Function.update (hfam H τ ca cb w s) τ (hfam H τ ca cb w s τ * (1 + Matrix.single cb ca t)) =
      hfam H τ ca cb w (s + t) := by
  unfold hfam
  rw [Function.update_self, Function.update_idem, mul_assoc, one_add_single_mul hne]

end Matrices

section Analytic

variable {N : ℕ} {e : ℕ} {V : Set (Fin e → ℂ)}

theorem an_sum {α : Type} {s : Finset α} {f : α → (Fin e → ℂ) → ℂ} (h : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) V) :
    AnalyticOnNhd ℂ (fun u => ∑ i ∈ s, f i u) V := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticOnNhd_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem an_prod {α : Type} {s : Finset α} {f : α → (Fin e → ℂ) → ℂ} (h : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) V) :
    AnalyticOnNhd ℂ (fun u => ∏ i ∈ s, f i u) V := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using analyticOnNhd_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem an_det {m : ℕ} {A : (Fin e → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun u => A u r s) V) : AnalyticOnNhd ℂ (fun u => (A u).det) V := by
  simp only [Matrix.det_apply']
  exact an_sum fun σ _ => analyticOnNhd_const.mul (an_prod fun i _ => hA _ _)

theorem an_minorIJ {h : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ r s, AnalyticOnNhd ℂ (fun u => h u r s) V) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun u => minorIJ (h u) I J) V := by
  unfold minorIJ
  by_cases c : I.card = J.card
  · simp only [dif_pos c]
    exact an_det fun r s => hh _ _
  · simp only [dif_neg c]
    exact analyticOnNhd_const

theorem an_mul_transvection {h : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ r s, AnalyticOnNhd ℂ (fun u => h u r s) V) (ca cb : Fin N) {t : (Fin e → ℂ) → ℂ}
    (ht : AnalyticOnNhd ℂ t V) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun u => (h u * (1 + Matrix.single cb ca (t u))) r s) V := by
  simp only [Matrix.mul_apply]
  refine an_sum fun c _ => (hh _ _).mul ?_
  simp only [Matrix.add_apply, Matrix.single_apply]
  refine analyticOnNhd_const.add ?_
  split_ifs
  · exact ht
  · exact analyticOnNhd_const

theorem an_hfam {Ψ : Type} [DecidableEq Ψ] {d : ℕ} {H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ} {τ : Ψ}
    {ca cb : Fin N} {w : (Fin e → ℂ) → Fin d → ℂ} {t : (Fin e → ℂ) → ℂ}
    (hH : ∀ τ' r s, AnalyticOnNhd ℂ (fun u => H τ' (w u) r s) V) (ht : AnalyticOnNhd ℂ t V) (τ' : Ψ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun u => hfam H τ ca cb (w u) (t u) τ' r s) V := by
  by_cases c : τ' = τ
  · subst c
    simp only [hfam, Function.update_self]
    exact an_mul_transvection (hH _) ca cb ht r s
  · simp only [hfam, Function.update_of_ne c]
    exact hH _ _ _

theorem an_chart_comp {D D' : ℕ} {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X] (B : FinHolAtlas D Y)
    (A : FinHolAtlas D' X) {f : Y → X} (hf : HoloMap B A f) (hV : IsOpen V) {g : (Fin e → ℂ) → Y}
    (hg : ContinuousOn g V) (hga : ∀ k, AnalyticOnNhd ℂ (B.chart k ∘ g) (V ∩ g ⁻¹' (B.chart k).source)) (k : Fin A.n) :
    AnalyticOnNhd ℂ (A.chart k ∘ fun u => f (g u)) (V ∩ (fun u => f (g u)) ⁻¹' (A.chart k).source) := by
  rintro u ⟨huV, hus⟩
  obtain ⟨i, hi⟩ := B.cover (g u)
  have h1 : AnalyticAt ℂ (B.chart i ∘ g) u := hga i u ⟨huV, hi⟩
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart i).symm) ((B.chart i ∘ g) u) :=
    hf.2 i k _ ⟨(B.chart i).map_source hi, by
      show f ((B.chart i).symm (B.chart i (g u))) ∈ (A.chart k).source
      rw [(B.chart i).left_inv hi]
      exact hus⟩
  refine (h2.comp h1).congr ?_
  have h3 : ∀ᶠ z in 𝓝 u, g z ∈ (B.chart i).source :=
    (hg.continuousAt (hV.mem_nhds huV)).eventually ((B.chart i).open_source.mem_nhds hi)
  filter_upwards [h3] with z hz
  show A.chart k (f ((B.chart i).symm (B.chart i (g z)))) = A.chart k (f (g z))
  rw [(B.chart i).left_inv hz]

theorem an_tail {e : ℕ} : AnalyticOnNhd ℂ (Fin.tail : (Fin (e + 1) → ℂ) → Fin e → ℂ) Set.univ := fun z _ =>
  (ContinuousLinearMap.pi fun i : Fin e =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (e + 1) => ℂ) i.succ).analyticAt z

theorem an_tail_tail {e : ℕ} :
    AnalyticOnNhd ℂ (fun z : Fin (e + 2) → ℂ => Fin.tail (Fin.tail z)) Set.univ := fun z _ =>
  (ContinuousLinearMap.pi fun i : Fin e =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (e + 2) => ℂ) i.succ.succ).analyticAt z

theorem pull_base {e' D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) {Un : Set (Fin e' → ℂ)}
    {w : (Fin e → ℂ) → Fin e' → ℂ} (hwc : Continuous w) (hwa : AnalyticOnNhd ℂ w Set.univ) {bp : (Fin e' → ℂ) → X}
    (hc : ContinuousOn bp Un) (ha : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source)) :
    ContinuousOn (fun u => bp (w u)) (w ⁻¹' Un) ∧
      ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ fun u => bp (w u)) (w ⁻¹' Un ∩ (fun u => bp (w u)) ⁻¹' (A.chart k).source) :=
  ⟨hc.comp hwc.continuousOn fun _ h => h, fun k u hu =>
    AnalyticAt.comp (g := A.chart k ∘ bp) (f := w) (ha k (w u) hu) (hwa u trivial)⟩

end Analytic

section Families

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem reg_u {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (q : Σ k, ι k)
    (I : Finset (Fin N)) : ∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) ((BM.F l).u q I) := fun b hb =>
  ((FC.bvec_good K ι Φ y Ψ N j M n BM l b hb).2.1.2.1 q I).1

theorem an_flagPt {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source))
    (hO : ∀ u ∈ V, bp u ∈ BM.O l) (h : (Fin e → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hh : ∀ τ' r s, AnalyticOnNhd ℂ (fun u => h u τ' r s) V) (q : Σ k, ι k) :
    AnalyticOnNhd ℂ (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (bp u)) (h u) q) V := by
  obtain ⟨k, m⟩ := q
  have va := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l e V bp hV hc ha hO
  by_cases hk : ∀ p, M.blk p ≠ some k
  · have e1 : (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (bp u)) (h u) ⟨k, m⟩) =
        fun u => FC.bvec BM l (bp u) ⟨⟨k, hk⟩, m⟩ := funext fun u => dif_pos hk
    rw [e1]
    exact va.1 _
  · obtain ⟨p, hp⟩ := not_forall.1 hk
    have hp' := not_not.1 hp
    have e1 : (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (bp u)) (h u) ⟨k, m⟩) =
        fun u => ∑ I, valAt M.x ((BM.F l).u ⟨k, m⟩ I) (FC.bvec BM l (bp u)) *
          minorIJ (h u p.1) I (stepCols N j p.2) := funext fun u => FC.flagPt_step M _ _ _ hp' m
    rw [e1]
    exact an_sum fun I _ => (va.2 _ (reg_u BM l _ _)).mul (an_minorIJ (hh p.1) _ _)

theorem an_wVec {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {e : ℕ}
    {V : Set (Fin e → ℂ)} {bp : (Fin e → ℂ) → BM.Rb.X} (hV : IsOpen V) (hc : ContinuousOn bp V)
    (ha : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source))
    (hO : ∀ u ∈ V, bp u ∈ BM.O l) (h : (Fin e → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hh : ∀ τ' r s, AnalyticOnNhd ℂ (fun u => h u τ' r s) V) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    {t : (Fin e → ℂ) → ℂ} (ht : AnalyticOnNhd ℂ t V) (q : Σ o : Option K, ι (o.getD k₀)) :
    AnalyticOnNhd ℂ (fun u => FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (h u) τ a k₀ ca cb (t u) q) V := by
  obtain ⟨o, m⟩ := q
  cases o with
  | some k => exact an_flagPt BM l hV hc ha hO h hh ⟨k, m⟩
  | none =>
    have va := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l e V bp hV hc ha hO
    show AnalyticOnNhd ℂ (fun u => ∑ I, valAt M.x ((BM.F l).u ⟨k₀, m⟩ I) (FC.bvec BM l (bp u)) *
      minorIJ (h u τ * (1 + Matrix.single cb ca (t u))) I (stepCols N j a)) V
    exact an_sum fun I _ => (va.2 _ (reg_u BM l _ _)).mul
      (an_minorIJ (an_mul_transvection (hh τ) ca cb ht) _ _)

theorem base_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem fst_orbit (k₀ : K) {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem snd_orbit (k₀ : K) {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hc _
    · exact hc _
  · funext ⟨k, m⟩
    by_cases e : k = k₀
    · subst e
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) e, if_neg e]

end Families

theorem charts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (Un : Set (Fin d → ℂ)) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => H τ' w r s) Un) → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ w ∈ Un, bp w ∈ BM.O l \ bdry BM.s ∧ ∀ τ', IsBlockDiag j (H τ' w) ∧ (H τ' w).det ≠ 0) → ∃ (ΦY : (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : (Fin (d + 2) → ℂ) → RW.X), ContinuousOn ΦY {z | Fin.tail z ∈ Un} ∧ (∀ k, AnalyticOnNhd ℂ (FA.S.A.chart k ∘ ΦY) ({z | Fin.tail z ∈ Un} ∩ ΦY ⁻¹' (FA.S.A.chart k).source)) ∧ ContinuousOn ΦW {z | Fin.tail (Fin.tail z) ∈ Un} ∧ (∀ k, AnalyticOnNhd ℂ (RW.A.chart k ∘ ΦW) ({z | Fin.tail (Fin.tail z) ∈ Un} ∩ ΦW ⁻¹' (RW.A.chart k).source)) ∧ (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → FA.pr (ΦY z) = bp (Fin.tail z) ∧ ∀ x₀, FA.Re.π x₀ = ΦY z → SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (bp (Fin.tail z))) (Function.update (fun τ' => H τ' (Fin.tail z)) τ (H τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)))))) ∧ (∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → SameOrbit (RW.lift (ΦW z) (ΦW z)) (FC.wVec M (BM.F l) (FC.bvec BM l (bp (Fin.tail (Fin.tail z)))) (Function.update (fun τ' => H τ' (Fin.tail (Fin.tail z))) τ (H τ (Fin.tail (Fin.tail z)) * (1 + Matrix.single cb ca (z 0)))) τ a k₀ ca cb (z 1 - z 0)) ∧ q 0 (ΦW z) = ΦY (Fin.cons (z 0) (Fin.tail (Fin.tail z))) ∧ q 1 (ΦW z) = ΦY (Fin.tail z)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hba hab hk₀ hca hcb RW q hq hq0 hq1 hqi l Un H bp hUn hH hbc hba' hOk
  have hne : ca ≠ cb := fun e => by rw [e] at hcb; omega
  have hsb := same_block M.j_le hba hab hca hcb
  have hbi := FC.re_pi_bijective K ι Φ y Ψ N j M n d BM FA
  haveI : Nonempty FA.S.X := FibNonempty.flagAn_S_nonempty K ι Φ y Ψ N j M n d BM FA
  haveI : Nonempty FA.Re.R.X := by
    obtain ⟨x⟩ := ‹Nonempty FA.S.X›
    exact (hbi.2 x).elim fun r _ => ⟨r⟩
  haveI : Nonempty RW.X := GlobalTheory.T.flag_adjacent_twisted_resolution_third K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hba hab hk₀ hca hcb RW
  have hO : ∀ w ∈ Un, bp w ∈ BM.O l := fun w hw => (hOk w hw).1.1
  have hfl : ∀ w ∈ Un, ∀ t τ', IsBlockDiag j (hfam H τ ca cb w t τ') ∧ (hfam H τ ca cb w t τ').det ≠ 0 :=
    fun w hw t => flags_ok (hOk w hw).2 τ hsb hne t
  have hnot : ∀ z, z ∉ mcPts FA.Re.J := fun z => by rw [FA.J_top]; exact Proj.not_mem_mcPts_top z
  have exY : ∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Un → ∃ x, SameOrbit (FA.Re.R.lift x x)
      (FC.flagPt M (BM.F l) (FC.bvec BM l (bp (Fin.tail z))) (hfam H τ ca cb (Fin.tail z) (z 0))) := fun z hz =>
    FA.Re.R.surj _ (FC.flagPt_mem_mcPts K ι Φ y Ψ N j M n BM l _ (hO _ hz) _ (hfl _ hz _)) (hnot _)
  have exW : ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Un → ∃ x, SameOrbit (RW.lift x x)
      (FC.wVec M (BM.F l) (FC.bvec BM l (bp (Fin.tail (Fin.tail z)))) (hfam H τ ca cb (Fin.tail (Fin.tail z)) (z 0))
        τ a k₀ ca cb (z 1 - z 0)) := fun z hz =>
    RW.surj _ (GlobalTheory.T.flag_adjacent_arith_variety_first K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hba hab hk₀ hca hcb FA.Re.arith l _ (hO _ hz) _ _
      (hfl _ hz _)) (Proj.not_mem_mcPts_top _)
  choose! g hg using exY
  choose! ΦW hW using exW

  have hwc1 : Continuous (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) :=
    continuous_pi fun i => continuous_apply _
  have hwc2 : Continuous (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) :=
    continuous_pi fun i => continuous_apply _
  have hV1 : IsOpen {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Un} := hUn.preimage hwc1
  have hV2 : IsOpen {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Un} := hUn.preimage hwc2
  have hp1 := pull_base BM.Rb.A hwc1 an_tail hbc hba'
  have hp2 := pull_base BM.Rb.A hwc2 an_tail_tail hbc hba'
  have hH1 : ∀ τ' r s, AnalyticOnNhd ℂ (fun z : Fin (d + 1) → ℂ => H τ' (Fin.tail z) r s) {z | Fin.tail z ∈ Un} :=
    fun τ' r s z hz => by
      have h1 : AnalyticAt ℂ (fun w => H τ' w r s) (Fin.tail z) := hH τ' r s _ hz
      exact h1.comp (an_tail z trivial)
  have hH2 : ∀ τ' r s, AnalyticOnNhd ℂ (fun z : Fin (d + 2) → ℂ => H τ' (Fin.tail (Fin.tail z)) r s)
      {z | Fin.tail (Fin.tail z) ∈ Un} :=
    fun τ' r s z hz => by
      have h1 : AnalyticAt ℂ (fun w => H τ' w r s) (Fin.tail (Fin.tail z)) := hH τ' r s _ hz
      exact AnalyticAt.comp (f := fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) h1 (an_tail_tail z trivial)
  have ht1 : AnalyticOnNhd ℂ (fun z : Fin (d + 1) → ℂ => z 0) {z | Fin.tail z ∈ Un} := fun z _ =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt z
  have ht2 : AnalyticOnNhd ℂ (fun z : Fin (d + 2) → ℂ => z 0) {z | Fin.tail (Fin.tail z) ∈ Un} := fun z _ =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 2) => ℂ) 0).analyticAt z
  have ht3 : AnalyticOnNhd ℂ (fun z : Fin (d + 2) → ℂ => z 1 - z 0) {z | Fin.tail (Fin.tail z) ∈ Un} := fun z hz =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 2) => ℂ) 1).analyticAt z).sub (ht2 z hz)
  have anY : ∀ q', AnalyticOnNhd ℂ (fun z : Fin (d + 1) → ℂ => FC.flagPt M (BM.F l) (FC.bvec BM l (bp (Fin.tail z)))
      (hfam H τ ca cb (Fin.tail z) (z 0)) q') {z | Fin.tail z ∈ Un} :=
    an_flagPt BM l hV1 hp1.1 hp1.2 (fun z hz => hO _ hz) (fun z => hfam H τ ca cb (Fin.tail z) (z 0)) (an_hfam hH1 ht1)
  have anW : ∀ q', AnalyticOnNhd ℂ (fun z : Fin (d + 2) → ℂ => FC.wVec M (BM.F l) (FC.bvec BM l (bp (Fin.tail (Fin.tail z))))
      (hfam H τ ca cb (Fin.tail (Fin.tail z)) (z 0)) τ a k₀ ca cb (z 1 - z 0) q') {z | Fin.tail (Fin.tail z) ∈ Un} :=
    an_wVec BM l hV2 hp2.1 hp2.2 (fun z hz => hO _ hz) (fun z => hfam H τ ca cb (Fin.tail (Fin.tail z)) (z 0))
      (an_hfam hH2 ht2) τ a k₀ ca cb ht3
  obtain ⟨hgc, hga⟩ := HoloLift.holo_of_analytic_lift _ _ _ _ _ _ FA.Re.R FA.J_top _ _ g hV1 anY hg
  obtain ⟨hWc, hWa⟩ := HoloLift.holo_of_analytic_lift _ _ _ _ _ _ RW rfl _ _ ΦW hV2 anW hW
  refine ⟨fun z => FA.Re.π (g z), ΦW, FA.Re.holo.1.comp_continuousOn hgc,
    an_chart_comp FA.Re.R.A FA.S.A FA.Re.holo hV1 hgc hga, hWc, hWa, fun z hz => ⟨?_, fun x₀ hx₀ => ?_⟩,
    fun z hz => ⟨hW z hz, ?_, ?_⟩⟩
  · have h1 := FA.pr_eq (g z)
    have h2 := base_orbit M.blk (hg z hz)
    rw [FC.basePart_flagPt] at h2
    have h3 := (FC.bvec_good K ι Φ y Ψ N j M n BM l _ (hO _ hz)).2.2.2
    exact BM.Rb.inj _ _ (Proj.not_mem_mcPts_top _) (orbit_trans (orbit_symm h1) (orbit_trans h2 h3))
  · rw [hbi.1 hx₀]
    exact hg z hz
  · have hs := FC.fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hba hab hk₀ hca hcb (BM.F l)
      (FC.bvec BM l (bp (Fin.tail (Fin.tail z)))) (hfam H τ ca cb (Fin.tail (Fin.tail z)) (z 0)) (z 1 - z 0)
    obtain ⟨x₀, hx₀⟩ := hbi.2 (q 0 (ΦW z))
    have o1 := hq0 (ΦW z) x₀ hx₀
    have o2 := fst_orbit k₀ (hW z hz)
    rw [hs.1] at o2
    have o3 := hg (Fin.cons (z 0) (Fin.tail (Fin.tail z))) (by simpa [Fin.tail_cons] using hz)
    rw [Fin.tail_cons, Fin.cons_zero] at o3
    rw [← hx₀, FA.Re.R.inj _ _ (hnot _) (orbit_trans o1 (orbit_trans o2 (orbit_symm o3)))]
  · have hs := FC.fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hba hab hk₀ hca hcb (BM.F l)
      (FC.bvec BM l (bp (Fin.tail (Fin.tail z)))) (hfam H τ ca cb (Fin.tail (Fin.tail z)) (z 0)) (z 1 - z 0)
    obtain ⟨x₀, hx₀⟩ := hbi.2 (q 1 (ΦW z))
    have o1 := hq1 (ΦW z) x₀ hx₀
    have o2 := snd_orbit k₀ (hW z hz)
    rw [hs.2, hfam_update H τ hne, add_sub_cancel] at o2
    have o3 := hg (Fin.tail z) hz
    have e1 : Fin.tail z 0 = z 1 := by simp [Fin.tail]
    rw [e1] at o3
    rw [← hx₀, FA.Re.R.inj _ _ (hnot _) (orbit_trans o1 (orbit_trans o2 (orbit_symm o3)))]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FamCh
