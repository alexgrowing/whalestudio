import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CoverDenseAlt.Met

open GlobalTheory.CompanionTheory.Ar.RootHt GlobalTheory.CompanionTheory.Ar.RootHt.ArchC

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def evp (c : (k : K) → J k) (P : MvPolynomial ((k : K) → J k) ℤ) (w : (Σ k, J k) → ℂ) : ℂ :=
  MvPolynomial.aeval (fun c' => segreRatio c c' w) P

omit [∀ k, Fintype (J k)] in
theorem evp_cont (c : (k : K) → J k) (P : MvPolynomial ((k : K) → J k) ℤ) {w : (Σ k, J k) → ℂ}
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) : ContinuousAt (evp c P) w := by
  have hρ : ∀ c', ContinuousAt (fun v : (Σ k, J k) → ℂ => segreRatio c c' v) w := fun c' =>
    tendsto_finset_prod _ fun k _ =>
      ContinuousAt.div (continuous_apply _).continuousAt (continuous_apply _).continuousAt (hc k)
  have e : evp c P =
      fun v => MvPolynomial.eval (fun c' => segreRatio c c' v) (MvPolynomial.map (algebraMap ℤ ℂ) P) := by
    funext v
    rw [MvPolynomial.eval_map, evp, MvPolynomial.aeval_def]
  rw [e]
  exact ContinuousAt.comp (f := fun v : (Σ k, J k) → ℂ => fun c' => segreRatio c c' v)
    (g := fun u => MvPolynomial.eval u (MvPolynomial.map (algebraMap ℤ ℂ) P))
    (MvPolynomial.continuous_eval _).continuousAt (continuousAt_pi.2 hρ)

omit [∀ k, Fintype (J k)] in
theorem evp_smul (c : (k : K) → J k) (P : MvPolynomial ((k : K) → J k) ℤ) (w : (Σ k, J k) → ℂ) (a : K → ℂ)
    (ha : ∀ k, a k ≠ 0) : evp c P (fun p => a p.1 * w p) = evp c P w := by
  unfold evp segreRatio
  simp only [mul_div_mul_left _ _ (ha _)]

omit [∀ k, Fintype (J k)] in
theorem evp_conj (c : (k : K) → J k) (P : MvPolynomial ((k : K) → J k) ℤ) (w : (Σ k, J k) → ℂ) :
    evp c P (fun p => starRingEnd ℂ (w p)) = starRingEnd ℂ (evp c P w) := by
  unfold evp
  induction P using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp only [MvPolynomial.aeval_X, segreRatio, map_prod, map_div₀]

def chi (c : (k : K) → J k) (w : (Σ k, J k) → ℂ) : ℝ := ∏ k, ‖w ⟨k, c k⟩‖ / ‖fun i : J k => w ⟨k, i⟩‖

theorem chi_cont (c : (k : K) → J k) {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    ContinuousAt (chi c) w := by
  refine tendsto_finset_prod _ fun k _ => ContinuousAt.div (continuous_apply _).norm.continuousAt
    (continuous_pi fun i => continuous_apply _).norm.continuousAt ?_
  obtain ⟨i, hi⟩ := hw k
  exact norm_ne_zero_iff.2 fun h => hi (congrFun h i)

theorem chi_smul (c : (k : K) → J k) (w : (Σ k, J k) → ℂ) (a : K → ℂ) (ha : ∀ k, a k ≠ 0) :
    chi c (fun p => a p.1 * w p) = chi c w := by
  refine Finset.prod_congr rfl fun k _ => ?_
  have e : (fun i : J k => a k * w ⟨k, i⟩) = a k • fun i : J k => w ⟨k, i⟩ := rfl
  simp only [e, norm_mul, norm_smul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.2 (ha k))

theorem chi_conj (c : (k : K) → J k) (w : (Σ k, J k) → ℂ) :
    chi c (fun p => starRingEnd ℂ (w p)) = chi c w := by
  refine Finset.prod_congr rfl fun k _ => ?_
  have e : (fun i : J k => starRingEnd ℂ (w ⟨k, i⟩)) = star fun i : J k => w ⟨k, i⟩ := rfl
  simp only [e, norm_star, RCLike.norm_conj]

theorem exists_chi {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    ∃ c, (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ chi c w = 1 := by
  have h : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 ∧ ‖fun i : J k => w ⟨k, i⟩‖ = ‖w ⟨k, i⟩‖ := by
    intro k
    obtain ⟨i₀, h₀⟩ := hw k
    have : Nonempty (J k) := ⟨i₀⟩
    obtain ⟨i, hi⟩ := Finite.exists_max fun i : J k => ‖w ⟨k, i⟩‖
    refine ⟨i, norm_pos_iff.1 ((norm_pos_iff.2 h₀).trans_le (hi i₀)), le_antisymm ?_ ?_⟩
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hi
    · exact norm_le_pi_norm (fun i : J k => w ⟨k, i⟩) i
  choose c hc hc' using h
  exact ⟨c, hc, Finset.prod_eq_one fun k _ => by rw [hc', div_self (norm_ne_zero_iff.2 (hc k))]⟩

def wt (c : (k : K) → J k) (P : MvPolynomial ((k : K) → J k) ℤ) (w : (Σ k, J k) → ℂ) : ℝ :=
  max 0 (chi c w - 1 / 2) * ‖evp c P w‖

theorem wt_nonneg (c : (k : K) → J k) (P : MvPolynomial ((k : K) → J k) ℤ) (w : (Σ k, J k) → ℂ) : 0 ≤ wt c P w :=
  mul_nonneg (le_max_left _ _) (norm_nonneg _)

theorem chi_zero {c : (k : K) → J k} {w : (Σ k, J k) → ℂ} (h : ¬ ∀ k, w ⟨k, c k⟩ ≠ 0) : chi c w = 0 := by
  push Not at h
  obtain ⟨k, hk⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, norm_zero, zero_div])

theorem wt_ne {c : (k : K) → J k} {P : MvPolynomial ((k : K) → J k) ℤ} {w : (Σ k, J k) → ℂ} (h : wt c P w ≠ 0) :
    (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ evp c P w ≠ 0 := by
  refine ⟨?_, fun h0 => h (by rw [wt, h0, norm_zero, mul_zero])⟩
  by_contra h0
  exact h (by rw [wt, chi_zero h0, max_eq_left (by norm_num), zero_mul])

theorem wt_cont (c : (k : K) → J k) (P : MvPolynomial ((k : K) → J k) ℤ) {w : (Σ k, J k) → ℂ}
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : ContinuousAt (wt c P) w := by
  by_cases hc : ∀ k, w ⟨k, c k⟩ ≠ 0
  · exact (continuousAt_const.max ((chi_cont c hw).sub continuousAt_const)).mul (evp_cont c P hc).norm
  · have h1 : ∀ᶠ v in 𝓝 w, chi c v < 1 / 2 :=
      (chi_cont c hw).eventually_lt continuousAt_const (by rw [chi_zero hc]; norm_num)
    refine (continuousAt_const (y := (0 : ℝ))).congr (h1.mono fun v hv => ?_)
    show 0 = wt c P v
    rw [wt, max_eq_left (by linarith), zero_mul]

section Rho

variable {W Λ : Type} [Fintype Λ] (f : Λ → W → ℝ)

def rho (l : Λ) (w : W) : ℝ := max 0 (((Fintype.card Λ : ℝ) + 1) * f l w - ∑ m, f m w)

theorem rho_nonneg (l : Λ) (w : W) : 0 ≤ rho f l w := le_max_left _ _

theorem rho_ne {l : Λ} {w : W} (hf : ∀ l, 0 ≤ f l w) (h : rho f l w ≠ 0) : f l w ≠ 0 := fun h0 =>
  h (by
    have := Finset.sum_nonneg (s := Finset.univ) fun m _ => hf m
    rw [rho, h0, max_eq_left (by linarith)])

theorem exists_rho_pos {w : W} (h : ∃ l, 0 < f l w) : ∃ l, 0 < rho f l w := by
  obtain ⟨l₀, h₀⟩ := h
  have : Nonempty Λ := ⟨l₀⟩
  obtain ⟨l, hl⟩ := Finite.exists_max fun l => f l w
  refine ⟨l, lt_max_of_lt_right ?_⟩
  have h1 : ∑ m, f m w ≤ (Fintype.card Λ : ℝ) * f l w := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun m => f m w) (f l w) fun m _ => hl m
    rwa [nsmul_eq_mul] at this
  have := hl l₀
  linarith

theorem rho_cont [TopologicalSpace W] {w : W} (hc : ∀ l, ContinuousAt (f l) w) (l : Λ) :
    ContinuousAt (rho f l) w :=
  continuousAt_const.max ((continuousAt_const.mul (hc l)).sub (tendsto_finset_sum _ fun m _ => hc m))

theorem rho_eventually [TopologicalSpace W] {w : W} (hc : ∀ l, ContinuousAt (f l) w) (hf : ∀ l, 0 ≤ f l w)
    (h : ∃ l, 0 < f l w) {l : Λ} (hl : f l w = 0) : ∀ᶠ v in 𝓝 w, rho f l v = 0 := by
  obtain ⟨l₀, h₀⟩ := h
  have hs : 0 < ∑ m, f m w := Finset.sum_pos' (fun m _ => hf m) ⟨l₀, Finset.mem_univ _, h₀⟩
  have h1 : ContinuousAt (fun v => ((Fintype.card Λ : ℝ) + 1) * f l v - ∑ m, f m v) w :=
    (continuousAt_const.mul (hc l)).sub (tendsto_finset_sum _ fun m _ => hc m)
  have h2 := h1.eventually_lt (continuousAt_const (y := (0 : ℝ))) (by simp only [hl]; linarith)
  exact h2.mono fun v hv => max_eq_left hv.le

end Rho

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {y : (Σ k, J k) → Ω}

omit [∀ k, Fintype (J k)] in
theorem val_evp {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (c : (k : K) → J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ValAt ξ z (MvPolynomial.aeval (fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) P)
      (evp c P w) :=
  val_aeval hz _ _ (val_segre hz hw c hc) P

theorem unitAt_iff (hξ : IsCptGen ξ) {z : Sp ℂ ⟶ X} (hz : genPt ξ ⤳ centre z) {a : Ω} {s : ℂ}
    (h : ValAt ξ z a s) : unitAt ξ ⟨centre z, hz⟩ a ↔ s ≠ 0 := by
  constructor
  · rintro ⟨h0, -, h2⟩ hs
    obtain ⟨t, ht⟩ := ArchB.val_exists (R := ℂ) h2
    have h3 := ArchB.val_mul h ht
    rw [mul_inv_cancel₀ h0, hs, zero_mul] at h3
    exact zero_ne_one (CxVal.unique h3 (CxVal.one hz))
  · intro hs
    exact ⟨ArchB.val_ne_zero hξ (r := Units.mk0 s hs) h, (ArchB.val_spec h).2, (ArchB.val_spec (CxVal.inv h hs)).2⟩

theorem exists_poly {κ : Type} {x : κ → Ω} {c : κ} {g : Ω} (hg : g ∈ chartRing ℤ x c) :
    ∃ P : MvPolynomial κ ℤ, MvPolynomial.aeval (fun j => x j / x c) P = g := by
  have h : g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := hg
  rw [Algebra.adjoin_range_eq_range_aeval] at h
  exact h

open Classical in

def vl (ξ : Sp Ω ⟶ X) (y : (Σ k, J k) → Ω) (a : Ω) (w : (Σ k, J k) → ℂ) : ℂ :=
  if h : ∃ s : ℂ, ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w ∧ ValAt ξ z a s then h.choose else 0

theorem pt_unique (hall : ∀ q : X, genPt ξ ⤳ q)
    (tie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) {z z' : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z w) (h' : CoordsAt ξ y z' w) : z = z' := by
  have key := GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y tie ℂ
  exact (key.1 w h.1 (key.2.2 z w (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩

theorem vl_eq (hall : ∀ q : X, genPt ξ ⤳ q)
    (tie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z w) {a : Ω} {s : ℂ} (hs : ValAt ξ z a s) : vl ξ y a w = s := by
  have he : ∃ s : ℂ, ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w ∧ ValAt ξ z a s := ⟨s, z, h, hs⟩
  rw [vl, dif_pos he]
  obtain ⟨z', h', hs'⟩ := he.choose_spec
  rw [pt_unique hall tie h' h] at hs'
  exact CxVal.unique hs' hs

theorem vl_cont (hall : ∀ q : X, genPt ξ ⤳ q)
    (tie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) {z₀ : Sp ℂ ⟶ X} {w₀ : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z₀ w₀) {a : Ω} {s₀ : ℂ} (hs : ValAt ξ z₀ a s₀) :
    ContinuousWithinAt (vl ξ y a) {w | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w} w₀ := by
  choose c hc using h.1
  replace hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  obtain ⟨s, hs1, hs2, hs3⟩ := TieFrame.exists_den tie (ArchB.in_chart (hall _) h hc) (ArchB.val_spec hs).2
  obtain ⟨P₂, hP₂⟩ := exists_poly hs1
  obtain ⟨P₁, hP₁⟩ := exists_poly hs3
  have h2 : evp c P₂ w₀ ≠ 0 := by
    have := val_evp (hall _) h c hc P₂
    rw [hP₂] at this
    exact (unitAt_iff tie.gen _ this).1 hs2
  have key : ∀ (w : (Σ k, J k) → ℂ), (∀ k, w ⟨k, c k⟩ ≠ 0) → evp c P₂ w ≠ 0 →
      (∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w) → vl ξ y a w = evp c P₁ w * (evp c P₂ w)⁻¹ := by
    rintro w hw hw2 ⟨z, hz⟩
    have v1 := val_evp (hall _) hz c hw P₁
    have v2 := val_evp (hall _) hz c hw P₂
    rw [hP₁] at v1
    rw [hP₂] at v2
    have v3 := CxVal.mul v1 (CxVal.inv v2 hw2)
    rw [mul_comm s a, mul_inv_cancel_right₀ hs2.1] at v3
    exact vl_eq hall tie hz v3
  have e1 : ∀ᶠ v : (Σ k, J k) → ℂ in 𝓝 w₀, ∀ k, v ⟨k, c k⟩ ≠ 0 :=
    eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  have e2 := (evp_cont c P₂ hc).eventually_ne h2
  refine ((evp_cont c P₁ hc).mul ((evp_cont c P₂ hc).inv₀ h2)).continuousWithinAt.congr_of_eventuallyEq ?_
    (key w₀ hc h2 ⟨z₀, h⟩)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with w h1 h2 h3
  exact key w h1 h2 h3

theorem chart_cover {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) {E : Type} [AddCommGroup E] [Module Ω E]
    {L : Lat ξ E} (hL : L.IsVB (Module.finrank Ω E) ⊤) (c : κ) :
    ∃ (n : ℕ) (P : Fin n → MvPolynomial κ ℤ) (B : Fin n → Module.Basis (Fin (Module.finrank Ω E)) Ω E),
      (∀ l p, InChart ξ x c p → unitAt ξ p (MvPolynomial.aeval (fun j => x j / x c) (P l)) → L.IsFrameAt (B l) p) ∧
      ∀ p, InChart ξ x c p → ∃ l, unitAt ξ p (MvPolynomial.aeval (fun j => x j / x c) (P l)) := by
  by_cases hc : x c = 0
  · exact ⟨0, Fin.elim0, Fin.elim0, fun l => l.elim0, fun p hp => (hp.1 hc).elim⟩
  let S : Set (chartRing ℤ x c) := {g | ∃ b : Fin (Module.finrank Ω E) → E, Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p g → L.IsFrameAt b p}
  have hS : Ideal.span S = ⊤ := TieFrame.ideal_eq_top tie hc _ fun p hp => by
    obtain ⟨g, hg, b, hu, hb, hb'⟩ := TieFrame.exists_frame_basic tie hL hp
    exact ⟨⟨g, hg⟩, Ideal.subset_span ⟨b, hb, hb'⟩, hu⟩
  have h1 : (1 : chartRing ℤ x c) ∈ Submodule.span (chartRing ℤ x c) S := (Ideal.eq_top_iff_one _).1 hS
  obtain ⟨n, a, g, hag⟩ := Submodule.mem_span_set'.1 h1
  choose b hb hb' using fun l => (g l).2
  choose P hP using fun l => exists_poly (g l).1.2
  refine ⟨n, P, fun l => basisOfTopLeSpanOfCardEqFinrank (b l) (hb l).ge (Fintype.card_fin _), fun l p hp hu => ?_,
    fun p hp => ?_⟩
  · rw [coe_basisOfTopLeSpanOfCardEqFinrank]
    rw [hP] at hu
    exact hb' l p hp hu
  · simp only [hP]
    refine TieFrame.exists_unitAt_of_sum tie.gen p _ (fun l => (a l : Ω))
      (fun l => TieFrame.chart_le_regAt tie hp (g l).1.2) (fun l => TieFrame.chart_le_regAt tie hp (a l).2) ?_
    have := congrArg (chartRing ℤ x c).val hag
    simpa [map_sum] using this

end CoverDenseAlt.Met
