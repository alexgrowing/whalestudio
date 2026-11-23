import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LimsupAddTendsto
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivializationStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.Bdd

open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular

theorem continuousAt_of_holoOn {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X} {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨i, hi⟩ := A.cover x
  have h1 := (hg i (A.chart i x) ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩).continuousAt
  refine (h1.comp ((A.chart i).continuousAt hi)).congr ?_
  filter_upwards [(A.chart i).open_source.mem_nhds hi] with y hy
  simp [(A.chart i).left_inv hy]

theorem limsup_invol {X : Type} [TopologicalSpace X] {σ : X → X} (hσ : Continuous σ) (hi : ∀ x, σ (σ x) = x)
    {Y : Set X} (hY : ∀ x ∈ Y, σ x ∈ Y) {g : X → ℝ} (hg : ∀ x ∈ Y, g (σ x) = g x) (x : X) :
    limsup g (𝓝[Y] (σ x)) = limsup g (𝓝[Y] x) := by
  have ht : ∀ x, map σ (𝓝[Y] x) ≤ 𝓝[Y] (σ x) := fun x =>
    (hσ.continuousWithinAt (s := Y) (x := x)).tendsto_nhdsWithin hY
  have he : map σ (𝓝[Y] x) = 𝓝[Y] (σ x) := by
    refine le_antisymm (ht x) ?_
    have h1 := map_mono (m := σ) (ht (σ x))
    rw [Filter.map_map, show σ ∘ σ = id from funext hi, Filter.map_id, hi] at h1
    exact h1
  rw [← he, ← limsup_comp]
  exact limsup_congr (eventually_nhdsWithin_of_forall hg)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} (M : XModel D)

theorem smul_inv (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
  funext p
  simp [torusSmul, hc]

theorem bd_iff {z z' : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) (hz' : z' ∈ mcPts (mCoordIdeal D.y))
    (h : M.proj z = M.proj z') : z ∈ D.Bd ↔ z' ∈ D.Bd := by
  obtain ⟨c, hc, e⟩ := (M.fibre z hz z' hz').1 h
  obtain ⟨c', hc', e'⟩ := (M.fibre z' hz' z hz).1 h.symm
  exact ⟨fun h => e ▸ D.bd_torus z h c hc, fun h => e' ▸ D.bd_torus z' h c' hc'⟩

def Yo : Set M.Xc := {x | (M.surj x).choose ∉ D.Bd}

theorem proj_mem_Yo {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) : M.proj z ∈ Yo M ↔ z ∉ D.Bd :=
  not_congr (bd_iff M (M.surj (M.proj z)).choose_spec.1 hz (M.surj (M.proj z)).choose_spec.2)

noncomputable def ph0 (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (x : M.Xc) : ℝ :=
  w (M.surj x).choose - Real.log (ref.h (M.surj x).choose)

theorem relative_weight_projection {ref : HermLine J} {w : ((Σ k, J k) → ℂ) → ℝ} (hL : LogHom D ref.a w) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ D.Xo) : ph0 M ref w (M.proj z) = w z - Real.log (ref.h z) := by
  obtain ⟨hw, he⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, e⟩ := (M.fibre z hz.1 _ hw).1 he.symm
  have h2 := SncPiece.logHom_log D ref z hz c hc
  unfold ph0
  rw [e, hL z hz c hc]
  simp only at h2
  rw [h2]
  ring

theorem analyticAt_sec {ψ : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)} (hψ : IsCompatChart M.atlas ψ)
    {U : Set M.Xc} {s : M.Xc → (Σ k, J k) → ℂ} (hs : ∀ p, M.atlas.HoloOn U fun y => s y p) {v : Fin D.n → ℂ}
    (hv : v ∈ ψ.target) (hU : ψ.symm v ∈ U) (p : Σ k, J k) : AnalyticAt ℂ (fun u => s (ψ.symm u) p) v := by
  have h := analyticAt_comp_symm_of_holoOn hψ (hs p) hU (ψ.map_target hv)
  rwa [ψ.right_inv hv] at h

theorem exists_factor {ψ : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)} (hψ : IsCompatChart M.atlas ψ)
    {v : Fin D.n → ℂ} (hv : v ∈ ψ.target) :
    ∃ (a : Fin D.nCharts) (F : (Fin D.n → ℂ) → Fin D.n → ℂ), AnalyticAt ℂ F v ∧
      ∀ᶠ u in 𝓝 v, F u ∈ ball (0 : Fin D.n → ℂ) 1 ∧ M.proj ((D.chart a).γ (F u)) = ψ.symm u := by
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections (ψ.symm v)
  obtain ⟨a, t₀, ht₀, c, hc, e⟩ := D.chart_cover _ (hs _ hx).1
  obtain ⟨V, T, hV, hV0, hT, -, hTz⟩ := GlobalTheory.T.chart_local_analytic_trivialization K J II Ψ Ω W D a t₀ (mem_ball_zero_iff.2 (by linarith))
  let σ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ := fun u => torusSmul (fun k => (c k)⁻¹) (s (ψ.symm u))
  have hσ : AnalyticAt ℂ σ v := analyticAt_pi_iff.2 fun p => analyticAt_const.mul (analyticAt_sec M hψ hh hv hx p)
  have hσv : σ v ∈ V := by
    change torusSmul _ (s (ψ.symm v)) ∈ V
    rwa [e, smul_inv c hc]
  refine ⟨a, fun u => T (σ u), (hT _ hσv).comp hσ, ?_⟩
  filter_upwards [hσ.continuousAt.eventually (hV.mem_nhds hσv),
    (ψ.continuousAt_symm hv).eventually (hU.mem_nhds hx)] with u h1 h2
  have hm : σ u ∈ mcPts (mCoordIdeal D.y) :=
    mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) (hs _ h2).1
  obtain ⟨hb, c', hc', e'⟩ := hTz _ ⟨h1, hm⟩
  refine ⟨hb, ?_⟩
  rw [(M.fibre _ ((D.chart a).mem _ hb) _ hm).2 ⟨c', hc', e'⟩,
    ← (M.fibre _ (hs _ h2).1 _ hm).2 ⟨_, fun k => inv_ne_zero (hc k), rfl⟩, (hs _ h2).2]

theorem isOpen_nz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const

variable {ref : HermLine J} {w : ((Σ k, J k) → ℂ) → ℝ} (P : PotentialCharts M.atlas)

include P in

theorem relative_weight_bounded (hr : IsSmoothHerm ref) (hL : LogHom D ref.a w) (hB : ChartBdd D w) :
    ∃ C, ∀ y ∈ Yo M, |ph0 M ref w y| ≤ C := by
  have hloc : ∀ x : M.Xc, ∃ C, ∀ᶠ y in 𝓝 x, y ∈ Yo M → |ph0 M ref w y| ≤ C := by
    intro x
    obtain ⟨j, hj⟩ := P.cover x
    have hx := P.mid_subset_source j (P.inner_subset_mid j hj)
    obtain ⟨a, F, hF, hev⟩ := exists_factor M (P.compat j) ((P.chart j).map_source hx)
    have hb := hev.self_of_nhds.1
    obtain ⟨ε, hε, C, hC⟩ := hB a _ hb
    have hm := (D.chart a).mem _ hb
    have hc : ContinuousAt (fun u => Real.log (ref.h ((D.chart a).γ (F u)))) (P.chart j x) :=
      ((hr.continuousOn.continuousAt (isOpen_nz.mem_nhds hm.1)).comp (f := fun u => (D.chart a).γ (F u))
        (((D.chart a).analytic _ hb).continuousAt.comp hF.continuousAt)).log (ref.pos _ hm.1).ne'
    have h3 := (hev.and (hc.eventually (ball_mem_nhds _ one_pos))).and (hF.continuousAt.eventually (ball_mem_nhds _ hε))
    refine ⟨C + (|Real.log (ref.h ((D.chart a).γ (F (P.chart j x))))| + 1), ?_⟩
    filter_upwards [((P.chart j).continuousAt hx).eventually h3, (P.chart j).open_source.mem_nhds hx] with y hy hys hY
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, h5⟩ := hy
    rw [(P.chart j).left_inv hys] at h2
    have hm' := (D.chart a).mem _ h1
    have hbd : (D.chart a).γ (F (P.chart j y)) ∉ D.Bd := (proj_mem_Yo M hm').1 (by rw [h2]; exact hY)
    have h6 := hC _ ⟨h1, hbd⟩ ((dist_eq_norm _ _).symm.trans_lt h5)
    have h7 := relative_weight_projection M hL (z := (D.chart a).γ (F (P.chart j y))) ⟨hm', hbd⟩
    rw [h2] at h7
    have h8 : |Real.log (ref.h ((D.chart a).γ (F (P.chart j y)))) -
        Real.log (ref.h ((D.chart a).γ (F (P.chart j x))))| < 1 := h4
    rw [h7]
    refine (abs_sub _ _).trans (add_le_add h6 ?_)
    linarith [abs_sub_abs_le_abs_sub (Real.log (ref.h ((D.chart a).γ (F (P.chart j y)))))
      (Real.log (ref.h ((D.chart a).γ (F (P.chart j x)))))]
  choose C hC using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => {y | y ∈ Yo M → |ph0 M ref w y| ≤ C x})
    fun x _ => hC x
  refine ⟨∑ x ∈ t, |C x|, fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  exact ((hxy hy).trans (le_abs_self _)).trans (Finset.single_le_sum (fun x _ => abs_nonneg (C x)) hx)

theorem symm_mem_Yo {S : Fin P.N → Finset (Fin D.n)} (hA : Adapted M P S) (j : Fin P.N) {v : Fin D.n → ℂ}
    (hv : v ∈ (P.chart j).target) : (P.chart j).symm v ∈ Yo M ↔ v ∉ coordDiv (S j) :=
  not_congr (hA.mem_bd_iff hv (M.surj _).choose_spec.1 (M.surj _).choose_spec.2.symm)

theorem chart_local (hth : ThRef M ref P.th) (hL : LogHom D ref.a w) (hP : ChartPsh D w) (hC : ChartCont D w)
    (j : Fin P.N) {v : Fin D.n → ℂ} (hv : v ∈ (P.chart j).target) (hY : ∀ᶠ u in 𝓝 v, (P.chart j).symm u ∈ Yo M) :
    ContinuousAt (fun u => P.q j u + ph0 M ref w ((P.chart j).symm u)) v ∧
      ∃ V, IsOpen V ∧ v ∈ V ∧ IsPsh V fun u => P.q j u + ph0 M ref w ((P.chart j).symm u) := by
  classical
  obtain ⟨a, F, hF, hev⟩ := exists_factor M (P.compat j) hv
  have hxs := (P.chart j).map_target hv
  obtain ⟨U, hU, hxU, hUs, s, hs, hh, G, hG, hGe⟩ := hth _ _ (P.th.mem_U ((P.chart j).symm v))
  obtain ⟨W', hW, hxW, G', hG', hGe'⟩ := P.q_th j _ _ ⟨P.th.mem_U ((P.chart j).symm v), hxs⟩
  have a1 := analyticAt_comp_symm_of_holoOn (P.compat j) hG hxU hxs
  have a2 := analyticAt_comp_symm_of_holoOn (P.compat j) hG' hxW hxs
  rw [(P.chart j).right_inv hv] at a1 a2
  have hb := hev.self_of_nhds.1
  have hm := (D.chart a).mem _ hb
  choose i hi using hm.1
  have hγ : ∀ k, AnalyticAt ℂ (fun u => (D.chart a).γ (F u) ⟨k, i k⟩) v := fun k =>
    analyticAt_pi_iff.1 (((D.chart a).analytic _ hb).comp hF) ⟨k, i k⟩
  have hsa := fun k => analyticAt_sec M (P.compat j) hh hv hxU ⟨k, i k⟩
  have hs0 : ∀ k, s ((P.chart j).symm v) ⟨k, i k⟩ ≠ 0 := by
    obtain ⟨c, hc, e⟩ := (M.fibre _ hm _ (hs _ hxU).1).1 (hev.self_of_nhds.2.trans (hs _ hxU).2.symm)
    intro k
    rw [e]
    exact mul_ne_zero (hc k) (hi k)
  have hPH : PH (fun u => (∑ k, (ref.a k : ℝ) *
      Real.log ‖s ((P.chart j).symm u) ⟨k, i k⟩ / (D.chart a).γ (F u) ⟨k, i k⟩‖) +
        ((G ((P.chart j).symm u)).re + (G' ((P.chart j).symm u)).re)) v :=
    (PH.sum _ fun k _ => (PH.log_norm ((hsa k).div (hγ k) (hi k)) (div_ne_zero (hs0 k) (hi k))).const_mul _).add
      (PH.add ⟨_, a1, Eventually.of_forall fun _ => rfl⟩ ⟨_, a2, Eventually.of_forall fun _ => rfl⟩)
  have hbd : ∀ᶠ u in 𝓝 v, F u ∈ offBd D a := by
    filter_upwards [hev, hY] with u h1 h2
    exact ⟨h1.1, (proj_mem_Yo M ((D.chart a).mem _ h1.1)).1 (h1.2 ▸ h2)⟩
  refine local_psh (SncPiece.isOpen_offBd D a) (hC a) (hP a) hF hbd.self_of_nhds hPH ?_
  filter_upwards [hev, hbd, (P.chart j).open_target.mem_nhds hv,
    ((P.chart j).continuousAt_symm hv).eventually (hU.mem_nhds hxU),
    ((P.chart j).continuousAt_symm hv).eventually (hW.mem_nhds hxW),
    eventually_all.2 fun k => (hγ k).continuousAt.eventually_ne (hi k)] with u h1 h2 h3 h4 h5 h6
  have hXo := SncPiece.mem_Xo_of_offBd D h2
  obtain ⟨c, hc, e⟩ := (M.fibre _ hXo.1 _ (hs _ h4).1).1 (h1.2.trans (hs _ h4).2.symm)
  have e1 := hGe _ h4
  have e2 := hGe' _ ⟨⟨h5, hUs h4⟩, (P.chart j).map_target h3⟩
  rw [(P.chart j).right_inv h3] at e2
  have e3 := relative_weight_projection M hL hXo
  rw [h1.2] at e3
  have e4 := SncPiece.logHom_log D ref _ hXo c hc
  simp only at e4
  rw [← e] at e4
  have e5 : ∀ k, s ((P.chart j).symm u) ⟨k, i k⟩ / (D.chart a).γ (F u) ⟨k, i k⟩ = c k := fun k => by
    rw [e]
    exact mul_div_cancel_right₀ _ (h6 k)
  simp only [e5]
  linarith

open Classical in

noncomputable def ph (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (x : M.Xc) : ℝ :=
  if x ∈ Yo M then ph0 M ref w x else limsup (ph0 M ref w) (𝓝[Yo M] x)

theorem map_nhds_Yo {S : Fin P.N → Finset (Fin D.n)} (hA : Adapted M P S) (j : Fin P.N) {v : Fin D.n → ℂ}
    (hv : v ∈ (P.chart j).target) :
    map (P.chart j).symm (𝓝[(P.chart j).target \ coordDiv (S j)] v) = 𝓝[Yo M] ((P.chart j).symm v) := by
  rw [← (P.chart j).symm.map_nhdsWithin_preimage_eq hv]
  congr 1
  exact nhdsWithin_eq_nhdsWithin' ((P.chart j).open_target.mem_nhds hv) (Set.ext fun y =>
    ⟨fun h => ⟨(symm_mem_Yo M P hA j h.2).2 h.1.2, h.2⟩, fun h => ⟨⟨h.2, (symm_mem_Yo M P hA j h.2).1 h.1⟩, h.2⟩⟩)

noncomputable def cj (x : M.Xc) : M.Xc := M.proj (conjVec (M.surj x).choose)

theorem cj_proj {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) : cj M (M.proj z) = M.proj (conjVec z) := by
  obtain ⟨hw, he⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, e⟩ := (M.fibre z hz _ hw).1 he.symm
  refine ((M.fibre _ (SncPiece.conj_mem hz) _ (SncPiece.conj_mem hw)).2
    ⟨fun k => starRingEnd ℂ (c k), fun k => (map_ne_zero _).2 (hc k), ?_⟩).symm
  rw [e]
  funext p
  simp [conjVec, torusSmul]

theorem continuous_cj : Continuous (cj M) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections x
  have h1 : ContinuousAt (fun y => conjVec (s y)) x := continuousAt_pi.2 fun p =>
    Complex.continuous_conj.continuousAt.comp (continuousAt_of_holoOn (hh p) hx)
  have h2 : ContinuousWithinAt (fun y => M.proj (conjVec (s y))) U x :=
    (M.cont _ (SncPiece.conj_mem (hs x hx).1)).comp (f := fun y => conjVec (s y)) h1.continuousWithinAt
      fun y hy => SncPiece.conj_mem (hs y hy).1
  refine (h2.continuousAt (hU.mem_nhds hx)).congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  rw [← cj_proj M (hs y hy).1, (hs y hy).2]

theorem ph_conj (hL : LogHom D ref.a w) (hr : IsConjInvariantH ref) (hO : ConjOff D w) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) : ph M ref w (M.proj (conjVec z)) = ph M ref w (M.proj z) := by
  have hi : ∀ x, cj M (cj M x) = x := fun x => by
    obtain ⟨z, hz, rfl⟩ := M.surj x
    rw [cj_proj M hz, cj_proj M (SncPiece.conj_mem hz), SncPiece.conj_conj]
  have hY : ∀ x, cj M x ∈ Yo M ↔ x ∈ Yo M := fun x => by
    obtain ⟨z, hz, rfl⟩ := M.surj x
    rw [cj_proj M hz, proj_mem_Yo M hz, proj_mem_Yo M (SncPiece.conj_mem hz), SncPiece.conj_mem_bd_iff]
  have hg : ∀ x ∈ Yo M, ph0 M ref w (cj M x) = ph0 M ref w x := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := M.surj x
    have hz' : z ∈ D.Xo := ⟨hz, (proj_mem_Yo M hz).1 hx⟩
    have e : ref.h (conjVec z) = ref.h z := hr z
    rw [cj_proj M hz, relative_weight_projection M hL hz', relative_weight_projection M hL (SncPiece.conj_mem_Xo D hz'), hO z hz', e]
  rw [← cj_proj M hz]
  unfold ph
  by_cases h : M.proj z ∈ Yo M
  · rw [if_pos h, if_pos ((hY _).2 h), hg _ h]
  · rw [if_neg h, if_neg fun h' => h ((hY _).1 h'),
      limsup_invol (continuous_cj M) hi (fun x hx => (hY x).2 hx) hg]

end LevelTowerAlt.Bdd

open LevelTowerAlt.Bdd in
theorem LevelTowerAlt.potential_charts_regular_bound : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (ref : HermLine J) (w : ((Σ k, J k) → ℂ) → ℝ) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (S : Fin P.N → Finset (Fin D.n)), IsSmoothHerm ref → ThRef M ref P.th → Adapted M P S → LogHom D ref.a w → ChartPsh D w → ChartCont D w → ChartBdd D w → ∃ B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData M.atlas, B.toPotentialCharts = P ∧ (∀ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), B.ph (M.proj z) = w z - Real.log (ref.h z)) ∧ (IsConjInvariantH ref → ConjOff D w → ∀ z ∈ mcPts (mCoordIdeal D.y), B.ph (M.proj (conjVec z)) = B.ph (M.proj z)) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M ref w P S hr hth hA hL hP hC hB
  obtain ⟨C, hCb⟩ := relative_weight_bounded M P hr hL hB
  have hloc := fun j v (hv : v ∈ (P.chart j).target \ ReciprocityTheory.AnForm.A.coordDiv (S j)) =>
    chart_local M P hth hL hP hC j hv.1 (by
      filter_upwards [((P.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)).mem_nhds hv]
        with u hu
      exact (symm_mem_Yo M P hA j hu.1).2 hu.2)
  refine ⟨{ toPotentialCharts := P, ph := ph M ref w, bdd := ⟨C, fun x => ?_⟩, u_psh := fun j => ?_ }, rfl,
    fun z hz => ?_, fun hr' hO z hz => ph_conj M hL hr' hO hz⟩
  · unfold ph
    split_ifs with h
    · exact hCb x h
    · obtain ⟨j, hj⟩ := P.cover x
      have hx := P.mid_subset_source j (P.inner_subset_mid j hj)
      have h1 := map_nhds_Yo M P hA j ((P.chart j).map_source hx)
      rw [(P.chart j).left_inv hx] at h1
      have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S j) (P.chart j).open_target ((P.chart j).map_source hx)
      have : (𝓝[Yo M] x).NeBot := h1 ▸ inferInstance
      exact abs_limsup_le (eventually_nhdsWithin_of_forall hCb)
  · refine isPsh_ext (P.chart j).open_target (P.target_subset j) (S j)
      (g := fun u => ph0 M ref w ((P.chart j).symm u)) (C := C) (P.q_smooth j).continuousOn
      (fun v hv => hCb _ ((symm_mem_Yo M P hA j hv.1).2 hv.2))
      (fun v hv => (hloc j v hv).1.continuousWithinAt)
      (GlobalTheory.T.plurisubharmonic_local _ _ _ ((P.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _))
        fun v hv => (hloc j v hv).2)
      (fun v hv => if_pos ((symm_mem_Yo M P hA j hv.1).2 hv.2)) fun v hv hS => ?_
    show ph M ref w ((P.chart j).symm v) = _
    unfold ph
    rw [if_neg fun h => (symm_mem_Yo M P hA j hv).1 h hS, ← map_nhds_Yo M P hA j hv]
    rfl
  · show ph M ref w (M.proj z) = _
    unfold ph
    rw [if_pos ((proj_mem_Yo M hz.2).2 hz.1.2), relative_weight_projection M hL hz.1]
