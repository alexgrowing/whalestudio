import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.Regularisation.RegMaxReindex
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventuallyStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt.Conj

open MeasureTheory Metric
open ReciprocityTheory.AnForm.A (Mollifier molli regMax)
open GroundTheory.Heights₂.Heights.Regular

theorem integral_star {n : ℕ} (g : (Fin n → ℂ) → ℝ) : ∫ v, g (star v) = ∫ v, g v := by
  have hc : MeasurePreserving (fun z : ℂ => star z) volume volume := Complex.conjLIE.measurePreserving
  have hmp : MeasurePreserving (fun v : Fin n → ℂ => star v) volume volume := by
    rw [volume_pi]
    exact measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => hc)
  exact hmp.integral_comp (starL' ℝ : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ)).toHomeomorph.measurableEmbedding g

theorem molli_star {n : ℕ} (ρ : Mollifier n) (hρ : ∀ v, ρ.toFun (star v) = ρ.toFun v) {t : ℝ} (ht : 0 < t)
    {u u' : (Fin n → ℂ) → ℝ} {y : Fin n → ℂ} (h : ∀ v ∈ closedBall y t, u' (star v) = u v) :
    molli ρ t u' (star y) = molli ρ t u y := by
  unfold molli
  rw [← integral_star (fun w => ρ.scaled t w * u' (star y - w))]
  congr 1
  funext v
  have hs : ρ.scaled t (star v) = ρ.scaled t v := by
    simp only [Mollifier.scaled]
    rw [show t⁻¹ • star v = star (t⁻¹ • v) by rw [star_smul, star_trivial t⁻¹], hρ]
  rw [hs]
  by_cases h0 : ρ.toFun (t⁻¹ • v) = 0
  · simp [Mollifier.scaled, h0]
  · have hb := ρ.support_subset h0
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht,
      inv_mul_lt_iff₀ ht, _root_.mul_one] at hb
    rw [← star_sub, h (y - v) (by rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hb.le)]

theorem eventually_margin {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas n X} (P : PotentialCharts A) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ P.mid j, closedBall (P.chart j x) t ⊆ (P.chart j).target := by
  rw [Filter.eventually_all]
  intro j
  have hK : IsCompact ((P.chart j) '' closure (P.mid j)) :=
    isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono (P.closure_mid j))
  have hsub : (P.chart j) '' closure (P.mid j) ⊆ (P.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (P.chart j).map_source (P.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := hK.exists_cthickening_subset_open (P.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ (subset_closure hx)) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

noncomputable def symmH {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (A : HermLine J) : HermLine J where
  a := A.a
  h z := (A.h z + A.h (conjVec z)) / 2
  pos z hz := by
    have h1 := A.pos z hz
    have h2 := A.pos (conjVec z) fun k => (hz k).imp fun i hi => (map_ne_zero _).2 hi
    positivity
  smul c z hc := by
    have e : conjVec (fun p : Σ k, J k => c p.1 * z p) = fun p => (starRingEnd ℂ (c p.1)) * conjVec z p := by
      funext p; simp [conjVec]
    rw [e, A.smul c z hc, A.smul (fun k => starRingEnd ℂ (c k)) _ fun k => (map_ne_zero _).2 (hc k)]
    simp only [Complex.norm_conj]
    ring

theorem symmH_smooth {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {A : HermLine J}
    (hA : IsSmoothHerm A) : IsSmoothHerm (symmH A) := by
  unfold IsSmoothHerm at hA ⊢
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (conjVec : ((Σ k, J k) → ℂ) → ((Σ k, J k) → ℂ)) :=
    (starL' ℝ : ((Σ k, J k) → ℂ) ≃L[ℝ] ((Σ k, J k) → ℂ)).contDiff
  have hmaps : Set.MapsTo (conjVec : ((Σ k, J k) → ℂ) → ((Σ k, J k) → ℂ))
      {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    fun z hz k => (hz k).imp fun i hi => (map_ne_zero _).2 hi
  exact (hA.add (hA.comp hc.contDiffOn hmaps)).div_const 2

theorem symmH_conj {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (A : HermLine J) :
    IsConjInvariantH (symmH A) := fun z => by
  change (A.h (conjVec z) + A.h (conjVec (conjVec z))) / 2 = (A.h z + A.h (conjVec z)) / 2
  rw [SncPiece.conj_conj, add_comm]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} {M : XModel D}

theorem regularised_conj (B : BoundedPshData M.atlas) (κ : Equiv.Perm (Fin B.N))
    (hS : SymmCharts M B.toPotentialCharts κ) (ρ : Mollifier D.n) (hρ : ∀ v, ρ.toFun (star v) = ρ.toFun v)
    (ct : Fin B.N → M.Xc → ℝ)
    (hη : ∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), ct (κ j) (M.proj (conjVec z)) = ct j (M.proj z))
    (hph : ∀ z ∈ mcPts (mCoordIdeal D.y), B.ph (M.proj (conjVec z)) = B.ph (M.proj z)) {t : ℝ} (ht : 0 < t)
    (hm : ∀ j, ∀ x ∈ B.mid j, closedBall (B.chart j x) t ⊆ (B.chart j).target) (ε : ℝ)
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    B.regularised ρ t ε ct (M.proj (conjVec z)) = B.regularised ρ t ε ct (M.proj z) := by
  classical
  have hκκ := hS.1
  have hsym := hS.2.2
  unfold BoundedPshData.regularised PotentialCharts.glue
  congr 1
  let e : {j // M.proj z ∈ B.mid j} ≃ {j // M.proj (conjVec z) ∈ B.mid j} :=
    { toFun := fun j => ⟨κ j, (hsym j z hz).2.1.mpr j.2⟩
      invFun := fun j => ⟨κ j, by
        have := (hsym (κ j) z hz).2.1
        rw [hκκ] at this
        exact this.mp j.2⟩
      left_inv := fun j => Subtype.ext (hκκ j)
      right_inv := fun j => Subtype.ext (hκκ j) }
  have hterm : ∀ j : {j // M.proj z ∈ B.mid j},
      B.phReg ρ t (κ j) (M.proj (conjVec z)) + 4 * ε * ct (κ j) (M.proj (conjVec z)) =
      B.phReg ρ t j (M.proj z) + 4 * ε * ct j (M.proj z) := by
    intro j
    rw [hη j z hz]
    congr 1
    have hsrc : M.proj z ∈ (B.chart j).source := B.closure_mid j (subset_closure j.2)
    have hch := (hsym j z hz).2.2.2 hsrc
    unfold BoundedPshData.phReg BoundedPshData.smoothed
    rw [hch, hS.2.1 j]
    have hu : ∀ v ∈ closedBall ((B.chart j) (M.proj z)) t, B.u (κ j) (star v) = B.u j v := by
      intro v hv
      have hvt : v ∈ (B.chart j).target := hm j (M.proj z) j.2 hv
      obtain ⟨z', hz', hpz⟩ := M.surj ((B.chart j).symm v)
      have hsrc' : M.proj z' ∈ (B.chart j).source := by
        rw [hpz]
        exact (B.chart j).map_target hvt
      have hc2 := (hsym j z' hz').2.2.2 hsrc'
      have hsrcκ : M.proj (conjVec z') ∈ (B.chart (κ j)).source := (hsym j z' hz').1.mpr hsrc'
      have e1 : (B.chart j) (M.proj z') = v := by
        rw [hpz]
        exact (B.chart j).right_inv hvt
      have hsymm : (B.chart (κ j)).symm (star v) = M.proj (conjVec z') := by
        rw [← e1, ← hc2]
        exact (B.chart (κ j)).left_inv hsrcκ
      unfold BoundedPshData.u PotentialCharts.chartFun
      rw [hS.2.1 j v, hsymm, hph z' hz', hpz]
    rw [molli_star ρ hρ ht hu]
  convert (regMax_comp_equiv e ε (fun j : {j // M.proj (conjVec z) ∈ B.mid j} =>
    B.phReg ρ t j (M.proj (conjVec z)) + 4 * ε * ct j (M.proj (conjVec z)))).symm using 2
  funext j
  exact (hterm j).symm

end LevelTowerAlt.Conj

theorem LevelTowerAlt.tied_setting_symmetric_charts : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w) (κ : Equiv.Perm (Fin S'.B.N)), S'.IsTied → SymmCharts M S'.B.toPotentialCharts κ → (∀ v, S'.ρ.toFun (star v) = S'.ρ.toFun v) → (∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), S'.η (κ j) (M.proj (conjVec z)) = S'.η j (M.proj z)) → IsConjInvariantH S'.ref → (∀ z ∈ mcPts (mCoordIdeal D.y), S'.B.ph (M.proj (conjVec z)) = S'.B.ph (M.proj z)) → ConjU S' := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' κ hT hS hρ hη hrefc hph
  intro B p q _ _ _
  have hev := (GlobalTheory.T.regularized_weight_dominates_eventually K J II Ψ Ω W D Hd M w S' hT).and
    (LevelTowerAlt.Conj.eventually_margin S'.B.toPotentialCharts)
  obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  refine ⟨t₀, ht₀, fun t' ht' ht'le => ?_⟩
  obtain ⟨⟨-, -, hMU⟩, hm⟩ := hsub ⟨ht', ht'le⟩
  obtain ⟨hsm, hdeg, hlog⟩ := hMU B p q
  apply smoothRepConj_conj
  refine ⟨LevelTowerAlt.Conj.symmH (MUc Hd S' B p q t'), hdeg, LevelTowerAlt.Conj.symmH_smooth hsm,
    LevelTowerAlt.Conj.symmH_conj _, ?_⟩
  intro z hz
  have hcz : conjVec z ∈ mcPts (mCoordIdeal D.y) :=
    ⟨LevelTowerAlt.conjVec_ne hz.1, fun f hf => by rw [LevelTowerAlt.eval_conjVec, hz.2 f hf, map_zero]⟩
  have h1 : S'.ref.h (conjVec z) = S'.ref.h z := hrefc z
  have h2 : S'.bregWeight t' (M.proj (conjVec z)) = S'.bregWeight t' (M.proj z) :=
    LevelTowerAlt.Conj.regularised_conj S'.B κ hS S'.ρ hρ S'.η hη hph ht' hm (S'.e1 t') hz
  have h3 : ∀ r ∈ D.SB B, D.vertFactor r (conjVec z) = D.vertFactor r z := by
    intro r hr
    have hrS : r ∈ D.S := (Finset.mem_filter.1 hr).1
    obtain ⟨A, -, -, hAc, hAv⟩ := (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D r hrS).1
    rw [← hAv _ hz, ← hAv _ hcz]
    exact hAc z
  have h4 : D.A'.h (conjVec z) = D.A'.h z := D.A'_conj z
  have heq : (MUc Hd S' B p q t').h (conjVec z) = (MUc Hd S' B p q t').h z := by
    have p1 := (MUc Hd S' B p q t').pos z hz.1
    have p2 := (MUc Hd S' B p q t').pos (conjVec z) hcz.1
    apply Real.log_injOn_pos (Set.mem_Ioi.2 p2) (Set.mem_Ioi.2 p1)
    rw [hlog _ hcz, hlog _ hz, h1, h2, Finset.sum_congr rfl (fun r hr => by rw [h3 r hr]), h4]
  show ((MUc Hd S' B p q t').h z + (MUc Hd S' B p q t').h (conjVec z)) / 2 = _
  rw [heq, add_self_div_two]
  exact smoothRepConj_h _ hz
