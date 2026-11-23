import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLocalOrbitChart
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PLevelSetLocalInj
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_injective_linear {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    (h : Module.finrank ℂ W ≤ n) : ∃ j : W →ₗ[ℂ] (Fin n → ℂ), Function.Injective j := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearEquiv.ofFinrankEq _ _ (by simp)
  let s : Fin (Module.finrank ℂ W) → Fin n := Fin.castLE h
  have hs : Function.Injective s := Fin.castLE_injective h
  refine ⟨(Function.ExtendByZero.linearMap ℂ s).comp e.toLinearMap, fun a b hab => e.injective ?_⟩
  funext i
  have := congrFun hab (s i)
  change Function.extend s (e a) 0 (s i) = Function.extend s (e b) 0 (s i) at this
  rwa [hs.extend_apply, hs.extend_apply] at this

theorem exists_injOn_of_strict {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {Φ : E → F} {L : E →L[ℂ] F} {w : E}
    (hΦ : HasStrictFDerivAt Φ L w) (hL : Function.Injective L) :
    ∃ B : Set E, IsOpen B ∧ w ∈ B ∧ Set.InjOn Φ B := by
  obtain ⟨N, hN, hanti⟩ := (L : E →ₗ[ℂ] F).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hL)
  have hc : (0 : NNReal) < (2 * N)⁻¹ := by positivity
  obtain ⟨s, hs, hap⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * N)⁻¹) (Or.inr hc)
  obtain ⟨B, hBs, hB, hwB⟩ := mem_nhds_iff.1 hs
  refine ⟨B, hB, hwB, fun u hu v hv huv => ?_⟩
  have h1 := hap u (hBs hu) v (hBs hv)
  rw [huv, sub_self, zero_sub, norm_neg] at h1
  have h2 : ‖u - v‖ ≤ N * ‖L (u - v)‖ := by
    have := hanti.le_mul_dist (u - v) 0
    simpa [dist_eq_norm] using this
  by_contra hne
  have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ‖u - v‖ ≤ N * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 hN'.le)
  have h4 : (N : ℝ) * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) = ‖u - v‖ / 2 := by
    push_cast
    field_simp
  rw [h4] at h3
  linarith

theorem exists_linear_separation {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (n : ℕ)
    (hcard : Fintype.card σ ≤ Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) + n) :
    ∃ (π : (σ → ℂ) →L[ℂ] (Fin n → ℂ)) (B : Set (σ → ℂ)), IsOpen B ∧ w ∈ B ∧
      ∀ u ∈ B, ∀ v ∈ B, (∀ h ∈ I, eval u h = 0) → (∀ h ∈ I, eval v h = 0) → π u = π v → u = v := by
  classical
  set S : Set (σ → ℂ) := (fun h : MvPolynomial σ ℂ => fun j => eval w (pderiv j h)) '' (I : Set _) with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hbfin : b.Finite := hli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hex : ∀ t : b, ∃ f ∈ I, (fun j => eval w (pderiv j f)) = (t : σ → ℂ) := fun t => by
    obtain ⟨f, hf, h⟩ := hbS t.2
    exact ⟨f, hf, h⟩
  choose F hFI hFg using hex
  let M : Matrix b σ ℂ := fun t q => (t : σ → ℂ) q
  have hrank : M.rank = Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : Set.range M.row = b := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact t.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [this, hspan]
    rfl
  let W : Submodule ℂ (σ → ℂ) := LinearMap.ker M.mulVecLin
  have hW : Module.finrank ℂ W ≤ n := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h' : Module.finrank ℂ (LinearMap.range M.mulVecLin) = M.rank := rfl
    simp only [Module.finrank_fintype_fun_eq_card] at h
    show Module.finrank ℂ (LinearMap.ker M.mulVecLin) ≤ n
    omega
  obtain ⟨j, hj⟩ := exists_injective_linear hW
  obtain ⟨l, hl⟩ := W.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype W)
  let π : (σ → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (j.comp l)
  let Φ : (σ → ℂ) → (b → ℂ) × (Fin n → ℂ) := fun x => (fun t => eval x (F t), π x)
  let L0 : (σ → ℂ) →L[ℂ] (b → ℂ) := ContinuousLinearMap.pi fun t => polyDiff (F t) w
  have hd : HasStrictFDerivAt Φ (L0.prod π) w :=
    (hasStrictFDerivAt_pi.2 fun t => hasStrictFDerivAt_eval_poly (F t) w).prodMk π.hasStrictFDerivAt
  have hinj : Function.Injective (L0.prod π) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : L0 v = 0 := congrArg Prod.fst hv
    have h2 : π v = 0 := congrArg Prod.snd hv
    have hvW : v ∈ W := by
      show M.mulVecLin v = 0
      funext t
      have h3 := congrFun h1 t
      have h4 : polyDiff (F t) w v = 0 := h3
      rw [polyDiff_apply] at h4
      have h5 : ∀ q, eval w (pderiv q (F t)) = (t : σ → ℂ) q := fun q => congrFun (hFg t) q
      simp only [h5] at h4
      show ∑ q, (t : σ → ℂ) q * v q = 0
      exact h4
    have h6 : j (l v) = 0 := h2
    have h7 : l v = 0 := hj (by rw [h6, map_zero])
    have h8 : l (W.subtype ⟨v, hvW⟩) = ⟨v, hvW⟩ := LinearMap.congr_fun hl _
    have h9 : (⟨v, hvW⟩ : W) = 0 := by rw [← h8]; exact h7
    exact congrArg Subtype.val h9
  obtain ⟨B, hB, hwB, hBinj⟩ := exists_injOn_of_strict hd hinj
  refine ⟨π, B, hB, hwB, fun u hu v hv hIu hIv huv => hBinj hu hv ?_⟩
  refine Prod.ext (funext fun t => ?_) huv
  show eval u (F t) = eval v (F t)
  rw [hIu _ (hFI t), hIv _ (hFI t)]

theorem localOrbitChart : LocalOrbitChart.Statement := by
  intro K _ ι _ Ω _ inst y n hP hsm z₀ hz₀
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z₀ hz₀.1
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz₀.2 _ hX
    rw [map_X, eval_X] at h1
    exact hp k h1
  have hzero : ∀ z ∈ mcPts (mCoordIdeal y), (∀ k, z ⟨k, p k⟩ ≠ 0) →
      ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p,
        eval (ReciprocityTheory.AnForm.R.affCoord p z) h = 0 := fun z hz hzp =>
    (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p z hzp).1 ((mem_mcPts_iff_conePts_pC _ _).1 hz)
  have hrank := GlobalTheory.CompanionTheory.Ar.PB.SmoothMan.card_le_finrank_jacSpanAt K ι Ω y n hP hsm p hy
    (ReciprocityTheory.AnForm.R.affCoord p z₀) (hzero z₀ hz₀ hp)
  obtain ⟨π, B, hB, hwB, hsep⟩ := exists_linear_separation _ _ n hrank
  let D : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, z ⟨k, p k⟩ ≠ 0}
  have hDopen : IsOpen D := by
    have : D = ⋂ k, {z | z ⟨k, p k⟩ ≠ 0} := by ext z; simp [D]
    rw [this]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have han : ∀ z ∈ D, AnalyticAt ℂ (ReciprocityTheory.AnForm.R.affCoord p) z := by
    intro z hz
    refine analyticAt_pi_iff.2 fun q => ?_
    have hc : ∀ r : Σ k, ι k, AnalyticAt ℂ (fun v : (Σ k, ι k) → ℂ => v r) z := fun r =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) r).analyticAt z
    exact (hc q).div (hc ⟨q.1, p q.1⟩) (hz q.1)
  have hcont : ContinuousOn (ReciprocityTheory.AnForm.R.affCoord p) D := fun z hz =>
    (han z hz).continuousAt.continuousWithinAt
  refine ⟨D ∩ ReciprocityTheory.AnForm.R.affCoord p ⁻¹' B, hcont.isOpen_inter_preimage hDopen hB, ⟨hp, hwB⟩,
    fun z => π (ReciprocityTheory.AnForm.R.affCoord p z), ?_, ?_, ?_⟩
  · intro z hz
    exact (π.analyticAt _).comp (han z hz.1)
  · intro z hz c hc
    have hA : ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) = ReciprocityTheory.AnForm.R.affCoord p z :=
      ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit p ⟨c, hc, rfl⟩
    refine ⟨⟨fun k => mul_ne_zero (hc k) (hz.1 k), ?_⟩, ?_⟩
    · show ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) ∈ B
      rw [hA]
      exact hz.2
    · show π _ = π _
      rw [hA]
  · rintro z ⟨hzN, hzX⟩ z' ⟨hzN', hzX'⟩ hκ
    have hA := hsep _ hzN.2 _ hzN'.2 (hzero z hzX hzN.1) (hzero z' hzX' hzN'.1) hκ
    refine ⟨fun k => z' ⟨k, p k⟩ / z ⟨k, p k⟩, fun k => div_ne_zero (hzN'.1 k) (hzN.1 k), ?_⟩
    funext q
    have h1 : z q / z ⟨q.1, p q.1⟩ = z' q / z' ⟨q.1, p q.1⟩ := congrFun hA q
    have h2 := hzN.1 q.1
    have h3 := hzN'.1 q.1
    show z' q = z' ⟨q.1, p q.1⟩ / z ⟨q.1, p q.1⟩ * z q
    rw [div_mul_eq_mul_div, eq_div_iff h2]
    rw [div_eq_div_iff h2 h3] at h1
    linear_combination -h1

end GlobalTheory.CompanionTheory.Ar.Giv
