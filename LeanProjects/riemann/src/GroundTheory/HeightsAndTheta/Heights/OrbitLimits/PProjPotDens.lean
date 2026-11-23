import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsProjPotDens
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegular
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjPotDensLevi
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

namespace ProjPotDens

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X} {BV : FinHolAtlas n V}

theorem affLift_analyticAt (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    AnalyticAt ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ∀ k, R.lift x.1 ((BV.chart j).symm u).1 ⟨k, p k⟩ ≠ 0 := by
  have hG := (ProjRegular.lift_analyticAt hB x hx).1
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hc : ∀ q, AnalyticAt ℂ (fun u => R.lift x.1 ((BV.chart j).symm u).1 q) (BV.chart j x) :=
    fun q => analyticAt_pi_iff.1 hG q
  have hp' : ∀ k, R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ ≠ 0 := by
    rw [hsx]; exact hp
  refine ⟨?_, eventually_all.2 fun k => (hc ⟨k, p k⟩).continuousAt.eventually_ne (hp' k)⟩
  show AnalyticAt ℂ (fun u q => R.lift x.1 ((BV.chart j).symm u).1 q /
    R.lift x.1 ((BV.chart j).symm u).1 ⟨q.1, p q.1⟩) (BV.chart j x)
  exact AnalyticAt.pi fun q => (hc q).div (hc ⟨q.1, p q.1⟩) (hp' q.1)

theorem fderiv_affLift_self (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) (w : Fin n → ℂ) (k : K) :
    fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w
      ⟨k, p k⟩ = 0 := by
  obtain ⟨hτa, hev⟩ := affLift_analyticAt hB x hx p hp
  have h1 := hasFDerivAt_pi'.1 hτa.differentiableAt.hasFDerivAt ⟨k, p k⟩
  have h2 : HasFDerivAt (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1) ⟨k, p k⟩)
      (0 : (Fin n → ℂ) →L[ℂ] ℂ) (BV.chart j x) :=
    (hasFDerivAt_const (1 : ℂ) _).congr_of_eventuallyEq (by
      filter_upwards [hev] with u hu
      exact div_self (hu k))
  have := congrArg (fun L => L w) (h1.unique h2)
  simpa using this

theorem injective_fderiv_affLift (hB : HoloMap BV R.A Subtype.val) (x : V) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) {j j' : Fin BV.n} (hj : x ∈ (BV.chart j).source)
    (hj' : x ∈ (BV.chart j').source)
    (hr : Module.finrank ℂ (LinearMap.range (fderiv ℂ
      (fun u => affCoord p (R.lift x.1 ((BV.chart j').symm u).1)) (BV.chart j' x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))) = n) :
    Function.Injective (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1))
      (BV.chart j x)) := by
  set F : Fin BV.n → (Fin n → ℂ) → ((Σ k, ι k) → ℂ) :=
    fun i u => affCoord p (R.lift x.1 ((BV.chart i).symm u).1) with hF
  have hinj' : Function.Injective (fderiv ℂ (F j') (BV.chart j' x)) := by
    have hk := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℂ (F j') (BV.chart j' x) : (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ))
    rw [hr, Module.finrank_fin_fun] at hk
    have h0 : LinearMap.ker (fderiv ℂ (F j') (BV.chart j' x) :
        (Fin n → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ)) = ⊥ :=
      Submodule.finrank_eq_zero.1 (by omega)
    exact LinearMap.ker_eq_bot.1 h0
  have hu0 : BV.chart j x ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hv0 : BV.chart j' x ∈ (BV.chart j').target := (BV.chart j').map_source hj'
  have hsj : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hj
  have hsk : (BV.chart j').symm (BV.chart j' x) = x := (BV.chart j').left_inv hj'
  have hτu : (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x) = BV.chart j' x := by simp [hsj]
  have hτ : AnalyticAt ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x) :=
    BV.holo j j' _ ⟨hu0, by
      show (BV.chart j).symm (BV.chart j x) ∈ (BV.chart j').source; rw [hsj]; exact hj'⟩
  have hσ : AnalyticAt ℂ (BV.chart j ∘ (BV.chart j').symm)
      ((BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hτu]
    exact BV.holo j' j _ ⟨hv0, by
      show (BV.chart j').symm (BV.chart j' x) ∈ (BV.chart j).source; rw [hsk]; exact hj⟩
  have hev : ∀ᶠ u in 𝓝 (BV.chart j x), (BV.chart j).symm u ∈ (BV.chart j').source :=
    ((BV.chart j).continuousAt_symm hu0).preimage_mem_nhds (by
      show (BV.chart j').source ∈ 𝓝 ((BV.chart j).symm (BV.chart j x))
      rw [hsj]; exact (BV.chart j').open_source.mem_nhds hj')
  have hid : (BV.chart j ∘ (BV.chart j').symm) ∘ (BV.chart j' ∘ (BV.chart j).symm)
      =ᶠ[𝓝 (BV.chart j x)] id := by
    filter_upwards [hev, (BV.chart j).open_target.mem_nhds hu0] with u hu hut
    simp [(BV.chart j').left_inv hu, (BV.chart j).right_inv hut]
  have hq : F j =ᶠ[𝓝 (BV.chart j x)] F j' ∘ (BV.chart j' ∘ (BV.chart j).symm) := by
    filter_upwards [hev] with u hu
    simp [hF, (BV.chart j').left_inv hu]
  have hFa : AnalyticAt ℂ (F j') ((BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hτu]; exact (affLift_analyticAt hB x hj' p hp).1
  have hD : fderiv ℂ (F j) (BV.chart j x) = (fderiv ℂ (F j') (BV.chart j' x)).comp
      (fderiv ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    rw [hq.fderiv_eq, fderiv_comp _ hFa.differentiableAt hτ.differentiableAt, hτu]
  have hT : Function.LeftInverse (fderiv ℂ (BV.chart j ∘ (BV.chart j').symm) (BV.chart j' x))
      (fderiv ℂ (BV.chart j' ∘ (BV.chart j).symm) (BV.chart j x)) := by
    intro w
    have h1 := hid.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_comp _ hσ.differentiableAt hτ.differentiableAt, fderiv_id, hτu] at h1
    simpa using congrArg (fun L => L w) h1
  show Function.Injective (fderiv ℂ (F j) (BV.chart j x))
  rw [hD]
  exact hinj'.comp hT.injective

theorem hessC_chartPot (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    ReciprocityTheory.AnForm.hessC (fun u => (multiprojPot R V).φ x ((BV.chart j).symm u)) (BV.chart j x) =
      ReciprocityTheory.AnForm.hessC
        (fsMultiPot ∘ fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) := by
  obtain ⟨hτa, hev⟩ := affLift_analyticAt hB x hx p hp
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  set G : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun u => R.lift x.1 ((BV.chart j).symm u).1 with hG
  set τ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun u => affCoord p (G u) with hτ
  have hGa : ∀ q, AnalyticAt ℂ (fun u => G u q) (BV.chart j x) :=
    fun q => analyticAt_pi_iff.1 (ProjRegular.lift_analyticAt hB x hx).1 q
  have hp' : ∀ k, G (BV.chart j x) ⟨k, p k⟩ ≠ 0 := by
    intro k; simp only [hG, hsx]; exact hp k
  have hτ1 : ∀ u, (∀ k, G u ⟨k, p k⟩ ≠ 0) → ∀ k, τ u ⟨k, p k⟩ = 1 :=
    fun u hu k => div_self (hu k)
  let g : (Fin n → ℂ) → ℂ := fun u => ∏ k, G u ⟨k, p k⟩ ^ 2
  have hga : AnalyticAt ℂ g (BV.chart j x) :=
    Finset.univ.analyticAt_fun_prod fun k _ => (hGa ⟨k, p k⟩).pow 2
  have hg0 : g (BV.chart j x) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero 2 (hp' k)
  have hC : ContDiffAt ℝ 2 fsMultiPot (τ (BV.chart j x)) :=
    (levi_fsMultiPot p (fun k => by rw [hτ1 _ hp' k]; exact one_ne_zero) 0).1
  have hgerm : (fun u => (multiprojPot R V).φ x ((BV.chart j).symm u)) =ᶠ[𝓝 (BV.chart j x)]
      fun u => (fsMultiPot ∘ τ) u + Real.log ‖g u‖ := by
    filter_upwards [hev] with u hu
    show ∑ k, Real.log (∑ i, ‖G u ⟨k, i⟩‖ ^ 2) =
      ∑ k, Real.log (∑ i, ‖τ u ⟨k, i⟩‖ ^ 2) + Real.log ‖∏ k, G u ⟨k, p k⟩ ^ 2‖
    have hs : ∀ k, ∑ i, ‖G u ⟨k, i⟩‖ ^ 2 = ‖G u ⟨k, p k⟩‖ ^ 2 * ∑ i, ‖τ u ⟨k, i⟩‖ ^ 2 := by
      intro k
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hn : ‖G u ⟨k, p k⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hu k)
      simp only [hτ, affCoord, norm_div, div_pow]
      field_simp
    have hpos : ∀ k, 0 < ∑ i, ‖τ u ⟨k, i⟩‖ ^ 2 := fun k =>
      lt_of_lt_of_le (by rw [hτ1 u hu k]; norm_num)
        (Finset.single_le_sum (f := fun i => ‖τ u ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ (p k)))
    have hne : ∀ k ∈ (Finset.univ : Finset K), ‖G u ⟨k, p k⟩ ^ 2‖ ≠ 0 := fun k _ => by
      rw [norm_pow]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hu k))
    rw [norm_prod, Real.log_prod hne, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs k, norm_pow, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu k))) (hpos k).ne',
      add_comm]
  rw [hessCGerm _ _ _ hgerm]
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g _
    (hC.comp _ (hτa.contDiffAt.restrict_scalars ℝ)) hga hg0

end ProjPotDens

theorem ProjPotDens.proof : ProjPotDens.Statement := by
  intro K _ ι _ P J n R V BV hB j y hy
  obtain ⟨x, hx, rfl⟩ : ∃ x, x ∈ (BV.chart j).source ∧ BV.chart j x = y :=
    ⟨_, (BV.chart j).map_target hy, (BV.chart j).right_inv hy⟩
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx

  have hdens : ∀ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) →
      locDens BV (fun _ => multiprojPot R V) j (BV.chart j x) =
        ReciprocityTheory.AnForm.maDens (fun _ => ProjPotDens.fsMultiPot ∘
          fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) := by
    intro p hp
    unfold locDens
    rw [hsx]
    exact maDens_congr_hessC _ _ _ fun _ => ProjPotDens.hessC_chartPot hB x hx p hp
  have hlevi : ∀ p : (k : K) → ι k, (∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) →
      ContDiffAt ℝ 2 (ProjPotDens.fsMultiPot ∘
          fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) ∧
        ∀ w, 0 ≤ ReciprocityTheory.AnForm.levi (ProjPotDens.fsMultiPot ∘
            fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w ∧
          (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w
              ≠ 0 →
            0 < ReciprocityTheory.AnForm.levi (ProjPotDens.fsMultiPot ∘
              fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w) := by
    intro p hp
    have hτa := (ProjPotDens.affLift_analyticAt hB x hx p hp).1
    have hτ1 : ∀ k, affCoord p (R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1) ⟨k, p k⟩ ≠ 0 := by
      intro k
      show R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ /
        R.lift x.1 ((BV.chart j).symm (BV.chart j x)).1 ⟨k, p k⟩ ≠ 0
      rw [hsx, div_self (hp k)]
      exact one_ne_zero
    have hC := (ProjPotDens.levi_fsMultiPot p hτ1 0).1
    refine ⟨hC.comp (f := fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x)
      (hτa.contDiffAt.restrict_scalars ℝ), fun w => ?_⟩
    rw [ReciprocityTheory.AnForm.levi_comp w hτa hC]
    obtain ⟨_, h1, h2⟩ := ProjPotDens.levi_fsMultiPot p hτ1
      (fderiv ℂ (fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) w)
    exact ⟨h1, h2 fun k => ProjPotDens.fderiv_affLift_self hB x hx p hp w k⟩
  refine ⟨?_, fun hfull => ?_⟩
  · obtain ⟨p, hp⟩ : ∃ p : (k : K) → ι k, ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0 :=
      ⟨fun k => Classical.choose ((R.mem x.1 x.1 (R.mem_U x.1)).1 k),
        fun k => Classical.choose_spec ((R.mem x.1 x.1 (R.mem_U x.1)).1 k)⟩
    rw [hdens p hp]
    obtain ⟨hC, hl⟩ := hlevi p hp
    exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ =>
      hessC_posSemidef _ _ hC fun w => (hl w).1
  · rw [hsx] at hfull
    obtain ⟨p, hp, j', hj', hr⟩ := hfull
    have hinj := ProjPotDens.injective_fderiv_affLift hB x p hp hx hj' hr
    rw [hdens p hp]
    obtain ⟨hC, hl⟩ := hlevi p hp
    unfold ReciprocityTheory.AnForm.maDens
    refine mul_pos (mul_pos (Nat.cast_pos.2 (Nat.factorial_pos _))
      (pow_pos (div_pos two_pos Real.pi_pos) _))
      (ReciprocityTheory.AnForm.A.mdisc_pos_of_posDef _ fun _ => hessC_posDef _ _ hC fun w hw =>
        (hl w).2 fun h0 => hw (hinj (h0.trans (map_zero _).symm))).2

end GroundTheory.Heights₂.Heights.Targets
