import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

def gbPsi (e : Fin (D + 1) → Ix κ) : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ) :=
  LinearMap.pi fun k => LinearMap.proj (fun _ => (e k).2)

theorem gb_segre_apply (z : Ix κ → ℂ) (i : (k : Unit) → GlobalTheory κ k) :
    segre (ι := GlobalTheory κ) z i = z ⟨(), i ()⟩ := by
  simp only [segre, Fintype.prod_unique]

theorem gbPsi_segre (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    gbPsi e (segre (ι := GlobalTheory κ) z) = fun k => z (e k) := by
  funext k
  simp only [gbPsi, LinearMap.pi_apply, LinearMap.proj_apply]
  rw [gb_segre_apply]

theorem gb_segre_injective : Function.Injective (segre (ι := GlobalTheory κ)) := by
  intro z z' h
  funext p
  have := congrFun h (fun _ => p.2)
  rw [gb_segre_apply, gb_segre_apply] at this
  exact this

theorem gb_mcPts_eq (P : Ideal (MRing (GlobalTheory κ))) : mcPts P = pts P := by
  ext z
  simp only [mcPts, pts, conePts, Set.mem_setOf_eq]
  refine and_congr_left' ⟨fun h h0 => ?_, fun h k => ?_⟩
  · obtain ⟨i, hi⟩ := h ()
    exact hi (congrFun h0 _)
  · by_contra hne
    push_neg at hne
    exact h (funext fun p => hne p.2)

theorem gb_fibre_eq (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (y : Fin D → ℂ) :
    fibre (coordIdeal ℤ x) (gbPsi e) y = segre (ι := GlobalTheory κ) '' prFib x e (Fin.cons 1 y) := by
  ext w
  simp only [fibre, Set.mem_setOf_eq, Set.mem_image, prFib, gb_mcPts_eq]
  constructor
  · rintro ⟨z, hz, rfl, hΨ⟩
    rw [gbPsi_segre] at hΨ
    exact ⟨z, ⟨hz, fun k => congrFun hΨ k⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hk⟩, rfl⟩
    refine ⟨z, hz, rfl, ?_⟩
    rw [gbPsi_segre]
    funext k
    exact hk k

theorem gb_prFib_smul (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (w : Fin (D + 1) → ℂ) {c : ℂ}
    (hc : c ≠ 0) : prFib x e (c • w) = (fun z => c • z) '' prFib x e w := by
  ext z
  constructor
  · rintro ⟨hz, hk⟩
    refine ⟨c⁻¹ • z, ⟨smul_mem_pts_coord x hz (inv_ne_zero hc), fun k => ?_⟩, ?_⟩
    · simp [hk k, hc]
    · simp [smul_smul, hc]
  · rintro ⟨z', ⟨hz', hk⟩, rfl⟩
    exact ⟨smul_mem_pts_coord x hz' hc, fun k => by simp [hk k]⟩

theorem gb_sum_cons (y : Fin D → ℂ) :
    ∑ k, ‖(Fin.cons 1 y : Fin (D + 1) → ℂ) k‖ ^ 2 = 1 + ∑ i, ‖y i‖ ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp

theorem gb_sheetDensity {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {y : Fin D → ℂ} {w : ((k : Unit) → GlobalTheory κ k) → ℂ}
    (h : ∃ γ, IsSheet (coordIdeal ℤ x) (gbPsi e) y w γ) :
    sheetDensity (coordIdeal ℤ x) (gbPsi e) (purePot m D) (fun _ => 1) y w =
      maDensity (fun _ : Fin D => gbPot) y := by
  have hs := h.choose_spec
  unfold sheetDensity
  rw [dif_pos h]
  simp only [one_mul]
  apply maDensity_congr_of_eventuallyEq
  intro j
  filter_upwards [hs.2] with y' hy'
  obtain ⟨-, hmem, hΨ⟩ := hy'
  rw [gb_mcPts_eq] at hmem
  rw [gbPsi_segre] at hΨ
  simp only [purePot, gbPot]
  rw [hFS _ hmem, ← gb_sum_cons y']
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← congrFun hΨ k]

def gbConsL (D : ℕ) : (Fin D → ℂ) →L[ℂ] (Fin (D + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.cons 0 y
      map_add' := fun a b => by ext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp
      map_smul' := fun c a => by ext k; refine Fin.cases ?_ (fun i => ?_) k <;> simp }

theorem gb_scaledCons_eq (c : ℂ) (y : Fin D → ℂ) :
    c • (Fin.cons 1 y : Fin (D + 1) → ℂ) = c • (Fin.cons 1 0 : Fin (D + 1) → ℂ) + (c • gbConsL D) y := by
  ext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp [gbConsL]

theorem gb_analytic_scaledCons (c : ℂ) :
    AnalyticOnNhd ℂ (fun y : Fin D → ℂ => c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) Set.univ := by
  have h : (fun y : Fin D → ℂ => c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) =
      fun y => c • (Fin.cons 1 0 : Fin (D + 1) → ℂ) + (c • gbConsL D) y := funext (gb_scaledCons_eq c)
  rw [h]
  exact analyticOnNhd_const.add ((c • gbConsL D).analyticOnNhd _)

theorem gb_exists_scale {Δ : MvPolynomial (Fin (D + 1)) ℂ} (hΔ : Δ ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ y₀ : Fin D → ℂ, eval (c • (Fin.cons 1 y₀ : Fin (D + 1) → ℂ)) Δ ≠ 0 := by
  have h1 : Δ * X 0 ≠ 0 := mul_ne_zero hΔ (X_ne_zero _)
  obtain ⟨w, hw⟩ : ∃ w, eval w (Δ * X 0) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h1 (MvPolynomial.funext (fun w => by simpa using hne w))
  rw [eval_mul, eval_X] at hw
  have hw0 : w 0 ≠ 0 := right_ne_zero_of_mul hw
  refine ⟨w 0, hw0, fun i => w i.succ / w 0, ?_⟩
  have hw' : w 0 • (Fin.cons 1 (fun i => w i.succ / w 0) : Fin (D + 1) → ℂ) = w := by
    ext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp
    · first
      | (simp [hw0]; done)
      | (simp; field_simp)
  rw [hw']
  exact left_ne_zero_of_mul hw

theorem gb_ae_good {c : ℂ} {Δ : MvPolynomial (Fin (D + 1)) ℂ} {y₀ : Fin D → ℂ}
    (h₀ : eval (c • (Fin.cons 1 y₀ : Fin (D + 1) → ℂ)) Δ ≠ 0) :
    ∀ᵐ y : Fin D → ℂ, eval (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) Δ ≠ 0 := by
  have hpoly : ∀ p : MvPolynomial (Fin (D + 1)) ℂ, AnalyticOnNhd ℂ (fun w => eval w p) Set.univ := by
    intro p
    induction p using MvPolynomial.induction_on
    next a =>
      simp only [eval_C]
      exact analyticOnNhd_const
    next p q hp hq =>
      simp only [map_add]
      exact hp.add hq
    next p i hp =>
      simp only [map_mul, eval_X]
      exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (D + 1) => ℂ) i).analyticOnNhd _)
  have hf : AnalyticOnNhd ℂ ((fun w => eval w Δ) ∘ fun y : Fin D → ℂ => c • (Fin.cons 1 y : Fin (D + 1) → ℂ))
      Set.univ := (hpoly Δ).comp (gb_analytic_scaledCons c) (Set.mapsTo_univ _ _)
  have h := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ hf
    ⟨y₀, Set.mem_univ _, h₀⟩
  rw [ae_iff]
  simpa using h

theorem gb_fibre_good {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {Δ : MvPolynomial (Fin (D + 1)) ℂ}
    (hΔ : IsDiscr x e Δ) {c : ℂ} (hc : c ≠ 0) {y : Fin D → ℂ}
    (hy : eval (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) Δ ≠ 0) :
    (fibre (coordIdeal ℤ x) (gbPsi e) y).Finite ∧
      (fibre (coordIdeal ℤ x) (gbPsi e) y).ncard = projDeg x e ∧
      ∀ w ∈ fibre (coordIdeal ℤ x) (gbPsi e) y, ∃ γ, IsSheet (coordIdeal ℤ x) (gbPsi e) y w γ := by
  obtain ⟨hfin, hcard, hsec, -⟩ := hΔ.2 _ hy
  have hS : prFib x e (Fin.cons 1 y) =
      (fun z => c⁻¹ • z) '' prFib x e (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) := by
    rw [← gb_prFib_smul x e (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) (inv_ne_zero hc), smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hinj : Function.Injective (fun z : Ix κ → ℂ => segre (ι := GlobalTheory κ) (c⁻¹ • z)) :=
    fun a b hab => smul_right_injective _ (inv_ne_zero hc) (gb_segre_injective hab)
  have hF : fibre (coordIdeal ℤ x) (gbPsi e) y =
      (fun z => segre (ι := GlobalTheory κ) (c⁻¹ • z)) '' prFib x e (c • (Fin.cons 1 y : Fin (D + 1) → ℂ)) := by
    rw [gb_fibre_eq, hS, Set.image_image]
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]
    exact hfin.image _
  · rw [hF, Set.ncard_image_of_injective _ hinj, hcard]
  · intro w hw
    rw [hF] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    obtain ⟨U, Γ, hU, hWU, hΓ, hΓW, hΓU⟩ := hsec z hz
    refine ⟨fun y' => c⁻¹ • Γ (c • (Fin.cons 1 y' : Fin (D + 1) → ℂ)), ?_, ?_⟩
    · simp only [hΓW]
    · have hcont : Continuous (fun y' : Fin D → ℂ => c • (Fin.cons 1 y' : Fin (D + 1) → ℂ)) :=
        continuousOn_univ.1 (gb_analytic_scaledCons c).continuousOn
      filter_upwards [hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hWU)] with y' hy'
      have hmem := hΓU _ hy'
      refine ⟨?_, ?_, ?_⟩
      · exact ((hΓ.differentiableAt (hU.mem_nhds hy')).comp y'
          ((gb_analytic_scaledCons c) y' (Set.mem_univ _)).differentiableAt).const_smul c⁻¹
      · rw [gb_mcPts_eq]
        exact smul_mem_pts_coord x hmem.1 (inv_ne_zero hc)
      · rw [gbPsi_segre]
        funext k
        simp [hmem.2 k, hc]

theorem gb_integrand_ae {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hfr : IsProjFrame x e) (hFS : IsPullFS x e m) :
    ∀ᵐ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (coordIdeal ℤ x) (gbPsi e) y,
        sheetDensity (coordIdeal ℤ x) (gbPsi e) (purePot m D) (fun _ => 1) y w =
      (projDeg x e : ℝ) * maDensity (fun _ : Fin D => gbPot) y := by
  obtain ⟨Δ, hΔ⟩ := exists_isDiscr hfr
  obtain ⟨c, hc, y₀, h₀⟩ := gb_exists_scale hΔ.1
  filter_upwards [gb_ae_good h₀] with y hy
  obtain ⟨hfin, hcard, hsh⟩ := gb_fibre_good hΔ hc hy
  rw [finsum_mem_congr rfl (fun w hw => gb_sheetDensity hFS (hsh w hw)),
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hfin, hcard]

theorem gb_ptsIntegralAt {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hfr : IsProjFrame x e) (hFS : IsPullFS x e m) :
    ptsIntegralAt (coordIdeal ℤ x) (gbPsi e) (purePot m D) (fun _ => 1) = projDeg x e := by
  unfold ptsIntegralAt
  rw [integral_congr_ae (gb_integrand_ae hfr hFS)]
  first
  | rw [integral_const_mul, integral_maDensity_gbPot, mul_one]
  | rw [integral_mul_left, integral_maDensity_gbPot, mul_one]

theorem gb_isGoodProj {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) :
    IsGoodProj (coordIdeal ℤ x) (gbPsi e) := by
  intro z hz
  rw [gbPsi_segre]
  rw [gb_mcPts_eq] at hz
  obtain ⟨k, hk⟩ := exists_proj_ne_zero hfr hz
  intro h0
  exact hk (congrFun h0 k)

def gbOne : HermLine (GlobalTheory κ) := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)

theorem gb_logNorm_one : logNorm (gbOne (κ := κ)) 1 = fun _ => (1 : ℝ) := by
  funext z
  simp [logNorm, gbOne, HermLine.ofWeight]

theorem gb_ptsIntegral (hInd : PtsIndepStatement) {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)}
    (hL : IsSmoothHerm (HermLine.ofCone m))
    (harith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1))
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m) :
    ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (purePot m D) (fun _ => 1) = projDeg x e := by
  have hg : IsGoodProj (coordIdeal ℤ x) (gbPsi e) := gb_isGoodProj hfr
  have hex : ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (coordIdeal ℤ x) Ψ :=
    ⟨gbPsi e, hg⟩
  have hSm : IsSmoothHerm (gbOne (κ := κ)) := contDiffOn_const
  have hSec : IsSectionOn (coordIdeal ℤ x) (gbOne (κ := κ)) 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro mm hm k
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    · intro h
      exact RingHom.ker_ne_top _ ((Ideal.eq_top_iff_one _).2 h)
  have key := hInd Unit (GlobalTheory κ) (coordIdeal ℤ x) D hex.choose (gbPsi e) (fun _ => HermLine.ofCone m)
    (gbOne (κ := κ)) 1 harith hex.choose_spec hg (fun _ => hL) hSm hSec
  rw [gb_logNorm_one] at key
  unfold ptsIntegral
  rw [dif_pos hex]
  exact key.trans (gb_ptsIntegralAt hfr hFS)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
