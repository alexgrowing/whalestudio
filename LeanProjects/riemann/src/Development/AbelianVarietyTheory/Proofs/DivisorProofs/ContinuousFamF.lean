import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PBConjTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousDen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDiagReNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StExpDeriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeSignFormDiagEqSignedSumCol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StConstHolds
import Mathlib

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc3
open scoped ContDiff

namespace GlobalTheory.PsCo.Pcd

variable {n : ℕ}

theorem iter_zero {G : ℝ → ℝ} (h1 : ∀ x, 1 ≤ x → G x = 0) {t : ℝ} (ht : 0 < t) (k : ℕ) {y : ℝ}
    (hy : 1 < t * y) : iteratedDeriv k (fun x => G (t * x)) y = 0 := by
  have hev : (fun x => G (t * x)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    have : ∀ᶠ x in 𝓝 y, 1 < t * x :=
      (continuous_const.mul continuous_id).continuousAt.eventually (lt_mem_nhds hy)
    filter_upwards [this] with x hx using h1 _ hx.le
  rw [hev.iteratedDeriv_eq k]
  simp [iteratedDeriv_const]

theorem iter_cont {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (t : ℝ) (k : ℕ) :
    Continuous (iteratedDeriv k fun x => G (t * x)) :=
  (hG.comp (contDiff_const.mul contDiff_id)).continuous_iteratedDeriv k (by exact_mod_cast le_top)

theorem norm_le_sqrt {ι : Type} [Fintype ι] (B : ι → ℂ) : ‖B‖ ≤ Real.sqrt (∑ x, ‖B x‖ ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun x => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun x => ‖B x‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)

theorem muK_univ (ε : Fin n → Bool) : muK ε Set.univ = 1 := by
  unfold Formalism.REAL.muK
  exact Measure.haarMeasure_self

theorem toM_mul (ε : Fin n → Bool) (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

theorem continuous_toM (ε : Fin n → Bool) : Continuous fun g : UJ ε => toM g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_ev (P : Poly n) : Continuous fun M : Mat n => ev M P := by
  unfold ev
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun i => ?_)
  rcases i with x | x
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; fun_prop

theorem continuous_rM (ε : Fin n → Bool) : Continuous fun M : Mat n => rM ε M := by
  unfold rM; fun_prop

theorem continuous_famF (ε : Fin n → Bool) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (p : ℕ → Poly n) (t : ℝ) :
    Continuous fun M : Mat n => famF ε G p t M := by
  unfold famF bas
  refine continuous_finset_sum _ fun k _ => ?_
  exact (Complex.continuous_ofReal.comp ((iter_cont hG t k).comp (continuous_rM ε))).mul (continuous_ev _)

theorem famF_eq_zero (ε : Fin n → Bool) {G : ℝ → ℝ} (h1 : ∀ x, 1 ≤ x → G x = 0) (p : ℕ → Poly n) {t : ℝ}
    (ht : 0 < t) {M : Mat n} (hM : 1 < t * rM ε M) : famF ε G p t M = 0 := by
  unfold famF bas
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [iter_zero h1 ht k hM]
  simp

theorem blkM_one (ε : Fin n → Bool) : blkM ε (1 : Mat n) = 0 := by
  funext x
  have : x.1.1 ≠ x.1.2 := fun h => by
    have h1 := x.2.1; have h2 := x.2.2; rw [h] at h1; rw [h1] at h2; exact Bool.noConfusion h2
  simp [blkM, Matrix.one_apply_ne this]

theorem blkM_diag (ε : Fin n → Bool) (d : Fin n → ℂ) : blkM ε (Matrix.diagonal d) = 0 := by
  funext x
  have : x.1.1 ≠ x.1.2 := fun h => by
    have h1 := x.2.1; have h2 := x.2.2; rw [h] at h1; rw [h1] at h2; exact Bool.noConfusion h2
  simp [blkM, Matrix.diagonal_apply_ne _ this]

theorem rM_eq_blk (ε : Fin n → Bool) (M : Mat n) : rM ε M = ∑ x, ‖blkM ε M x‖ ^ 2 := rfl

end GlobalTheory.PsCo.Pcd

end
end

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc3

namespace GlobalTheory.PsCo.Pcd

variable {n : ℕ}

theorem fam_cs (hR : StR) (ε : Fin n → Bool) {G : ℝ → ℝ} (hG : IsProfile (nMode ε) G) (p : ℕ → Poly n) {t : ℝ}
    (ht : 0 < t) (w : UJ ε → ℂ) (hw : Continuous w) :
    Continuous (fun g : UJ ε => famF ε G p t (toM g) * w g) ∧
      HasCompactSupport (fun g : UJ ε => famF ε G p t (toM g) * w g) := by
  refine ⟨((continuous_famF ε hG.1 p t).comp (continuous_toM ε)).mul hw, ?_⟩
  refine HasCompactSupport.intro ((hR n ε).2.2.2 (1 / t)) fun g hg => ?_
  have hg' : 1 < t * rM ε (toM g) := by
    simp only [Set.mem_setOf_eq, not_le] at hg
    rwa [div_lt_iff₀' ht] at hg
  simp [famF_eq_zero ε hG.2.1 p ht hg']

theorem lim1 (hEB : StEB) (hR : StR) (hL : StExpLow) (hD : StExpDeriv) (hF : StFamBlow)
    (ε : Fin n → Bool) (μ : Measure (UJ ε)) (J : (Mode ε → ℂ) → ℝ) (hJc : Continuous J)
    (hpol : ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = ∫ B, (J B : ℂ) * ∫ k : KG ε, f (k * eB ε B) ∂(muK ε))
    (G : ℝ → ℝ) (hG : IsProfile (nMode ε) G) (p : ℕ → Poly n) (w : UJ ε → ℂ) (hw : Continuous w) :
    Tendsto (fun t : ℝ => ∫ g, famF ε G p t (toM g) * w g ∂μ) atTop
      (𝓝 ((J 0 : ℂ) * ((∫ v : Mode ε → ℂ, iteratedDeriv (nMode ε) G (∑ x, ‖v x‖ ^ 2) : ℝ) : ℂ) *
        ∫ k, ev (toMK k) (p (nMode ε)) * w k ∂(muK ε))) := by
  obtain ⟨hcEB, hEB0, hEBm⟩ := hEB n ε
  let β : (Mode ε → ℂ) → (Mode ε → ℂ) := fun B => blkM ε (toM (eB ε B))
  have hβe : β = fun B => blkM ε (NormedSpace.exp (pB ε B)) := funext fun B => by
    simp only [β, (hEBm B).1]
  let ψ : ℕ → (Mode ε → ℂ) → ℂ := fun j B =>
    (J B : ℂ) * ∫ k : KG ε, ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B) ∂(muK ε)
  have hcont2 : ∀ j, Continuous (Function.uncurry fun (B : Mode ε → ℂ) (k : KG ε) =>
      ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B)) := fun j => by
    have hm : Continuous fun q : (Mode ε → ℂ) × KG ε => (q.2 : UJ ε) * eB ε q.1 :=
      (continuous_subtype_val.comp continuous_snd).mul (hcEB.comp continuous_fst)
    exact ((continuous_ev _).comp ((continuous_toM ε).comp hm)).mul (hw.comp hm)
  have hψc : ∀ j, Continuous (ψ j) := fun j => by
    refine (Complex.continuous_ofReal.comp hJc).mul ?_
    have := continuous_parametric_integral_of_continuous (μ := muK ε) (hcont2 j) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hβc : Continuous β := by
    show Continuous fun B => blkM ε (toM (eB ε B))
    have hb : Continuous fun M : Mat n => blkM ε M :=
      continuous_pi fun x => (continuous_apply x.1.2).comp (continuous_apply x.1.1)
    exact hb.comp ((continuous_toM ε).comp hcEB)
  have hβ0 : β 0 = 0 := by
    show blkM ε (toM (eB ε 0)) = 0
    rw [hEB0]; exact blkM_one ε
  have hβd : HasFDerivAt β (ContinuousLinearMap.id ℝ (Mode ε → ℂ)) 0 := by
    rw [hβe]; exact (hD n ε).1
  have hco : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, ‖β B x‖ ^ 2 ≤ η → ‖B‖ ≤ δ := by
    intro δ hδ
    refine ⟨δ ^ 2, by positivity, fun B hB => ?_⟩
    have h1 := hL n ε B
    have h2 : rM ε (NormedSpace.exp (pB ε B)) = ∑ x, ‖β B x‖ ^ 2 := by
      rw [hβe]; rfl
    refine (norm_le_sqrt B).trans ?_
    rw [← Real.sqrt_sq hδ.le]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlim := hF (Mode ε) β (fun _ => 1) (ContinuousLinearMap.id ℝ _) (fun _ => one_ne_zero)
    (fun v x => by simp) hβc hβ0 hβd hco G hG ψ hψc
  have hval : ψ (nMode ε) 0 = (J 0 : ℂ) * ∫ k, ev (toMK k) (p (nMode ε)) * w k ∂(muK ε) := by
    simp only [ψ, hEB0, mul_one]
  have heq : ∀ᶠ t : ℝ in atTop, ∫ g, famF ε G p t (toM g) * w g ∂μ =
      ∫ B, ∑ k ∈ Finset.range (Fintype.card (Mode ε) + 1),
        ((iteratedDeriv k (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    obtain ⟨hc, hs⟩ := fam_cs hR ε hG p ht w hw
    rw [hpol _ hc hs]
    refine integral_congr_ae (Eventually.of_forall fun B => ?_)
    have hr : ∀ k : KG ε, rM ε (toM ((k : UJ ε) * eB ε B)) = ∑ x, ‖β B x‖ ^ 2 := fun k => by
      have := (hR n ε).2.1 k 1 (eB ε B)
      simp only [OneMemClass.coe_one, mul_one] at this
      rw [this]; rfl
    have hint : ∀ j, Integrable (fun k : KG ε => ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B))
        (muK ε) := fun j => by
      have hm : Continuous fun k : KG ε => (k : UJ ε) * eB ε B := continuous_subtype_val.mul continuous_const
      have hc1 : Continuous fun k : KG ε => ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B) :=
        ((continuous_ev _).comp ((continuous_toM ε).comp hm)).mul (hw.comp hm)
      exact integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
    have hpt : ∀ k : KG ε, famF ε G p t (toM ((k : UJ ε) * eB ε B)) * w (k * eB ε B) =
        ∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1),
          ((iteratedDeriv j (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) *
            (ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B)) := fun k => by
      show (∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1), bas ε (iteratedDeriv j fun x => G (t * x)) (p j)
        (toM ((k : UJ ε) * eB ε B))) * _ = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bas, hr k]
      ring
    show (J B : ℂ) * ∫ k : KG ε, famF ε G p t (toM ((k : UJ ε) * eB ε B)) * w (k * eB ε B) ∂(muK ε) = _
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finset_sum _ fun j _ => (hint j).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring
  have h2 := hlim.congr' (heq.mono fun t h => h.symm)
  convert h2 using 2
  rw [show Fintype.card (Mode ε) = nMode ε from rfl, hval]
  simp only [norm_one, one_pow, Finset.prod_const_one, Complex.ofReal_one, div_one]
  ring

theorem lim2 (hEB : StEB) (hR : StR) (hL : StExpLow) (hD : StExpDeriv) (hC : StConjLow) (hF : StFamBlow)
    (ε : Fin n → Bool) (μ : Measure (UJ ε)) (J : (Mode ε → ℂ) → ℝ) (hJc : Continuous J)
    (hpol : ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = ∫ B, (J B : ℂ) * ∫ k : KG ε, f (eB ε B * k) ∂(muK ε))
    (G : ℝ → ℝ) (hG : IsProfile (nMode ε) G) (p : ℕ → Poly n) (θ : Fin n → ℝ) (s : UJ ε)
    (hs : toM s = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)))
    (hinj : Function.Injective (fun a => Complex.exp (θ a * Complex.I)))
    (hinv : ∀ k : KG ε, ev (toM ((k : UJ ε)⁻¹ * s * (k : UJ ε))) (p (nMode ε)) = ev (toM s) (p (nMode ε))) :
    Tendsto (fun t : ℝ => ∫ x, famF ε G p t (toM (x⁻¹ * s * x)) ∂μ) atTop
      (𝓝 ((J 0 : ℂ) * ((∫ v : Mode ε → ℂ, iteratedDeriv (nMode ε) G (∑ x, ‖v x‖ ^ 2) : ℝ) : ℂ) *
        ev (toM s) (p (nMode ε)) / (dMode ε θ : ℂ))) := by
  obtain ⟨hcEB, hEB0, hEBm⟩ := hEB n ε
  set d : Fin n → ℂ := fun a => Complex.exp (θ a * Complex.I) with hd
  let β : (Mode ε → ℂ) → (Mode ε → ℂ) := fun B => blkM ε (toM ((eB ε B)⁻¹ * s * eB ε B))
  have hβe : β = fun B => blkM ε (NormedSpace.exp (-pB ε B) * Matrix.diagonal d * NormedSpace.exp (pB ε B)) :=
    funext fun B => by simp only [β, toM_mul, (hEBm B).1, (hEBm B).2, hs]
  obtain ⟨L, hLd, hLder⟩ := (hD n ε).2 d
  have hdd : ∀ x : Mode ε, d x.1.1 - d x.1.2 ≠ 0 := fun x h => by
    have hne : x.1.1 ≠ x.1.2 := fun h' => by
      have h1 := x.2.1; have h2 := x.2.2; rw [h'] at h1; rw [h1] at h2; exact Bool.noConfusion h2
    exact hne (hinj (sub_eq_zero.1 h))
  let ψ : ℕ → (Mode ε → ℂ) → ℂ := fun j B =>
    (J B : ℂ) * ∫ k : KG ε, ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j) ∂(muK ε)
  have hcont2 : ∀ j, Continuous (Function.uncurry fun (B : Mode ε → ℂ) (k : KG ε) =>
      ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j)) := fun j => by
    have hy : Continuous fun q : (Mode ε → ℂ) × KG ε => (eB ε q.1)⁻¹ * s * eB ε q.1 :=
      ((hcEB.comp continuous_fst).inv.mul continuous_const).mul (hcEB.comp continuous_fst)
    have hk : Continuous fun q : (Mode ε → ℂ) × KG ε => (q.2 : UJ ε) := continuous_subtype_val.comp continuous_snd
    exact (continuous_ev _).comp ((continuous_toM ε).comp ((hk.inv.mul hy).mul hk))
  have hψc : ∀ j, Continuous (ψ j) := fun j => by
    refine (Complex.continuous_ofReal.comp hJc).mul ?_
    have := continuous_parametric_integral_of_continuous (μ := muK ε) (hcont2 j) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hβc : Continuous β := by
    have hb : Continuous fun M : Mat n => blkM ε M :=
      continuous_pi fun x => (continuous_apply x.1.2).comp (continuous_apply x.1.1)
    exact hb.comp ((continuous_toM ε).comp ((hcEB.inv.mul continuous_const).mul hcEB))
  have hβ0 : β 0 = 0 := by
    show blkM ε (toM ((eB ε 0)⁻¹ * s * eB ε 0)) = 0
    rw [hEB0, inv_one, one_mul, mul_one, hs]; exact blkM_diag ε _
  have hβd : HasFDerivAt β L 0 := by rw [hβe]; exact hLder
  have hco : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, ‖β B x‖ ^ 2 ≤ η → ‖B‖ ≤ δ := by
    intro δ hδ
    obtain ⟨η, hη, hη'⟩ := hC n ε s d hs hinj (δ ^ 2) (by positivity)
    refine ⟨η, hη, fun B hB => ?_⟩
    have h3 := hη' (eB ε B) (by rw [rM_eq_blk]; exact hB)
    have h1 := hL n ε B
    rw [← (hEBm B).1] at h1
    refine (norm_le_sqrt B).trans ?_
    rw [← Real.sqrt_sq hδ.le]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlim := hF (Mode ε) β (fun x => d x.1.1 - d x.1.2) L hdd hLd hβc hβ0 hβd hco G hG ψ hψc
  have hval : ψ (nMode ε) 0 = (J 0 : ℂ) * ev (toM s) (p (nMode ε)) := by
    simp only [ψ, hEB0, inv_one, one_mul, mul_one]
    rw [integral_congr_ae (Eventually.of_forall hinv)]
    simp [integral_const, Measure.real, muK_univ]
  obtain ⟨η, hη, hη'⟩ := hC n ε s d hs hinj 1 one_pos
  have heq : ∀ᶠ t : ℝ in atTop, ∫ x, famF ε G p t (toM (x⁻¹ * s * x)) ∂μ =
      ∫ B, ∑ k ∈ Finset.range (Fintype.card (Mode ε) + 1),
        ((iteratedDeriv k (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B := by
    filter_upwards [eventually_gt_atTop (1 / η)] with t ht
    have ht0 : 0 < t := lt_trans (by positivity) ht
    have hc : Continuous fun x : UJ ε => famF ε G p t (toM (x⁻¹ * s * x)) :=
      (continuous_famF ε hG.1 p t).comp ((continuous_toM ε).comp ((continuous_inv.mul continuous_const).mul
        continuous_id))
    have hcs : HasCompactSupport fun x : UJ ε => famF ε G p t (toM (x⁻¹ * s * x)) := by
      refine HasCompactSupport.intro ((hR n ε).2.2.2 1) fun x hx => ?_
      by_contra hne
      have hle : t * rM ε (toM (x⁻¹ * s * x)) ≤ 1 := by
        by_contra hlt; exact hne (famF_eq_zero ε hG.2.1 p ht0 (not_le.1 hlt))
      have h4 : rM ε (toM (x⁻¹ * s * x)) ≤ η := by
        have h5 : rM ε (toM (x⁻¹ * s * x)) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
        have h6 : 1 / t < η := by rw [div_lt_iff₀ ht0]; rw [div_lt_iff₀ hη] at ht; linarith
        linarith
      exact hx (hη' x h4)
    rw [hpol _ hc hcs]
    refine integral_congr_ae (Eventually.of_forall fun B => ?_)
    have hr : ∀ k : KG ε, rM ε (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) = ∑ x, ‖β B x‖ ^ 2 :=
      fun k => by
        have := (hR n ε).2.1 k⁻¹ k ((eB ε B)⁻¹ * s * eB ε B)
        simp only [InvMemClass.coe_inv] at this
        rw [this]; rfl
    have hint : ∀ j, Integrable (fun k : KG ε =>
        ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j)) (muK ε) := fun j => by
      have hk : Continuous fun k : KG ε => (k : UJ ε) := continuous_subtype_val
      have hc1 : Continuous fun k : KG ε => ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j) :=
        (continuous_ev _).comp ((continuous_toM ε).comp ((hk.inv.mul continuous_const).mul hk))
      exact integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
    have hpt : ∀ k : KG ε, famF ε G p t (toM ((eB ε B * (k : UJ ε))⁻¹ * s * (eB ε B * (k : UJ ε)))) =
        ∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1),
          ((iteratedDeriv j (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) *
            ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j) := fun k => by
      have hg : (eB ε B * (k : UJ ε))⁻¹ * s * (eB ε B * (k : UJ ε)) = (k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * k := by group
      rw [hg]
      show ∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1), bas ε (iteratedDeriv j fun x => G (t * x)) (p j)
        (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) = _
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bas, hr k]
    show (J B : ℂ) * ∫ k : KG ε, famF ε G p t (toM ((eB ε B * (k : UJ ε))⁻¹ * s * (eB ε B * (k : UJ ε)))) ∂(muK ε) = _
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finset_sum _ fun j _ => (hint j).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring
  have h2 := hlim.congr' (heq.mono fun t h => h.symm)
  convert h2 using 2
  rw [show Fintype.card (Mode ε) = nMode ε from rfl, hval]
  simp only [dMode, d]
  push_cast
  ring

end GlobalTheory.PsCo.Pcd

end
end

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc3

namespace GlobalTheory.PsCo.Pcd

theorem stLim_of (hEB : StEB) (hR : StR) (hP : StPolar) (hL : StExpLow) (hD : StExpDeriv) (hC : StConjLow)
    (hF : StFamBlow) (hK : StConst) : StLim := by
  intro n ε μ _ G hG
  obtain ⟨J, hJc, hJ0, hpol⟩ := hP n ε μ
  have hκ := hK (Mode ε) G hG
  refine ⟨(J 0 : ℂ) * ((∫ v : Mode ε → ℂ, iteratedDeriv (nMode ε) G (∑ x, ‖v x‖ ^ 2) : ℝ) : ℂ),
    mul_ne_zero (by exact_mod_cast hJ0.ne') (by exact_mod_cast hκ), fun p => ⟨fun w hw => ?_, ?_⟩⟩
  · have := lim1 hEB hR hL hD hF ε μ J hJc (fun f hf hs => (hpol f hf hs).1) G hG p w hw
    simpa only [mul_assoc] using this
  · intro θ s hs hinj hinv
    have := lim2 hEB hR hL hD hC hF ε μ J hJc (fun f hf hs => (hpol f hf hs).2) G hG p θ s hs hinj hinv
    simpa only [mul_assoc, mul_div_assoc] using this

end GlobalTheory.PsCo.Pcd

end
end

namespace GlobalTheory.PsCo.Pcd

theorem stLim : GlobalTheory.PsCo.Pc1.StLim :=
  stLim_of GlobalTheory.PsCo.Pc3.stEB GlobalTheory.PsCo.Pc3.stR GlobalTheory.PsCo.Pc3.stPolar GlobalTheory.PsCo.Pc3.stExpLow GlobalTheory.PsCo.Pc3.stExpDeriv GlobalTheory.PsCo.Pcd.stConjLow GlobalTheory.PsCo.Pcd.stFamBlow GlobalTheory.PsCo.Pc3.stConst_holds

end GlobalTheory.PsCo.Pcd
