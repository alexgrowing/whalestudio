import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsSmoothL2OfCasimirEigen
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ContDiffOnZeroOfContinuousOn
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

noncomputable section

open Finset Matrix MeasureTheory Set Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Spec

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local notation "JJ" => Formalism.REAL.Jm

variable {ε : Fin n → Bool}

theorem toL2_eq_toLp_of_memLp {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε F = hF.toLp _ := by
  unfold toL2
  rw [dif_pos hF]

theorem slm_exists_y {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h2 : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    calc (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hJJ]
  have h1 : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
    rw [← Matrix.inv_eq_left_inv h2]
    exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse h2)
  exact ⟨⟨⟨g, _, h1, h2⟩, hg⟩, rfl⟩

theorem slm_memLp_tr {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun x : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat x)) 2 (Formalism.REAL.muG ε))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    MemLp (fun x : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat x * g)) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨y, rfl⟩ := slm_exists_y hg
  exact hF.comp_measurePreserving (measurePreserving_mul_right ε y)

theorem slm_contOn {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F) :
    ContinuousOn F {g | Formalism.REAL.inUJ ε g} := by
  intro g₀ hg₀
  obtain ⟨U, G, hU, hgU, hG, hFG⟩ := hF g₀ hg₀
  have hc : ContinuousAt G g₀ := hG.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hFG g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin {g | Formalism.REAL.inUJ ε g} (hU.mem_nhds hgU)] with g hg
  exact hFG g hg.2 hg.1

theorem slm_Rd_zero (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Rd 0 F g = 0 := by
  simp [Formalism.REAL.Rd]

theorem slm_Rd_sum {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : Formalism.REAL.inG ε Y) :
    Formalism.REAL.Rd Y F g = ∑ a, ∑ b, Y a b * Formalism.REAL.Eab ε a b F g := by
  have h := Formalism.REAL.ecSumV n ε ℂ F Y g hF hg
  have h1 : Formalism.REAL.cpart1 ε Y = Y := skewAdjointPart_eq_self_of_isSkewAdjoint hY
  have h2 : Formalism.REAL.cpart2 ε Y = 0 := by
    have hY' := hY
    unfold Formalism.REAL.inG at hY'
    have e : Yᴴ * JJ ε = -(JJ ε * Y) := eq_neg_of_add_eq_zero_left hY'
    have e2 : JJ ε * Yᴴ * JJ ε = -Y := by rw [Matrix.mul_assoc, e, Matrix.mul_neg, slm_JJ]
    unfold Formalism.REAL.cpart2
    rw [e2, add_neg_cancel, smul_zero]
  unfold Formalism.REAL.EcV at h
  rw [h1, h2] at h
  have h0 : Formalism.REAL.RdV (0 : Matrix (Fin n) (Fin n) ℂ) F g = 0 := slm_Rd_zero F g
  rw [h0, smul_zero, add_zero] at h
  exact h

theorem slm_chain {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F)
    {c : ℝ → Matrix (Fin n) (Fin n) ℂ} {c' : Matrix (Fin n) (Fin n) ℂ} {s0 : ℝ}
    (hc : HasDerivAt c c' s0) (hcU : ∀ᶠ s in 𝓝 s0, Formalism.REAL.inUJ ε (c s)) :
    HasDerivAt (fun s => F (c s))
      (∑ a, ∑ b, (slmJi ε (c s0) * c') a b * Formalism.REAL.Eab ε a b F (c s0)) s0 := by
  have hc0 : Formalism.REAL.inUJ ε (c s0) := hcU.self_of_nhds
  obtain ⟨U, Ft, hU, hmem, hcd, heq⟩ := hF (c s0) hc0
  have hY := slm_inG_of_curve hc hcU
  have hdiff : DifferentiableAt ℝ Ft (c s0) :=
    (hcd.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hmem)
  have h1 : HasDerivAt (fun s => Ft (c s)) (fderiv ℝ Ft (c s0) c') s0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt s0 hc
  have hev : (fun s => F (c s)) =ᶠ[𝓝 s0] fun s => Ft (c s) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hmem), hcU] with s hs1 hs2
    exact heq _ hs1 hs2
  have hR : Formalism.REAL.Rd (slmJi ε (c s0) * c') F (c s0) = fderiv ℝ Ft (c s0) c' := by
    have h := Formalism.REAL.rdExtV n ε ℂ F Ft U (c s0) (slmJi ε (c s0) * c') hU hmem hc0 hcd heq hY
    rw [← Matrix.mul_assoc, slm_mul_Ji hc0, Matrix.one_mul] at h
    exact h
  rw [← slm_Rd_sum hF hc0 hY, hR]
  exact h1.congr_of_eventuallyEq hev

def slmPhi (ε : Fin n → Bool) (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (q : Matrix (Fin n) (Fin n) ℂ) : L2 ε :=
  toL2 ε (fun x => F (x * γ q))

theorem slm_coe_phi {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : MemLp (fun x : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat x)) 2 (Formalism.REAL.muG ε))
    {γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} {q : Matrix (Fin n) (Fin n) ℂ}
    (hq : Formalism.REAL.inUJ ε (γ q)) :
    (slmPhi ε γ F q : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun x => F (Formalism.MainNotions.S.umat x * γ q) := by
  unfold slmPhi
  rw [toL2_eq_toLp_of_memLp (F := fun x => F (x * γ q)) (slm_memLp_tr hF hq)]
  exact MemLp.coeFn_toLp _

theorem slm_phi_eq {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} {q : Matrix (Fin n) (Fin n) ℂ}
    (hq : Formalism.REAL.inUJ ε (γ q)) : slmPhi ε γ F q = rreg ε (γ q) (toL2 ε F) :=
  (rightRegular_toL2 ε F hq).symm

theorem slm_phi_cont {V : Set (Matrix (Fin n) (Fin n) ℂ)}
    {γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγc : ContinuousOn γ V)
    (hγU : ∀ q ∈ V, Formalism.REAL.inUJ ε (γ q)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    ContinuousOn (slmPhi ε γ F) V := by
  have h1 : ContinuousOn (fun q => rreg ε (γ q) (toL2 ε F)) V :=
    ((rreg_isURepOn ε).2.2 (toL2 ε F)).comp hγc (fun q hq => hγU q hq)
  exact h1.congr fun q hq => slm_phi_eq (hγU q hq)

def slmSum (ε : Fin n → Bool) (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (W q x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ a, ∑ b, (slmJi ε (γ q) * fderiv ℝ γ q W) a b * Formalism.REAL.Eab ε a b F (x * γ q)

def slmDv (ε : Fin n → Bool) (γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
    (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (W q : Matrix (Fin n) (Fin n) ℂ) : L2 ε :=
  ∑ a, ∑ b, ((slmJi ε (γ q) * fderiv ℝ γ q W) a b) • slmPhi ε γ (Formalism.REAL.Eab ε a b F) q

theorem slm_coe_Dv {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F)
    {γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} {q : Matrix (Fin n) (Fin n) ℂ}
    (hq : Formalism.REAL.inUJ ε (γ q)) (W : Matrix (Fin n) (Fin n) ℂ) :
    (slmDv ε γ F W q : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun x => slmSum ε γ F W q (Formalism.MainNotions.S.umat x) := by
  have h2 : ∀ a, (⇑(∑ b, ((slmJi ε (γ q) * fderiv ℝ γ q W) a b) •
      slmPhi ε γ (Formalism.REAL.Eab ε a b F) q) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun x => ∑ b, (slmJi ε (γ q) * fderiv ℝ γ q W) a b *
        Formalism.REAL.Eab ε a b F (Formalism.MainNotions.S.umat x * γ q) := by
    intro a
    have h3 := slm_coeFn_sum (μ := Formalism.REAL.muG ε) Finset.univ
      (fun b => ((slmJi ε (γ q) * fderiv ℝ γ q W) a b) • slmPhi ε γ (Formalism.REAL.Eab ε a b F) q)
    have h4 : ∀ b, (⇑(((slmJi ε (γ q) * fderiv ℝ γ q W) a b) •
        slmPhi ε γ (Formalism.REAL.Eab ε a b F) q) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
        fun x => (slmJi ε (γ q) * fderiv ℝ γ q W) a b *
          Formalism.REAL.Eab ε a b F (Formalism.MainNotions.S.umat x * γ q) := by
      intro b
      filter_upwards [Lp.coeFn_smul ((slmJi ε (γ q) * fderiv ℝ γ q W) a b)
        (slmPhi ε γ (Formalism.REAL.Eab ε a b F) q),
        slm_coe_phi (F := Formalism.REAL.Eab ε a b F) ((hF.Eab a b).2 []) hq] with x hx1 hx2
      rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]
    have h5 := ae_all_iff.mpr h4
    filter_upwards [h3, h5] with x hx3 hx5
    rw [hx3]
    exact Finset.sum_congr rfl fun b _ => hx5 b
  have h1 := slm_coeFn_sum (μ := Formalism.REAL.muG ε) Finset.univ
    (fun a => ∑ b, ((slmJi ε (γ q) * fderiv ℝ γ q W) a b) • slmPhi ε γ (Formalism.REAL.Eab ε a b F) q)
  have h6 := ae_all_iff.mpr h2
  filter_upwards [h1, h6] with x hx1 hx6
  unfold slmDv slmSum
  rw [hx1]
  exact Finset.sum_congr rfl fun a _ => hx6 a

def slmCl (s : ℝ) : ℝ := max 0 (min s 1)

theorem slmCl_mem (s : ℝ) : slmCl s ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem slmCl_cont : Continuous slmCl :=
  continuous_const.max (continuous_id.min continuous_const)

theorem slmCl_eq {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : slmCl s = s := by
  unfold slmCl
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem slm_hint {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    {γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V)
    (hγU : ∀ q ∈ V, Formalism.REAL.inUJ ε (γ q)) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F)
    {q : Matrix (Fin n) (Fin n) ℂ} (hq : q ∈ V) :
    ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖slmDv ε γ F W (q + s • W) - slmDv ε γ F W q‖ ≤ B) →
      ‖slmPhi ε γ F (q + W) - slmPhi ε γ F q - slmDv ε γ F W q‖ ≤ B := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV q hq
  refine ⟨δ, hδ, fun W hW B hB => ?_⟩
  have hseg : ∀ s ∈ Icc (0:ℝ) 1, q + s • W ∈ V := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    calc s * ‖W‖ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ < δ := by rw [one_mul]; exact hW
  have hpV : ∀ s, q + slmCl s • W ∈ V := fun s => hseg _ (slmCl_mem s)
  have hp : Continuous (fun s : ℝ => q + slmCl s • W) :=
    continuous_const.add (slmCl_cont.smul continuous_const)
  have hγc : ContinuousOn γ V := hγ.continuousOn
  have hmc : ContDiffOn ℝ ∞ (fun q => slmJi ε (γ q)) V := by
    unfold slmJi
    exact slm_cd_mul (slm_cd_mul contDiffOn_const (slm_cd_conjT hγ)) contDiffOn_const
  have hfdW : ContDiffOn ℝ ∞ (fun q => fderiv ℝ γ q W) V :=
    (hγ.fderiv_of_isOpen (m := ∞) hV (by simp)).clm_apply contDiffOn_const
  have hZe : ∀ a b, ContinuousOn (fun q => (slmJi ε (γ q) * fderiv ℝ γ q W) a b) V :=
    fun a b => ((slm_cd_iff.mp (slm_cd_mul hmc hfdW)) a b).continuousOn
  have hcx : Continuous (fun p : ℝ × Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat p.2) :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd
  have hSc : Continuous (fun p : ℝ × Formalism.REAL.UJ ε =>
      slmSum ε γ F W (q + slmCl p.1 • W) (Formalism.MainNotions.S.umat p.2)) := by
    unfold slmSum
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    refine ((hZe a b).comp_continuous (hp.comp continuous_fst) (fun p => hpV p.1)).mul ?_
    refine (slm_contOn (hF.Eab a b).1).comp_continuous ?_
      (fun p => slm_inUJ_mul p.2.2 (hγU _ (hpV p.1)))
    exact hcx.matrix_mul (hγc.comp_continuous (hp.comp continuous_fst) (fun p => hpV p.1))
  have hS0 : Continuous (fun p : ℝ × Formalism.REAL.UJ ε => slmSum ε γ F W q (Formalism.MainNotions.S.umat p.2)) := by
    unfold slmSum
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    refine continuous_const.mul ?_
    refine (slm_contOn (hF.Eab a b).1).comp_continuous ?_ (fun p => slm_inUJ_mul p.2.2 (hγU q hq))
    exact hcx.matrix_mul continuous_const
  have hDc : Continuous (Function.uncurry (fun (s : ℝ) (x : Formalism.REAL.UJ ε) =>
      slmSum ε γ F W (q + slmCl s • W) (Formalism.MainNotions.S.umat x) - slmSum ε γ F W q (Formalism.MainNotions.S.umat x))) :=
    hSc.sub hS0
  have hr : ∀ x : Formalism.REAL.UJ ε, (F (Formalism.MainNotions.S.umat x * γ (q + W)) - F (Formalism.MainNotions.S.umat x * γ q) -
      slmSum ε γ F W q (Formalism.MainNotions.S.umat x)) = ∫ s in (0:ℝ)..1,
        (slmSum ε γ F W (q + slmCl s • W) (Formalism.MainNotions.S.umat x) - slmSum ε γ F W q (Formalism.MainNotions.S.umat x)) := by
    intro x
    have hderiv : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t => F (Formalism.MainNotions.S.umat x * γ (q + t • W)))
        (slmSum ε γ F W (q + slmCl s • W) (Formalism.MainNotions.S.umat x)) s := by
      intro s hs
      rw [Set.uIcc_of_le zero_le_one] at hs
      rw [slmCl_eq hs]
      have hq' : q + s • W ∈ V := hseg s hs
      have hdγ : HasFDerivAt γ (fderiv ℝ γ (q + s • W)) (q + s • W) :=
        ((hγ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hq')).hasFDerivAt
      have hline := ((hasDerivAt_id' s).smul_const W).const_add q
      simp only [one_smul] at hline
      have hc1 : HasDerivAt (fun t => γ (q + t • W)) (fderiv ℝ γ (q + s • W) W) s :=
        hdγ.comp_hasDerivAt s hline
      have hc2 := slm_hd_mul (hasDerivAt_const s (Formalism.MainNotions.S.umat x)) hc1
      simp only [Matrix.zero_mul, zero_add] at hc2
      have hcU : ∀ᶠ t in 𝓝 s, Formalism.REAL.inUJ ε (Formalism.MainNotions.S.umat x * γ (q + t • W)) := by
        filter_upwards [hline.continuousAt.preimage_mem_nhds (hV.mem_nhds hq')] with t ht
        exact slm_inUJ_mul x.2 (hγU _ ht)
      have h := slm_chain hF.1 hc2 hcU
      have e : slmJi ε (Formalism.MainNotions.S.umat x * γ (q + s • W)) *
          (Formalism.MainNotions.S.umat x * fderiv ℝ γ (q + s • W) W) =
          slmJi ε (γ (q + s • W)) * fderiv ℝ γ (q + s • W) W := by
        rw [slm_Ji_mul_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (slmJi ε (Formalism.MainNotions.S.umat x)),
          slm_Ji_mul x.2, Matrix.one_mul]
      rw [e] at h
      exact h
    have hint1 : IntervalIntegrable (fun s => slmSum ε γ F W (q + slmCl s • W) (Formalism.MainNotions.S.umat x))
        volume 0 1 :=
      (hSc.comp (continuous_id.prodMk continuous_const : Continuous fun s : ℝ => (s, x))).intervalIntegrable 0 1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint1
    simp only [one_smul, zero_smul, add_zero] at hFTC
    rw [intervalIntegral.integral_sub hint1 intervalIntegrable_const, hFTC,
      intervalIntegral.integral_const, sub_zero, one_smul]
  have hBs : ∀ s ∈ Ioc (0:ℝ) 1, eLpNorm (fun x : Formalism.REAL.UJ ε =>
      slmSum ε γ F W (q + slmCl s • W) (Formalism.MainNotions.S.umat x) - slmSum ε γ F W q (Formalism.MainNotions.S.umat x)) 2
        (Formalism.REAL.muG ε) ≤ ENNReal.ofReal B := by
    intro s hs
    have hs' : s ∈ Icc (0:ℝ) 1 := Ioc_subset_Icc_self hs
    rw [slmCl_eq hs']
    have hae : (⇑(slmDv ε γ F W (q + s • W) - slmDv ε γ F W q) : Formalism.REAL.UJ ε → ℂ)
        =ᵐ[Formalism.REAL.muG ε] fun x => slmSum ε γ F W (q + s • W) (Formalism.MainNotions.S.umat x) -
          slmSum ε γ F W q (Formalism.MainNotions.S.umat x) := by
      filter_upwards [Lp.coeFn_sub (slmDv ε γ F W (q + s • W)) (slmDv ε γ F W q),
        slm_coe_Dv hF (hγU _ (hseg s hs')) W, slm_coe_Dv hF (hγU q hq) W] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    rw [← eLpNorm_congr_ae hae, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def]
    exact ENNReal.ofReal_le_ofReal (hB s hs)
  have hLp := slm_eLpNorm_le (μ := Formalism.REAL.muG ε)
    (fun x => F (Formalism.MainNotions.S.umat x * γ (q + W)) - F (Formalism.MainNotions.S.umat x * γ q) -
      slmSum ε γ F W q (Formalism.MainNotions.S.umat x))
    (fun s x => slmSum ε γ F W (q + slmCl s • W) (Formalism.MainNotions.S.umat x) - slmSum ε γ F W q (Formalism.MainNotions.S.umat x))
    hDc.measurable hr (ENNReal.ofReal B) hBs
  have hqW : q + W ∈ V := by simpa using hseg 1 ⟨zero_le_one, le_rfl⟩
  have hcoe : (⇑(slmPhi ε γ F (q + W) - slmPhi ε γ F q - slmDv ε γ F W q) : Formalism.REAL.UJ ε → ℂ)
      =ᵐ[Formalism.REAL.muG ε] fun x => F (Formalism.MainNotions.S.umat x * γ (q + W)) - F (Formalism.MainNotions.S.umat x * γ q) -
        slmSum ε γ F W q (Formalism.MainNotions.S.umat x) := by
    filter_upwards [Lp.coeFn_sub (slmPhi ε γ F (q + W) - slmPhi ε γ F q) (slmDv ε γ F W q),
      Lp.coeFn_sub (slmPhi ε γ F (q + W)) (slmPhi ε γ F q),
      slm_coe_phi (F := F) (hF.2 []) (hγU _ hqW), slm_coe_phi (F := F) (hF.2 []) (hγU q hq),
      slm_coe_Dv hF (hγU q hq) W] with x h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, h4, h5]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1 ⟨zero_lt_one, le_rfl⟩)
  rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hLp

theorem slm_mc {V : Set (Matrix (Fin n) (Fin n) ℂ)}
    {γ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ} (hγ : ContDiffOn ℝ ∞ γ V) :
    ContDiffOn ℝ ∞ (fun q => slmJi ε (γ q)) V := by
  have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => JJ ε * Mᴴ * JJ ε) :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun M => JJ ε * Mᴴ * JJ ε
      map_add' := fun A B => by
        simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c A => by
        simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul,
          RingHom.id_apply]
      cont := hcont }
  exact L.contDiff.comp_contDiffOn hγ

theorem slm_smooth {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) :
    S7.SmoothOnGV ε (fun g => rreg ε g (toL2 ε F)) := by
  intro g0 hg0
  obtain ⟨V, γ, hV, hg0V, hγ, hγU, hγid⟩ := slm_exists_ret ε hg0
  refine ⟨V, slmPhi ε γ F, hV, hg0V, ?_, ?_⟩
  · exact slm_mat hV hγ (slm_mc hγ) (slmPhi ε γ) (IsSmoothL2 ε) (Formalism.REAL.Eab ε)
      (fun G hG a b => hG.Eab a b) (fun G _ => slm_phi_cont hγ.continuousOn hγU G)
      (fun G hG q hq => slm_hint hV hγ hγU hG hq) F hF
  · intro g hgV hgU
    show rreg ε g (toL2 ε F) = slmPhi ε γ F g
    rw [slm_phi_eq (hγU g hgV), hγid g hgV hgU]

theorem slm_dS {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Formalism.REAL.inG ε X) :
    dS (rreg ε) X (toL2 ε F) = ∑ c, ∑ d, X c d • toL2 ε (Formalism.REAL.Eab ε c d F) := by
  have h1U : Formalism.REAL.inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
    unfold Formalism.REAL.inUJ
    simp
  obtain ⟨V, γ, hV, h1V, hγ, hγU, hγid⟩ := slm_exists_ret ε h1U
  have hD := slm_mat_hD hV hγ (slm_mc hγ) (slmPhi ε γ) (IsSmoothL2 ε) (Formalism.REAL.Eab ε)
    (fun G hG a b => hG.Eab a b) (fun G _ => slm_phi_cont hγ.continuousOn hγU G)
    (fun G hG q hq => slm_hint hV hγ hγU hG hq) F hF 1 h1V
  have hcurve : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
    have h := Formalism.REAL.hasDerivAt_mul_exp_smul_zero (1 : Matrix (Fin n) (Fin n) ℂ) X
    simp only [Matrix.one_mul] at h
    exact h
  have h0 : NormedSpace.exp (((0:ℝ) : ℂ) • X) = 1 := by simp
  have hev1 : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), NormedSpace.exp ((t : ℂ) • X) ∈ V :=
    hcurve.continuousAt.preimage_mem_nhds (by rw [h0]; exact hV.mem_nhds h1V)
  have hexpU : ∀ t : ℝ, Formalism.REAL.inUJ ε (NormedSpace.exp ((t : ℂ) • X)) :=
    fun t => Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t
  have hdγ : HasFDerivAt γ (fderiv ℝ γ 1) 1 :=
    ((hγ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds h1V)).hasFDerivAt
  have hγc : HasDerivAt (fun t : ℝ => γ (NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ γ 1 X) 0 :=
    hdγ.comp_hasDerivAt_of_eq 0 hcurve h0.symm
  have hγc' : HasDerivAt (fun t : ℝ => γ (NormedSpace.exp ((t : ℂ) • X))) X 0 :=
    hcurve.congr_of_eventuallyEq (by filter_upwards [hev1] with t ht; exact hγid _ ht (hexpU t))
  have hfd : fderiv ℝ γ 1 X = X := hγc.unique hγc'
  have hγ1 : γ 1 = 1 := hγid 1 h1V h1U
  have hm1 : slmJi ε (γ 1) = 1 := by
    rw [hγ1]
    unfold slmJi
    simp [Formalism.REAL.Jm_mul_self]
  have hΦc := hD.comp_hasDerivAt_of_eq 0 hcurve h0.symm
  have hev2 : (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (toL2 ε F)) =ᶠ[𝓝 0]
      (slmPhi ε γ F ∘ fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hev1] with t ht
    simp only [Function.comp]
    rw [slm_phi_eq (hγU _ ht), hγid _ ht (hexpU t)]
  unfold dS
  refine ((hΦc.congr_of_eventuallyEq hev2).deriv).trans ?_
  refine (slmG_mat_apply γ (fun q => slmJi ε (γ q)) 1 (fun a b => slmPhi ε γ (Formalism.REAL.Eab ε a b F) 1) X).trans ?_
  simp only [hfd, hm1, Matrix.one_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  unfold slmPhi
  rw [hγ1]
  simp only [Matrix.mul_one]

theorem slm_mem_smD {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) :
    toL2 ε F ∈ smD ε (rreg ε) :=
  ((exists_smoothDerived ε (rreg ε)).choose_spec.choose_spec.1 _).2 (slm_smooth hF)

theorem slm_smE {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) (a b : Fin n) :
    ((smE ε (rreg ε) a b ⟨toL2 ε F, slm_mem_smD hF⟩ : smD ε (rreg ε)) : L2 ε) =
      toL2 ε (Formalism.REAL.Eab ε a b F) := by
  have hσ := rreg_isURepOn ε
  obtain ⟨hc1, hc2, hdec, -⟩ := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  rw [smE_apply hσ]
  show dS (rreg ε) (S7.cpart1 ε (Matrix.single a b 1)) (toL2 ε F) +
      Complex.I • dS (rreg ε) (S7.cpart2 ε (Matrix.single a b 1)) (toL2 ε F) =
    toL2 ε (Formalism.REAL.Eab ε a b F)
  rw [slm_dS (X := S7.cpart1 ε (Matrix.single a b 1)) hF hc1,
    slm_dS (X := S7.cpart2 ε (Matrix.single a b 1)) hF hc2]
  have hZ : S7.cpart1 ε (Matrix.single a b 1) + Complex.I • S7.cpart2 ε (Matrix.single a b 1) =
      Matrix.single a b 1 := hdec.symm
  calc ∑ c, ∑ d, S7.cpart1 ε (Matrix.single a b 1) c d • toL2 ε (Formalism.REAL.Eab ε c d F) +
        Complex.I • ∑ c, ∑ d, S7.cpart2 ε (Matrix.single a b 1) c d • toL2 ε (Formalism.REAL.Eab ε c d F)
      = ∑ c, ∑ d, (S7.cpart1 ε (Matrix.single a b 1) + Complex.I • S7.cpart2 ε (Matrix.single a b 1)) c d •
          toL2 ε (Formalism.REAL.Eab ε c d F) := by
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul]
    _ = ∑ c, ∑ d, (Matrix.single a b 1 : Matrix (Fin n) (Fin n) ℂ) c d • toL2 ε (Formalism.REAL.Eab ε c d F) := by
        rw [hZ]
    _ = toL2 ε (Formalism.REAL.Eab ε a b F) := by
        rw [Finset.sum_eq_single a (fun c _ hc => Finset.sum_eq_zero fun d _ => by
            simp [Ne.symm hc]) (fun h => absurd (Finset.mem_univ _) h),
          Finset.sum_eq_single b (fun d _ hd => by simp [Ne.symm hd])
            (fun h => absurd (Finset.mem_univ _) h)]
        simp

end Spec

end ReciprocityTheory.ChartRestriction.DS
