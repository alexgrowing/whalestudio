import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.ExistsBumpOne
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CuspPairD
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_aS : Continuous (aS E n) :=
  GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.prodMk continuous_const

theorem lg_one_eq_zero : lg (1 : GA E n) = 0 := by
  have h := lg_mul (1 : GA E n) 1
  rw [mul_one] at h
  linarith

theorem lg_splitCentre (s : ℝ) : lg (splitCentre E n s) = s * lg (splitCentre E n 1) := by
  let f : ℝ →+ ℝ :=
    { toFun := fun s => lg (splitCentre E n s)
      map_zero' := by simp only [splitCentre_zero, lg_one_eq_zero]
      map_add' := fun s t => by simp only [splitCentre_add, lg_mul] }
  have hf : Continuous f := by
    show Continuous fun s => logAbs (splitCentre E n s).val.det
    exact continuous_logAbs_det.comp GlobalTheory.OneRep.SplitTwist.continuous_splitCentre
  have h := map_real_smul f hf s 1
  simpa [f, smul_eq_mul] using h

theorem ldet_mul_aS (x : H E n 0) (s : ℝ) : ldet (x * aS E n s) = ldet x + s * ldet (aS E n 1) := by
  show lg (x.1 * splitCentre E n s) = lg x.1 + s * lg (splitCentre E n 1)
  rw [lg_mul, lg_splitCentre]

theorem ldet_rat (γ : ratH E n 0) (y : H E n 0) : ldet ((γ : H E n 0) * y) = ldet y :=
  lg_rat_mul _ (eR γ).2 y.1

theorem sigmaFinite_nu (hn : 1 ≤ n) (D : Dom E n 0) : SigmaFinite D.ν :=
  ⟨⟨{ set := fun k : ℕ => {x : H E n 0 | |ldet x| ≤ k}
      set_mem := fun _ => Set.mem_univ _
      finite := fun k => CP.cp_vol hn D k
      spanning := Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈|ldet x|⌉₊, show |ldet x| ≤ (⌈|ldet x|⌉₊ : ℝ) from Nat.le_ceil _⟩ }⟩⟩

theorem integral_shift {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (D : Dom E n 0) (g : H E n 0 → F')
    (hg : ∀ (γ : ratH E n 0) x, g ((γ : H E n 0) * x) = g x) (a : H E n 0) :
    ∫ x, g (x * a) ∂D.ν = ∫ x, g x ∂D.ν := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI := D.haar.2.1
  haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ :=
    ⟨fun γ s _ => by haveI := D.haar.1; exact measure_preimage_mul D.μ (γ : H E n 0) s⟩
  haveI : Countable (ratH E n 0) := (eR_bijective (E := E) (n := n)).1.countable
  have hmp : MeasurePreserving (fun x : H E n 0 => x * a) D.μ D.μ := measurePreserving_mul_right D.μ a
  have hemb : MeasurableEmbedding (fun x : H E n 0 => x * a) :=
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableEmbedding
  have hfd : IsFundamentalDomain (ratH E n 0) ((fun x : H E n 0 => x * a) ⁻¹' D.F) D.μ :=
    D.fd.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, id, mul_assoc]
  rw [Dom.ν, D.fd.setIntegral_eq hfd (f := fun x => g (x * a)) fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc, hg]]
  exact hmp.setIntegral_preimage_emb hemb g D.F

theorem lintegral_shift (D : Dom E n 0) (g : H E n 0 → ℝ≥0∞)
    (hg : ∀ (γ : ratH E n 0) x, g ((γ : H E n 0) * x) = g x) (a : H E n 0) :
    ∫⁻ x, g (x * a) ∂D.ν = ∫⁻ x, g x ∂D.ν := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI := D.haar.2.1
  haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ :=
    ⟨fun γ s _ => by haveI := D.haar.1; exact measure_preimage_mul D.μ (γ : H E n 0) s⟩
  haveI : Countable (ratH E n 0) := (eR_bijective (E := E) (n := n)).1.countable
  have hmp : MeasurePreserving (fun x : H E n 0 => x * a) D.μ D.μ := measurePreserving_mul_right D.μ a
  have hemb : MeasurableEmbedding (fun x : H E n 0 => x * a) :=
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableEmbedding
  have hfd : IsFundamentalDomain (ratH E n 0) ((fun x : H E n 0 => x * a) ⁻¹' D.F) D.μ :=
    D.fd.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, id, mul_assoc]
  rw [Dom.ν, D.fd.setLIntegral_eq hfd (f := fun x => g (x * a)) fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc, hg]]
  exact hmp.setLIntegral_comp_preimage_emb hemb g D.F

theorem integrable_shift (D : Dom E n 0) (g : H E n 0 → ℂ) (hg : ∀ (γ : ratH E n 0) x, g ((γ : H E n 0) * x) = g x)
    (a : H E n 0) (hgi : Integrable g D.ν) (hm : AEStronglyMeasurable (fun x => g (x * a)) D.ν) :
    Integrable (fun x => g (x * a)) D.ν :=
  ⟨hm, (lintegral_shift D (fun x => ‖g x‖ₑ) (fun γ x => by simp only [hg]) a).trans_lt hgi.2⟩

theorem integral_affine {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (v : ℝ → F') (r c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, v (r - s * c) = c⁻¹ • ∫ u : ℝ, v u := by
  have h1 : (fun s : ℝ => v (r - s * c)) = fun s => (fun u => v (r - u)) (c * s) := by
    funext s
    show v (r - s * c) = v (r - c * s)
    rw [mul_comm]
  rw [h1, Measure.integral_comp_mul_left (fun u => v (r - u)) c, integral_sub_left_eq_self (fun u => v u) volume r,
    abs_of_pos (inv_pos.2 hc)]

theorem avgInt_holds : AvgInt := by
  intro E _ _ _ n hn D L hL hLc hLi w hwc hws hw1
  haveI := borelSpace_H (E := E) (n := n)
  haveI := sigmaFinite_nu hn D
  obtain ⟨c, hc_eq⟩ : ∃ c, c = ldet (aS E n 1) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_eq]; exact lg_e_pos hn
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  have hldc : Continuous (ldet : H E n 0 → ℝ) := continuous_ldet
  have cF3 : Continuous fun p : H E n 0 × ℝ => w (ldet p.1 - p.2 * c) * L p.1 :=
    (hwc.comp ((hldc.comp continuous_fst).sub (continuous_snd.mul continuous_const))).mul (hLc.comp continuous_fst)
  have cF2 : Continuous fun p : H E n 0 × ℝ => w (ldet p.1) * L (p.1 * aS E n p.2) :=
    (hwc.comp (hldc.comp continuous_fst)).mul (hLc.comp (continuous_fst.mul (continuous_aS.comp continuous_snd)))
  have hF3 : Integrable (fun p : H E n 0 × ℝ => w (ldet p.1 - p.2 * c) * L p.1) (D.ν.prod volume) := by
    rw [integrable_prod_iff cF3.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact ((hwi.comp_sub_left (ldet x)).comp_mul_right' hc.ne').mul_const (L x)
    · have e : (fun x => ∫ s : ℝ, ‖w (ldet x - s * c) * L x‖) = fun x => (c⁻¹ * ∫ u : ℝ, ‖w u‖) * ‖L x‖ := by
        funext x
        simp_rw [norm_mul]
        rw [integral_mul_const, integral_affine (fun u => ‖w u‖) (ldet x) c hc, smul_eq_mul]
      refine (hLi.norm.const_mul (c⁻¹ * ∫ u : ℝ, ‖w u‖)).congr (Eventually.of_forall fun x => ?_)
      exact (congrFun e x).symm
  have e3x : ∀ x, ∫ s : ℝ, w (ldet x - s * c) * L x = (c : ℂ)⁻¹ * L x := fun x => by
    rw [integral_mul_const, integral_affine w (ldet x) c hc, hw1, Complex.real_smul, mul_one, Complex.ofReal_inv]
  have I3 : ∫ x, ∫ s : ℝ, w (ldet x - s * c) * L x ∂volume ∂D.ν = (c : ℂ)⁻¹ * ∫ x, L x ∂D.ν := by
    simp_rw [e3x]
    exact integral_const_mul _ _
  have swap3 : ∫ x, ∫ s : ℝ, w (ldet x - s * c) * L x ∂volume ∂D.ν =
      ∫ s : ℝ, ∫ x, w (ldet x - s * c) * L x ∂D.ν ∂volume := integral_integral_swap hF3
  have hinv : ∀ s : ℝ, ∀ (γ : ratH E n 0) y, w (ldet ((γ : H E n 0) * y) - s * c) * L ((γ : H E n 0) * y) =
      w (ldet y - s * c) * L y := fun s γ y => by rw [ldet_rat, hL]
  have shift32 : ∀ s : ℝ, ∫ x, w (ldet x - s * c) * L x ∂D.ν = ∫ x, w (ldet x) * L (x * aS E n s) ∂D.ν := by
    intro s
    rw [← integral_shift D (fun y => w (ldet y - s * c) * L y) (hinv s) (aS E n s)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ldet_mul_aS, ← hc_eq, add_sub_cancel_right]
  have hF2 : Integrable (fun p : H E n 0 × ℝ => w (ldet p.1) * L (p.1 * aS E n p.2)) (D.ν.prod volume) := by
    rw [integrable_prod_iff' cF2.aestronglyMeasurable]
    obtain ⟨h1, h2⟩ := (integrable_prod_iff' cF3.aestronglyMeasurable).1 hF3
    refine ⟨h1.mono fun s hs => ?_, ?_⟩
    · have hm : AEStronglyMeasurable (fun x => (fun y => w (ldet y - s * c) * L y) (x * aS E n s)) D.ν :=
        (((hwc.comp (hldc.sub continuous_const)).mul hLc).comp (continuous_mul_right (aS E n s))).aestronglyMeasurable
      refine (integrable_shift D (fun y => w (ldet y - s * c) * L y) (hinv s) (aS E n s) hs hm).congr
        (Eventually.of_forall fun x => ?_)
      simp only [ldet_mul_aS, ← hc_eq, add_sub_cancel_right]
    · refine h2.congr (Eventually.of_forall fun s => ?_)
      show ∫ x, ‖w (ldet x - s * c) * L x‖ ∂D.ν = ∫ x, ‖w (ldet x) * L (x * aS E n s)‖ ∂D.ν
      rw [← integral_shift D (fun y => ‖w (ldet y - s * c) * L y‖) (fun γ y => by rw [hinv s γ y]) (aS E n s)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [ldet_mul_aS, ← hc_eq, add_sub_cancel_right]
  have swap2 : ∫ x, ∫ s : ℝ, w (ldet x) * L (x * aS E n s) ∂volume ∂D.ν =
      ∫ s : ℝ, ∫ x, w (ldet x) * L (x * aS E n s) ∂D.ν ∂volume := integral_integral_swap hF2
  have ex : ∀ x, w (ldet x) * (∫ s : ℝ, L (x * aS E n s)) = ∫ s : ℝ, w (ldet x) * L (x * aS E n s) :=
    fun x => (integral_const_mul _ _).symm
  have key : ∫ x, w (ldet x) * (∫ s : ℝ, L (x * aS E n s)) ∂D.ν = (c : ℂ)⁻¹ * ∫ x, L x ∂D.ν := by
    simp_rw [ex]
    rw [swap2]
    simp_rw [← shift32]
    rw [← swap3, I3]
  refine ⟨?_, ?_⟩
  · refine hF2.integral_prod_left.congr (Eventually.of_forall fun x => ?_)
    exact integral_const_mul (w (ldet x)) (fun s => L (x * aS E n s))
  · rw [key, ← hc_eq, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hc.ne'), one_mul]

end DiscreteGroups.T1.G

end
