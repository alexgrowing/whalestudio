import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped GlobalTheory.MixModel

namespace GlobalTheory.LeviScalar

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem proj_mul_mt_inv (V V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (g' : GA D V') (m : GA D V)
    (hB : HMul.hMul (mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g')) :
    HMul.hMul ((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) (mt V m⁻¹) =
      HMul.hMul (mt V' g'⁻¹) ((V'.gram⁻¹ * adj D B * V.gram).map (incA D)) := by
  have hadj : adj D B = Bᴴ := GlobalTheory.MixModel.cT_sig B
  have hP : (V'.gram⁻¹ * adj D B * V.gram).map (incA D) =
      GlobalTheory.MixModel.giA V' * GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.gA V := by
    rw [hadj]
    change GlobalTheory.MixModel.rat (V'.gram⁻¹ * Bᴴ * V.gram) = _
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_conjTranspose]
    rfl
  have hB' : mt V m * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B * mt V' g' := hB
  have key : GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.adj (mt V m) =
      GlobalTheory.MixModel.adj (mt V' g') * GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) := by
    rw [← GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.adj_mul, hB']
  rw [hP, GlobalTheory.MixModel.mt_inv, GlobalTheory.MixModel.mt_inv]
  simp only [Matrix.mul_assoc, GlobalTheory.MixModel.gA_giA_cancel]
  rw [← Matrix.mul_assoc (GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B)), key, Matrix.mul_assoc]

theorem actO_midPart (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (g' : GA D V') (m : GA D V)
    (hB : HMul.hMul (mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g')) (h : GA D W) (x : WO V' W) :
    actO V W m h (midPart V V' W B x) = midPart V V' W B (actO V' W g' h x) := by
  have hq := proj_mul_mt_inv V V' B g' m hB
  unfold midPart
  rw [GlobalTheory.MixModel.actO_eq, GlobalTheory.MixModel.actO_eq]
  generalize (V'.gram⁻¹ * adj D B * V.gram).map (incA D) = P at hq ⊢
  simp only [Matrix.mul_assoc]
  rw [hq]

theorem actO_inv_actO (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  rw [GlobalTheory.MixModel.actO_eq, GlobalTheory.MixModel.actO_eq, inv_inv]
  simp only [Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.one_mul]

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := by
  ext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem absE_ne_zero (u : (AE D)ˣ) : GlobalTheory.Doubling.absE D.host.F D.host.E u ≠ 0 := ((Group.isUnit u).map (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero

theorem detPow_pos {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  exact Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 (absE_ne_zero _))) _

theorem enorm_inv_detPow_sq {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) :
    ‖((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n : ℂ))⁻¹‖ₑ ^ 2 *
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ n = 1 := by
  have ht : (0 : ℝ) < (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 (absE_ne_zero _))
  have hd : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := detPow_pos a n
  have hsq : (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n) ^ 2 =
      (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ n := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le, ← Real.rpow_natCast _ n]
    congr 1
    push_cast
    ring
  have hn : ‖((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n : ℂ))⁻¹‖ₑ = ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n)⁻¹ := by
    rw [← ofReal_norm_eq_enorm, norm_inv, Complex.norm_real, Real.norm_of_nonneg hd.le]
  rw [hn, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (inv_nonneg.2 hd.le),
    ← ENNReal.ofReal_pow ht.le, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hd.le) _), ← hsq, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ hd.ne'), ENNReal.ofReal_one]

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := fun hf hg => GlobalTheory.OrientedHeis.theta_add hf hg
  smul_mem' := fun c _ hf => GlobalTheory.OrientedHeis.theta_smul c hf

theorem eq_zero_of_lintegral {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0) : f = 0 := by
  apply GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hcv hf
  unfold nrm2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    (GlobalTheory.ThetaSchurBdd.integrable_sq hψ hcv.2.2 hf).aestronglyMeasurable]
  have h2 : ∫⁻ w in 𝓕, ENNReal.ofReal (‖f w‖ ^ 2) ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
    congr 1
    funext w
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rw [h2, h0, ENNReal.toReal_zero]

theorem main : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ h : GA D W, ∃ c : Circle, ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) = ((c : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)) • ω' (g', h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω' μ 𝓨 hcv a g' m hC hB h
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hres := GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hcv
  have hheis := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1
  obtain ⟨μ', 𝓕', hcv'⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V'.rank
  rw [← GlobalTheory.MixModel.ratL_eq] at hcv'

  let Θ := thetaSpace ψ V W
  let R : Θ →ₗ[ℂ] (WO V' W → ℂ) :=
    { toFun := fun f => res V V' W C B μ 𝓨 f
      map_add' := fun f g => by
        funext x
        show ∫ y in 𝓨, ((f : WO V W → ℂ) + g) (isoPart V W C y + midPart V V' W B x) ∂μ =
          (∫ y in 𝓨, (f : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ) +
            ∫ y in 𝓨, (g : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ
        simp only [Pi.add_apply]
        exact integral_add ((hres.1 f f.2).1 x) ((hres.1 g g.2).1 x)
      map_smul' := fun c f => by
        funext x
        show ∫ y in 𝓨, (c • (f : WO V W → ℂ)) (isoPart V W C y + midPart V V' W B x) ∂μ =
          c * ∫ y in 𝓨, (f : WO V W → ℂ) (isoPart V W C y + midPart V V' W B x) ∂μ
        simp only [Pi.smul_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  let Φ : Θ →ₗ[ℂ] (WO V' W → ℂ) :=
    R ∘ₗ (ω (m, h)).restrict (p := Θ) (q := Θ) (fun f hf => hω.om_pres (m, h) f hf)

  have hker : LinearMap.ker R ≤ LinearMap.ker Φ := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    have hf0 : res V V' W C B μ 𝓨 f = 0 := hf
    have hθ : IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (m, h) f)) :=
      (hres.1 _ (hω.om_pres (m, h) f f.2)).2.1
    have hsq := GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcv μ' 𝓕' hcv'.1 hcv'.2.1 a g' m hC hB h f f.2
    rw [hf0] at hsq
    simp only [Pi.zero_apply, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      MeasureTheory.lintegral_const, zero_mul, mul_zero] at hsq
    exact eq_zero_of_lintegral hψ hcv' hθ hsq

  let N₀ : LinearMap.range R →ₗ[ℂ] (WO V' W → ℂ) :=
    (LinearMap.ker R).liftQ Φ hker ∘ₗ R.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Nf, hN⟩ := LinearMap.exists_extend N₀
  have hNf : ∀ f, IsThetaFunO ψ V W f → Nf (res V V' W C B μ 𝓨 f) = res V V' W C B μ 𝓨 (ω (m, h) f) := by
    intro f hf
    let F : Θ := ⟨f, hf⟩
    have e1 : Nf (R F) = N₀ ⟨R F, LinearMap.mem_range_self R F⟩ := by
      rw [← hN]
      rfl
    show Nf (R F) = Φ F
    rw [e1]
    show (LinearMap.ker R).liftQ Φ hker (R.quotKerEquivRange.symm ⟨R F, LinearMap.mem_range_self R F⟩) = Φ F
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl

  let d : ℂ := (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)
  have hd0 : d ≠ 0 := Complex.ofReal_ne_zero.2 (detPow_pos a W.rank).ne'
  let M : Module.End ℂ (WO V' W → ℂ) := d⁻¹ • (ω' (g'⁻¹, h⁻¹) * Nf)
  have hMres : ∀ f, IsThetaFunO ψ V W f →
      M (res V V' W C B μ 𝓨 f) = d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) := by
    intro f hf
    show d⁻¹ • ω' (g'⁻¹, h⁻¹) (Nf (res V V' W C B μ 𝓨 f)) = _
    rw [hNf f hf]
  have hθω : ∀ f, IsThetaFunO ψ V W f → IsThetaFunO ψ V' W (res V V' W C B μ 𝓨 (ω (m, h) f)) :=
    fun f hf => (hres.1 _ (hω.om_pres (m, h) f hf)).2.1
  have hM1 : ∀ f', IsThetaFunO ψ V' W f' → IsThetaFunO ψ V' W (M f') := by
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    rw [hMres f hf]
    exact GlobalTheory.OrientedHeis.theta_smul _ (hω'.om_pres _ _ (hθω f hf))
  have hM2 : ∀ x f', IsThetaFunO ψ V' W f' → M (heisO ψ V' W x f') = heisO ψ V' W x (M f') := by
    intro x f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    have hx : heisO ψ V' W x (res V V' W C B μ 𝓨 f) =
        res V V' W C B μ 𝓨 (heisO ψ V W (midPart V V' W B x) f) :=
      (GlobalTheory.TowerRestrict.res_heis_mid hs μ 𝓨 f x).symm
    rw [hx, hMres _ (hheis _ _ hf), hMres f hf, hω.om_heis m h _ f hf, actO_midPart V V' W B g' m hB h x,
      GlobalTheory.TowerRestrict.res_heis_mid hs, hω'.om_heis _ _ _ _ (hθω f hf), actO_inv_actO, heisO_smul]
  have hM3 : ∀ (μ₀ : Measure (WO V' W)) (𝓕₀ : Set (WO V' W)), μ₀.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL W V') 𝓕₀ μ₀ → ∀ f', IsThetaFunO ψ V' W f' →
      ∫⁻ w in 𝓕₀, ‖M f' w‖ₑ ^ 2 ∂μ₀ = ∫⁻ w in 𝓕₀, ‖f' w‖ₑ ^ 2 ∂μ₀ := by
    intro μ₀ 𝓕₀ hH hF f' hf'
    obtain ⟨f, hf, rfl⟩ := GlobalTheory.T.theta_restriction_down_witt_tower_surjective D V V' W r C B hs ψ hψ μ 𝓨 hcv f' hf'
    rw [hMres f hf]
    have hpt : ∀ w, ‖(d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f))) w‖ₑ ^ 2 =
        ‖d⁻¹‖ₑ ^ 2 * ‖ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) w‖ₑ ^ 2 := by
      intro w
      rw [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    simp only [hpt]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top),
      hω'.om_unit μ₀ 𝓕₀ hH hF _ _ (hθω f hf),
      GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcv μ₀ 𝓕₀ hH hF a g' m hC hB h f hf,
      ← mul_assoc, enorm_inv_detPow_sq, one_mul]
  obtain ⟨c₀, hc₀, hM⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ V' W M hM1 hM2 hM3
  have hinv : ∀ X, ω' (g', h) (ω' (g'⁻¹, h⁻¹) X) = X := by
    intro X
    have e : ω' (g', h) * ω' (g'⁻¹, h⁻¹) = 1 := by
      rw [← map_mul]
      show ω' ((g', h) * (g', h)⁻¹) = 1
      rw [mul_inv_cancel, map_one]
    exact congrArg (fun L : Module.End ℂ (WO V' W → ℂ) => L X) e
  refine ⟨⟨c₀, mem_sphere_zero_iff_norm.2 hc₀⟩, fun f hf => ?_⟩
  have e2 : d⁻¹ • ω' (g'⁻¹, h⁻¹) (res V V' W C B μ 𝓨 (ω (m, h) f)) = c₀ • res V V' W C B μ 𝓨 f := by
    rw [← hMres f hf]
    exact hM _ (hres.1 f hf).2.1
  have e3 : d⁻¹ • res V V' W C B μ 𝓨 (ω (m, h) f) = c₀ • ω' (g', h) (res V V' W C B μ 𝓨 f) := by
    have e4 := congrArg (ω' (g', h)) e2
    rwa [map_smul, map_smul, hinv] at e4
  calc res V V' W C B μ 𝓨 (ω (m, h) f) = d • (d⁻¹ • res V V' W C B μ 𝓨 (ω (m, h) f)) := by
        rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
    _ = _ := by
        rw [e3, smul_smul]
        congr 1
        exact mul_comm _ _

end GlobalTheory.LeviScalar
