import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseIsotropicFrameKillingEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfAdelicHomDecomposeIsotropicMiddleComplementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConstStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfInvariantFormIsotropicAverageNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPosIntegralHalfAdelicMatrixLeftMulEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
variable {D : D7}
theorem mt_mul'' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one'' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
end GlobalTheory.HalfAverage

namespace GlobalTheory.HalfAverage

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

variable {D : D7}

theorem res_add {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    {F G : WO V W → ℂ} (hF : ∀ x, IntegrableOn (fun y => F (isoPart V W C y + midPart V V' W B x)) 𝓨 μ)
    (hG : ∀ x, IntegrableOn (fun y => G (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) :
    res V V' W C B μ 𝓨 (F + G) = res V V' W C B μ 𝓨 F + res V V' W C B μ 𝓨 G :=
  funext fun x => integral_add (hF x) (hG x)

theorem res_smul {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (a : ℂ) (F : WO V W → ℂ) : res V V' W C B μ 𝓨 (a • F) = a • res V V' W C B μ 𝓨 F :=
  funext fun x => integral_const_mul a _

theorem res_zero {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} :
    res V V' W C B μ 𝓨 (0 : WO V W → ℂ) = 0 :=
  funext fun x => integral_zero _ _

theorem heisO_add' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := (GlobalTheory.SplitScalar.heisL ψ S T w).map_add f g

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    heisO ψ S T w (0 : WO S T → ℂ) = 0 := (GlobalTheory.SplitScalar.heisL ψ S T w).map_zero

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem charTwist_eq_one_at_split : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e W g → c g = 1 := by
  intro D V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hμ c hc e he g hg
  have hψ := hω.std
  obtain ⟨K, hKC, hKB⟩ := GlobalTheory.T.exists_leftInverse_isotropicFrame_killing_embedding D V V' r C B hs
  have hR := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1
  obtain ⟨ℓ', hℓ', f₀, hf₀, hA⟩ := GlobalTheory.T.exists_halfInvariantForm_isotropicAverage_ne_zero D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he
  have hth : ∀ {f : WO V W → ℂ}, IsThetaFunO ψ V W f → ∀ u, IsThetaFunO ψ V W (heisO ψ V W u f) :=
    fun hf u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have hee : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA]; exact he.2.1
  have hadd : ∀ u w : WO V W, IsHalf (cA D e) u → IsHalf (cA D e) w → ∀ f,
      heisO ψ V W (u + w) f = heisO ψ V W u (heisO ψ V W w f) := fun u w hu hw f =>
    GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W (GlobalTheory.SplitScalar.symplO_eq_zero V W hee hu hw) f

  have hint : ∀ f, IsThetaFunO ψ V W f → Integrable (fun t : halfMx (cA D e) W.rank r =>
      ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f))) (haarHalf (cA D e) W.rank r) := by
    intro f hf
    obtain ⟨L, Kc, hL, hKc, h0, hloc⟩ := GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he f hf
    refine Continuous.integrable_of_hasCompactSupport ?_
      (HasCompactSupport.intro hKc fun t ht => by rw [h0 t ht, map_zero])
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hn : {s : halfMx (cA D e) W.rank r | s - t ∈ L} ∈ nhds t := by
      refine IsOpen.mem_nhds (hL.preimage (continuous_id.sub continuous_const)) ?_
      show t - t ∈ L
      rw [sub_self]; exact L.zero_mem
    filter_upwards [hn] with s hs
    have h1 := hloc t (s - t) hs
    rw [show t + (s - t) = s by abel] at h1
    simp only [h1]

  let P : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {f | (∀ (t : halfMx (cA D e) W.rank r) x, IntegrableOn
          (fun y => heisO ψ V W (restEmb V W K t) f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧
        Integrable (fun t : halfMx (cA D e) W.rank r =>
          ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f))) (haarHalf (cA D e) W.rank r)}
      add_mem' := by
        rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
        refine ⟨fun t x => ?_, ?_⟩
        · rw [heisO_add']; exact (hf1 t x).add (hg1 t x)
        · refine (hf2.add hg2).congr (Filter.Eventually.of_forall fun t => ?_)
          simp only [Pi.add_apply, heisO_add', res_add (hf1 t) (hg1 t), map_add]
      zero_mem' := by
        refine ⟨fun t x => ?_, ?_⟩
        · rw [heisO_zero']; exact integrableOn_zero
        · simp only [heisO_zero', res_zero, map_zero]; exact integrable_zero _ _ _
      smul_mem' := by
        rintro a f ⟨hf1, hf2⟩
        refine ⟨fun t x => ?_, ?_⟩
        · rw [GlobalTheory.SplitScalar.heisO_smul]; exact (hf1 t x).const_mul a
        · refine (hf2.const_mul a).congr (Filter.Eventually.of_forall fun t => ?_)
          simp only [GlobalTheory.SplitScalar.heisO_smul, res_smul, map_smul, smul_eq_mul] }
  have hP : ∀ f, IsThetaFunO ψ V W f → f ∈ P := fun f hf => ⟨fun t x => (hR _ (hth hf _)).1 x, hint f hf⟩
  let ℓ₀ : P →ₗ[ℂ] ℂ :=
    { toFun := fun f => avgForm ψ V V' W C B μ 𝓨 K e ℓ' f.1
      map_add' := by
        rintro ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩
        show avgForm ψ V V' W C B μ 𝓨 K e ℓ' (f + g) = avgForm ψ V V' W C B μ 𝓨 K e ℓ' f + avgForm ψ V V' W C B μ 𝓨 K e ℓ' g
        unfold avgForm
        rw [← integral_add hf2 hg2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [heisO_add', res_add (hf1 t) (hg1 t), map_add]
      map_smul' := by
        rintro a ⟨f, hf1, hf2⟩
        show avgForm ψ V V' W C B μ 𝓨 K e ℓ' (a • f) = a • avgForm ψ V V' W C B μ 𝓨 K e ℓ' f
        unfold avgForm
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [GlobalTheory.SplitScalar.heisO_smul, res_smul, map_smul, smul_eq_mul] }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓP : ∀ f, f ∈ P → ℓ f = avgForm ψ V V' W C B μ 𝓨 K e ℓ' f := fun f hf =>
    LinearMap.congr_fun hℓ ⟨f, hf⟩

  have hsum : ∀ {p q : WO V W}, IsHalf (cA D e) p → IsHalf (cA D e) q → IsHalf (cA D e) (p + q) :=
    fun hp hq => (halfMx (cA D e) W.rank V.rank).add_mem hp hq
  have hinv : ∀ u : WO V W, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ V W f →
      ℓ (heisO ψ V W u f) = ℓ f := by
    intro u hu f hf
    rw [hℓP _ (hP _ (hth hf u)), hℓP _ (hP f hf)]
    obtain ⟨y, x, t₀, hy, hx, ht₀, rfl⟩ := GlobalTheory.T.halfAdelicHom_decompose_isotropic_middle_complement D V V' W r C B hs K hKC hKB (cA D e) u hu
    unfold avgForm
    let t₀' : halfMx (cA D e) W.rank r := ⟨t₀, ht₀⟩
    have h1 : IsHalf (cA D e) (isoPart V W C y) := isHalf_mul hy _
    have h2 : IsHalf (cA D e) (midPart V V' W B x) := isHalf_mul hx _
    have h3 : IsHalf (cA D e) (restEmb V W K t₀) := isHalf_mul ht₀ _
    have key : ∀ t : halfMx (cA D e) W.rank r,
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t)
          (heisO ψ V W (isoPart V W C y + midPart V V' W B x + restEmb V W K t₀) f))) =
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑(t + t₀')) f)) := by
      intro t
      have h4 : IsHalf (cA D e) (restEmb V W K ↑t) := isHalf_mul t.2 _
      have h5 : IsHalf (cA D e) (restEmb V W K ↑(t + t₀')) := isHalf_mul (t + t₀').2 _
      rw [← hadd _ _ h4 (hsum (hsum h1 h2) h3)]
      have e1 : restEmb V W K ↑t + (isoPart V W C y + midPart V V' W B x + restEmb V W K t₀) =
          isoPart V W C y + (midPart V V' W B x + restEmb V W K ↑(t + t₀')) := by
        rw [show ((t + t₀' : halfMx (cA D e) W.rank r) : Mx D W.rank r) = ↑t + t₀ from rfl, restEmb_add]
        abel
      rw [e1, hadd _ _ h1 (hsum h2 h5), hadd _ _ h2 h5]
      have g1 := hth hf (restEmb V W K ↑(t + t₀'))
      have g2 := hth g1 (midPart V V' W B x)
      rw [(hR _ g2).2.2.2 y, (hR _ g1).2.2.1 x]
      exact hℓ' x hx _ (hR _ g1).2.1
    rw [integral_congr_ae (Filter.Eventually.of_forall key)]
    exact integral_add_right_eq_self (fun t : halfMx (cA D e) W.rank r =>
      ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑t) f))) t₀'

  have hmi : mt W g * mt W g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  have him : mt W g⁻¹ * mt W g = 1 := by rw [← mt_mul'', inv_mul_cancel, mt_one'']
  have hdet : IsUnit (mt W g).det := Matrix.isUnit_det_of_right_inverse hmi
  set s : AE D := ((hdet.unit : (AE D)ˣ) : AE D) with hs_def
  set s' : AE D := (((hdet.unit)⁻¹ : (AE D)ˣ) : AE D) with hs'_def
  have hss : s * s' = 1 := hdet.unit.mul_inv
  have hss' : s' * s = 1 := hdet.unit.inv_mul
  have he1 : e * e = e := he.1
  let y : (AE D)ˣ := ⟨e * s + (1 - e), e * s' + (1 - e),
    by linear_combination (s * s' - s - s' + 1) * he1 + e * hss,
    by linear_combination (s' * s - s' - s + 1) * he1 + e * hss'⟩
  have hy : IsDetAt e W g y := by
    show e * s + (1 - e) = e * (mt W g).det + (1 - e)
    rw [hs_def, IsUnit.unit_spec]
  have hV1 : ∀ X : HSp D, SuppAt e X 1 := fun X i j => by
    rw [mt_one'', sub_self]; simp
  have hD1 : ∀ X : HSp D, IsDetAt e X 1 1 := fun X => by
    show (1 : AE D) = e * (mt X 1).det + (1 - e)
    rw [mt_one'', Matrix.det_one]; ring
  obtain ⟨r₁, hr₁, hsp⟩ := hω.om_split e he 1 g (hV1 V) hg 1 y (hD1 V) hy
  obtain ⟨r₂, hr₂, hsp'⟩ := hω'.om_split e he 1 g (hV1 V') hg 1 y (hD1 V') hy
  have E1 := hsp ℓ hinv f₀ hf₀
  obtain ⟨κ, hκ, hscale⟩ := GlobalTheory.T.exists_pos_integral_halfAdelicMatrix_leftMul_eq D (cA D e) W.rank r (mt W g⁻¹) (mt W g) him hmi
  have E2 : ℓ (ω (1, g) f₀) = ((c g : ℂ) * r₂ * splitFacO χS χT' 1 y * κ) * ℓ f₀ := by
    rw [hℓP _ (hP _ (hω.om_pres _ _ hf₀)), hℓP _ (hP _ hf₀)]
    unfold avgForm
    have key2 : ∀ t : halfMx (cA D e) W.rank r,
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) (ω (1, g) f₀))) =
        ((c g : ℂ) * r₂ * splitFacO χS χT' 1 y) *
          ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t)) f₀)) := by
      intro t
      have hG := hth hf₀ (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t))
      have hcomm : ω (1, g) (heisO ψ V W (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t)) f₀) =
          heisO ψ V W (restEmb V W K ↑t) (ω (1, g) f₀) := by
        rw [hω.om_heis 1 g _ f₀ hf₀]
        congr 1
        show HMul.hMul (HMul.hMul (mt W g) (HMul.hMul (HMul.hMul (mt W g⁻¹) (t : Mx D W.rank r)) (K.map (incA D))))
          (mt V 1⁻¹) = HMul.hMul (t : Mx D W.rank r) (K.map (incA D))
        rw [inv_one, mt_one'', Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hmi, Matrix.one_mul]
      rw [← hcomm, hc g _ hG, map_smul, hsp' ℓ' hℓ' _ (hR _ hG).2.1, smul_eq_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall key2), integral_const_mul,
      hscale (fun t => ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑t) f₀)))]
    ring

  have hχ : ((χS y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hL : ℓ f₀ ≠ 0 := by rw [hℓP _ (hP _ hf₀)]; exact hA
  have hsf : ∀ χ' : (AE D)ˣ →* Circle, (splitFacO χS χ' 1 y : ℂ) = (χS y : ℂ) := fun χ' => by
    simp [splitFacO]
  rw [E1, hsf, hsf] at E2
  have h1 : ((r₁ : ℂ) * (χS y : ℂ)) = (c g : ℂ) * r₂ * (χS y : ℂ) * κ := mul_right_cancel₀ hL E2
  have h2 : ((c g : ℂ) * ((r₂ : ℂ) * κ)) * (χS y : ℂ) = (r₁ : ℂ) * (χS y : ℂ) := by linear_combination -h1
  have h3 := mul_right_cancel₀ hχ h2
  have hpos : (0 : ℝ) < r₂ * κ := mul_pos hr₂ hκ
  have h4 : (c g : ℂ) = ((r₁ / (r₂ * κ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff (by exact_mod_cast hpos.ne'), h3]
  have hn : ‖(c g : ℂ)‖ = 1 := by
    first | exact Circle.norm_coe (c g) | exact Circle.abs_coe (c g) | exact mem_sphere_zero_iff_norm.1 (c g).2
  rw [h4, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr₁ hpos)] at hn
  have h5 : (c g : ℂ) = 1 := by rw [h4, hn, Complex.ofReal_one]
  exact Circle.ext (by rw [h5, Circle.coe_one])

end GlobalTheory.HalfAverage
