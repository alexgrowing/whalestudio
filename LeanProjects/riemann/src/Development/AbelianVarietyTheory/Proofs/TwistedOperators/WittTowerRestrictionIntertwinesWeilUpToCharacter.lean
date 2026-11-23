import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaarStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedThetaCoefficientEqIsotropicIntegralStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerRestrictScalar

theorem integral_unitary_mul : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)), ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ, ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν = ∫ y, Φ y ∂ν :=
  GlobalTheory.T.integral_leftMul_unitaryMatrix_addHaar

theorem coef_unfold : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν :=
  GlobalTheory.T.restrictedTheta_coefficient_eq_isotropic_integral

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_fd (S T : HSp D) :
    ∃ (m : Measure (WO S T)) (F : Set (WO S T)), m.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) F m := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

theorem integrable_prod (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    Integrable (fun x => f x * star (g x)) (μ.restrict 𝓕) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  have hcont : Continuous fun x => f x * star (g x) := hf.cont.mul hg.cont.star
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hf hg hγ w]
  exact hC _ h

theorem heisO_smul (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mt_one' (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem mt_mul' (S : HSp D) (h k : GA D S) :
    Formalism.L2.Theta.mt S (h * k) = Formalism.L2.Theta.mt S h * Formalism.L2.Theta.mt S k := by
  simp [Formalism.L2.Theta.mt]

theorem actO_one_mul (S T : HSp D) (h k : GA D T) (x : WO S T) :
    actO S T 1 h (actO S T 1 k x) = actO S T 1 (h * k) x := by
  simp [actO, mt_one', mt_mul', Matrix.mul_assoc]

theorem actO_one_one (S T : HSp D) (x : WO S T) : actO S T 1 1 x = x := by
  simp [actO, mt_one']

theorem actO_iso_mid (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (k : GA D W) (y : Mx D W.rank r) (x : WO V' W) :
    actO V W 1 k (isoPart V W C y + midPart V V' W B x) =
      isoPart V W C (HMul.hMul (Formalism.L2.Theta.mt W k) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) +
        midPart V V' W B (actO V' W 1 k x) := by
  simp [actO, isoPart, midPart, mt_one', Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem move (S T : HSp D) {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hω : IsWeilDatumO ψ S T χS χT ω) (h : GA D T) (w : WO S T) (P : WO S T → ℂ) (hP : IsThetaFunO ψ S T P) :
    heisO ψ S T w (ω (1, h) P) = ω (1, h) (heisO ψ S T (actO S T 1 h⁻¹ w) P) := by
  rw [hω.om_heis 1 h _ P hP, actO_one_mul, mul_inv_cancel, actO_one_one]

theorem inv_apply (S T : HSp D) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D T)
    (z : WO S T → ℂ) : ω (1, h⁻¹) (ω (1, h) z) = z := by
  have e : ((1 : GA D S), h⁻¹) * ((1 : GA D S), h) = 1 := Prod.ext (by simp) (by simp)
  rw [← Module.End.mul_apply, ← map_mul, e, map_one, Module.End.one_apply]

theorem per_h {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {χS χT χS' χT' : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω)
    (hω' : IsWeilDatumO ψ V' W χS' χT' ω') {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) (h : GA D W) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (1, h) f) = c • ω' (1, h) (res V V' W C B μ 𝓨 f) := by
  have hψ := hω.std
  obtain ⟨hR, f₀, hf₀, hR0⟩ := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ
  have thV := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1
  have thV' := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V' W).1
  obtain ⟨μV, 𝓕V, hμV, h𝓕V⟩ := exists_fd (D := D) V W
  obtain ⟨μ', 𝓕', hμ', h𝓕'⟩ := exists_fd (D := D) V' W
  obtain ⟨ν, hν, hMC⟩ := coef_unfold D V V' W r C B hs ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕'
  have hU : ∀ P Q, IsThetaFunO ψ V W P → IsThetaFunO ψ V W Q →
      ∫ w in 𝓕V, ω (1, h) P w * star (ω (1, h) Q w) ∂μV = ∫ w in 𝓕V, P w * star (Q w) ∂μV :=
    fun P Q hP hQ => GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ V W μV 𝓕V hμV h𝓕V (ω (1, h)) (hω.om_pres _)
      (hω.om_unit μV 𝓕V hμV h𝓕V _) P Q hP hQ
  have hU' : ∀ P Q, IsThetaFunO ψ V' W P → IsThetaFunO ψ V' W Q →
      ∫ w in 𝓕', ω' (1, h) P w * star (ω' (1, h) Q w) ∂μ' = ∫ w in 𝓕', P w * star (Q w) ∂μ' :=
    fun P Q hP hQ => GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ V' W μ' 𝓕' hμ' h𝓕' (ω' (1, h)) (hω'.om_pres _)
      (hω'.om_unit μ' 𝓕' hμ' h𝓕' _) P Q hP hQ

  have hpair : ∀ f g, IsThetaFunO ψ V W f → IsThetaFunO ψ V W g → ∀ x : WO V' W,
      ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 (ω (1, h) f)) w *
          star (res V V' W C B μ 𝓨 (ω (1, h) g) w) ∂μ' =
        ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f)) w *
          star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' := by
    intro f g hf hg x
    have hf1 := hω.om_pres (1, h) f hf
    have hg1 := hω.om_pres (1, h) g hg
    have hRf := (hR f hf).2.1
    have hRg := (hR g hg).2.1
    calc _ = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) (ω (1, h) f) w *
            star (ω (1, h) g w) ∂μV) ∂ν := hMC _ _ hf1 hg1 x
      _ = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹)
              (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) +
              midPart V V' W B (actO V' W 1 h⁻¹ x)) f w * star (g w) ∂μV) ∂ν := by
          refine congrArg (fun Φ : Mx D W.rank r → ℂ => ∫ y, Φ y ∂ν) (funext fun y => ?_)
          rw [move V W hω h _ f hf, actO_iso_mid, hU _ _ (thV _ f hf) hg]
      _ = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B (actO V' W 1 h⁻¹ x)) f w *
            star (g w) ∂μV) ∂ν :=
          integral_unitary_mul D W r h⁻¹ ν hν (fun y => ∫ w in 𝓕V, heisO ψ V W
            (isoPart V W C y + midPart V V' W B (actO V' W 1 h⁻¹ x)) f w * star (g w) ∂μV)
      _ = ∫ w in 𝓕', heisO ψ V' W (actO V' W 1 h⁻¹ x) (res V V' W C B μ 𝓨 f) w *
            star (res V V' W C B μ 𝓨 g w) ∂μ' := (hMC f g hf hg _).symm
      _ = ∫ w in 𝓕', ω' (1, h) (heisO ψ V' W (actO V' W 1 h⁻¹ x) (res V V' W C B μ 𝓨 f)) w *
            star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' := (hU' _ _ (thV' _ _ hRf) hRg).symm
      _ = _ := by rw [move V' W hω' h x _ hRf]
  have hcoef : ∀ f, IsThetaFunO ψ V W f → ∃ c : ℂ, ‖c‖ = 1 ∧
      res V V' W C B μ 𝓨 (ω (1, h) f) = c • ω' (1, h) (res V V' W C B μ 𝓨 f) := fun f hf =>
    GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq D ψ hψ V' W μ' 𝓕' hμ' h𝓕'
      (ω' (1, h) (res V V' W C B μ 𝓨 f)) (res V V' W C B μ 𝓨 (ω (1, h) f))
      (hω'.om_pres _ _ (hR f hf).2.1) (hR _ (hω.om_pres _ f hf)).2.1 (fun w => hpair f f hf hf w)
  have hv0t : IsThetaFunO ψ V' W (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) := hω'.om_pres _ _ (hR f₀ hf₀).2.1
  have hv0 : ω' (1, h) (res V V' W C B μ 𝓨 f₀) ≠ 0 := fun h0 => hR0 (by
    rw [← inv_apply V' W ω' h (res V V' W C B μ 𝓨 f₀), h0, map_zero])
  obtain ⟨c, hc, hu0⟩ := hcoef f₀ hf₀
  have hdiag : ∃ x, ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
      star (ω' (1, h) (res V V' W C B μ 𝓨 f₀) w) ∂μ' ≠ 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨c', -, h'⟩ := GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq D ψ hψ V' W μ' 𝓕' hμ' h𝓕'
      0 (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) GlobalTheory.WeilVacMove.isTheta_zero hv0t (fun w => by
        rw [hne w]
        simp [heisO])
    exact hv0 (by rw [h', smul_zero])
  have hA : ∀ g, IsThetaFunO ψ V W g → (∃ x, ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
      star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' ≠ 0) →
      res V V' W C B μ 𝓨 (ω (1, h) g) = c • ω' (1, h) (res V V' W C B μ 𝓨 g) := by
    rintro g hg ⟨x, hx⟩
    obtain ⟨cg, hcg, hug⟩ := hcoef g hg
    have e := hpair f₀ g hf₀ hg x
    rw [hu0, hug, heisO_smul] at e
    have e2 : (∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
        star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ') * (c * star cg) =
        (∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
        star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ') * 1 := by
      rw [mul_one, ← integral_mul_const]
      refine Eq.trans ?_ e
      refine congrArg (fun Φ : WO V' W → ℂ => ∫ w in 𝓕', Φ w ∂μ') (funext fun w => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, star_mul']
      ring
    have e3 : c * star cg = 1 := mul_left_cancel₀ hx e2
    have hcg2 : cg * star cg = 1 := by
      rw [Complex.star_def, Complex.mul_conj', hcg]
      simp
    have : cg = c := by
      calc cg = cg * (c * star cg) := by rw [e3, mul_one]
        _ = c * (cg * star cg) := by ring
        _ = c := by rw [hcg2, mul_one]
    rw [hug, this]
  refine ⟨c, hc, fun g hg => ?_⟩
  by_cases hx : ∃ x, ∫ w in 𝓕', heisO ψ V' W x (ω' (1, h) (res V V' W C B μ 𝓨 f₀)) w *
      star (ω' (1, h) (res V V' W C B μ 𝓨 g) w) ∂μ' ≠ 0
  · exact hA g hg hx
  · push_neg at hx
    obtain ⟨x₁, hx₁⟩ := hdiag
    have hRadd : ∀ a b, IsThetaFunO ψ V W a → IsThetaFunO ψ V W b →
        res V V' W C B μ 𝓨 (a + b) = res V V' W C B μ 𝓨 a + res V V' W C B μ 𝓨 b := fun a b ha hb => by
      funext z
      simp only [res, Pi.add_apply]
      exact integral_add ((hR a ha).1 z) ((hR b hb).1 z)
    have hv' : ω' (1, h) (res V V' W C B μ 𝓨 (f₀ + g)) =
        ω' (1, h) (res V V' W C B μ 𝓨 f₀) + ω' (1, h) (res V V' W C B μ 𝓨 g) := by
      rw [hRadd _ _ hf₀ hg, map_add]
    have hu' : res V V' W C B μ 𝓨 (ω (1, h) (f₀ + g)) =
        res V V' W C B μ 𝓨 (ω (1, h) f₀) + res V V' W C B μ 𝓨 (ω (1, h) g) := by
      rw [map_add, hRadd _ _ (hω.om_pres _ _ hf₀) (hω.om_pres _ _ hg)]
    have hvg : IsThetaFunO ψ V' W (ω' (1, h) (res V V' W C B μ 𝓨 g)) := hω'.om_pres _ _ (hR g hg).2.1
    have key := hA (f₀ + g) (GlobalTheory.WeilVacMove.isTheta_add hf₀ hg) ⟨x₁, by
      rw [hv']
      simp only [Pi.add_apply, star_add, mul_add]
      rw [integral_add (integrable_prod hψ μ' 𝓕' hμ' h𝓕' (thV' x₁ _ hv0t) hv0t)
        (integrable_prod hψ μ' 𝓕' hμ' h𝓕' (thV' x₁ _ hv0t) hvg), hx x₁, add_zero]
      exact hx₁⟩
    rw [hu', hv', hu0, smul_add] at key
    exact add_left_cancel key

theorem main : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ c : GA D W →* Circle, ∀ h f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT χS' χT' ω ω' hω hω' μ 𝓨 hμ
  have P := fun h => per_h hs hω hω' hμ h
  obtain ⟨-, f₀, hf₀, hR0⟩ := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hω.std μ 𝓨 hμ
  let c : GA D W → ℂ := fun h => Classical.choose (P h)
  have hc1 : ∀ h, ‖c h‖ = 1 := fun h => (Classical.choose_spec (P h)).1
  have hc : ∀ h f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (1, h) f) = c h • ω' (1, h) (res V V' W C B μ 𝓨 f) :=
    fun h => (Classical.choose_spec (P h)).2
  have uniq : ∀ h (a b : ℂ), a • ω' (1, h) (res V V' W C B μ 𝓨 f₀) = b • ω' (1, h) (res V V' W C B μ 𝓨 f₀) →
      a = b := fun h a b e => by
    by_contra hab
    have hz : (a - b) • ω' (1, h) (res V V' W C B μ 𝓨 f₀) = 0 := by rw [sub_smul, e, sub_self]
    rcases smul_eq_zero.1 hz with h1 | h1
    · exact hab (sub_eq_zero.1 h1)
    · exact hR0 (by rw [← inv_apply V' W ω' h (res V V' W C B μ 𝓨 f₀), h1, map_zero])
  let cc : GA D W → Circle := fun h => ⟨c h, by simp [Submonoid.unitSphere, hc1 h]⟩
  have hcc : ∀ h, ((cc h : Circle) : ℂ) = c h := fun h => rfl
  refine ⟨{ toFun := cc, map_one' := ?_, map_mul' := ?_ }, fun h f hf => ?_⟩
  · apply Circle.ext
    rw [hcc, Circle.coe_one]
    apply uniq 1
    rw [← hc 1 f₀ hf₀, one_smul]
    show res V V' W C B μ 𝓨 (ω 1 f₀) = ω' 1 (res V V' W C B μ 𝓨 f₀)
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply]
  · intro h k
    apply Circle.ext
    rw [hcc, Circle.coe_mul, hcc, hcc]
    apply uniq (h * k)
    have e1 : ω (1, h * k) = ω (1, h) * ω (1, k) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
    have e1' : ω' (1, h * k) = ω' (1, h) * ω' (1, k) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [← hc (h * k) f₀ hf₀, e1, Module.End.mul_apply, hc h _ (hω.om_pres _ _ hf₀), hc k _ hf₀, map_smul,
      smul_smul, e1', Module.End.mul_apply]
  · exact hc h f hf

end GlobalTheory.TowerRestrictScalar
