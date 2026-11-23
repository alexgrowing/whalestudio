import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentRadicalSurjectsUnitriangularCharactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergIntegralFourierBesselBasePointEqPairin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpecStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HandInvPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem mul_star_psi (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) : ψ x * star (ψ x) = 1 := by
  have h1 : ‖ψ x‖ = 1 := hψ.1.2.1 x
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp

theorem star_psi_neg (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) : star (ψ (-x)) = ψ x := by
  have h1 := mul_star_psi hψ (-x)
  have h2 : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  linear_combination ψ x * h1 - star (ψ (-x)) * h2

theorem om_mul {S T : HSp D} (om : Om S T) (a b : GA D S) (a' b' : GA D T) (f : WO S T → ℂ) :
    om (a * b, a' * b') f = om (a, a') (om (b, b') f) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem mixT_zero_heis {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (c : ℂ) (η : Mx D ρ S.rank) (w : WO S T₀) :
    d.mixT S ψ v.μ v.𝓕 (heisO ψ S T (d.incX S η + d.inc0 S w) (c • g)) 0 =
      c • heisO ψ S T₀ w (d.mixT S ψ v.μ v.𝓕 g 0) := by
  have hmix : ∀ (f : WO S T → ℂ) w₀, d.mixT S ψ v.μ v.𝓕 f 0 w₀ = ∫ ξ in v.𝓕, f (d.incX S ξ + d.inc0 S w₀) ∂v.μ := by
    intro f w₀
    change ∫ ξ in v.𝓕, heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S 0) (heisO ψ S T (d.inc0 S w₀) f)) 0 ∂v.μ = _
    congr 1
    funext ξ
    rw [HypDec.integrandT_eq, map_zero, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  funext w₀
  have hper : ∀ γ ∈ ratMx D ρ S.rank, ∀ ξ, g (d.incX S (γ + ξ) + d.inc0 S (w₀ + w)) = g (d.incX S ξ + d.inc0 S (w₀ + w)) := by
    intro γ hγ ξ
    have h := d.integrandT_periodic hg 0 (w₀ + w) γ hγ ξ
    rwa [HypDec.integrandT_eq, HypDec.integrandT_eq, map_zero, symplOH_zero_right, symplOH_zero_right,
      AddChar.map_zero_eq_one, one_mul, one_mul, add_zero, add_zero] at h
  rw [hmix, Pi.smul_apply, heisO, hmix, ← covolOne_integral_add v.covol (fun ξ => g (d.incX S ξ + d.inc0 S (w₀ + w))) hper η, smul_eq_mul, ← mul_assoc,
    ← integral_const_mul]
  congr 1
  funext ξ
  have e1 : symplOH S T (d.incX S ξ + d.inc0 S w₀) (d.incX S η + d.inc0 S w) = symplOH S T₀ w₀ w := by
    simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
      HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, HypDec.wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add]
    rw [symplOH_skew S T (d.incX S _) (d.inc0 S _), HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, neg_zero, zero_add]
  have e2 : d.incX S ξ + d.inc0 S w₀ + (d.incX S η + d.inc0 S w) = d.incX S (ξ + η) + d.inc0 S (w₀ + w) := by
    rw [map_add, map_add]; abel
  rw [heisO, e1, e2, Pi.smul_apply, smul_eq_mul]
  ring

theorem fourierBessel_centralTerm_const_on_orbit {σ : ℕ} (B : BesLev D σ) {S S₀ : HSp D} (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1))
    (v : UX D (σ + 1)) : d.qS B.V c (x0 B ⬝ v.1.1) = d.qS B.L c (zl B) := by
  obtain ⟨-, -, -, -, -, h⟩ := GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec D σ B
  obtain ⟨n, -, hn, -⟩ := (GlobalTheory.T.flagUnipotentRadical_surjects_unitriangular_characters_agree D σ B).1 v
  rw [← h S S₀ d c, ← cenS_nC, ← cenS_nC, ← neg_inj, LinkPoint.neg_cenS_eq, LinkPoint.neg_cenS_eq, ← hn,
    GlobalTheory.MixPer.Decomp.gram_mt]

set_option maxHeartbeats 1000000 in

theorem flatFB_source {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) {Ψ : WO J.W B.V → ℂ}
    (hΨ : IsThetaFunO ψ J.W B.V Ψ) {n : GA D J.W} (hn : n ∈ flagN J.d) :
    flatFB s (s.om (n, 1) Ψ) = (psiFlag ψ J.d n * ψ (cenS J.d B.L (zl B) n)) •
      heisO ψ J.W₀ B.V₀ ((B.o.resT J.W₀).symm (0, ptS J.d B.L (zl B) n)) (flatFB s Ψ) := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp J.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hz : ∀ u ∈ UX D (σ + 1), zl B ⬝ u.1 = zl B := fun u hu => zEll_mul B.L B.ζ hu
  have hx : J.d.extX B.L (zl B) ⬝ mt J.W (J.d.levi u * (J.d.nB b * J.d.nC c)) =
      J.d.extX B.L (zl B) ⬝ mt J.W (J.d.nB b * J.d.nC c) := by
    rw [mt_mul, ← Matrix.mul_assoc, J.d.extX_levi, hz u hu]
  have hpt : ptS J.d B.L (zl B) (J.d.levi u * (J.d.nB b * J.d.nC c)) = zl B ⬝ b := by
    rw [← ptS_nB_mul_nC J.d B.L (zl B) b c, ptS, ptS, hx]
  have hcen : cenS J.d B.L (zl B) (J.d.levi u * (J.d.nB b * J.d.nC c)) = J.d.qS B.L c (zl B) := by
    rw [← (GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zl B) hz).1 b c, cenS, cenS, hx]
  have hfl : psiFlag ψ J.d (J.d.levi u * (J.d.nB b * J.d.nC c)) = psiUni ψ u :=
    psiFlag_levi_mul ψ J.d u (radX_le_stabX J.d (mul_mem (nB_mem_radX J.d b) (nC_mem_radX J.d c)))
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod B.V.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (J.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (J.d.nB b, 1) _ h1
  have e : s.om (J.d.levi u * (J.d.nB b * J.d.nC c), 1) Ψ =
      s.om (J.d.levi u, 1) (s.om (J.d.nB b, 1) (s.om (J.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D (σ + 1) := ⟨u, hu⟩
  have key : ∀ v : UX D (σ + 1),
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (J.d.levi u * (J.d.nB b * J.d.nC c), 1) Ψ) (x0 B ⬝ v.1.1) 0 =
        ψ (J.d.qS B.L c (zl B)) • heisO ψ J.W₀ B.V₀ ((B.o.resT J.W₀).symm (0, zl B ⬝ b))
          (evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ (v * u').1.1) 0) := by
    intro v
    have ex : x0 B ⬝ v.1.1 ⬝ u.1 = x0 B ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have ez : zl B ⬝ ((v * u').1.1 ⬝ b) = zl B ⬝ b := by rw [← Matrix.mul_assoc, hz _ (v * u').2]
    have t1 := (FS _ h2).levi u (x0 B ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (x0 B ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (x0 B), fourierBesselBasePoint_mul_eq, ez] at t2
    have t3 : J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.nC c, 1) Ψ) (x0 B ⬝ (v * u').1.1) =
        ψ (J.d.qS B.V c (x0 B ⬝ (v * u').1.1)) • J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [fourierBessel_centralTerm_const_on_orbit] at t3
    unfold evalAt
    rw [e, t1, t2, t3]
    exact mixT_zero_heis B.d s.vT (MV _) _ _ _
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D (σ + 1)
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D (σ + 1)).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D (σ + 1), psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  funext w
  rw [hpt, hcen, hfl]
  simp only [Pi.smul_apply, smul_eq_mul, heisO]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (J.d.levi u * (J.d.nB b * J.d.nC c), 1) Ψ) (x0 B ⬝ v.1.1) 0 w ∂s.vU.ν = _ * (_ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ v.1.1) 0 _ ∂s.vU.ν)
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← mul_assoc, ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul, heisO]
  generalize evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (x0 B ⬝ (v * u').1.1) 0 _ = z
  generalize ψ (symplOH J.W₀ B.V₀ w _) = y
  linear_combination (-(star (psiUni ψ v.1) * ψ (J.d.qS B.L c (zl B)) * y * z)) * hu1

theorem handBF_heis {ρ σ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} {B' : BesLev D σ} (s : StepBF ψ B J)
    (l : Link B B'.L B'.ζ) (φ : GA D B.A → ℂ) {Ξ : WO B.V₀ J.W₀ → ℂ} (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (a : ℂ)
    (p : WO J.W₀ B'.L) (h h₀ : GA D J.W₀) (w : WO J.W₀ B'.L) :
    handBF s l φ (a • heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p)) (s.om₀ (1, h) Ξ)) h₀ w =
      star a * ψ (symplOH J.W₀ B'.L w (p ⬝ mt J.W₀ h₀⁻¹)) * handBF s l φ Ξ (h₀ * h) (w + p ⬝ mt J.W₀ h₀⁻¹) := by
  have hψ := s.weil.std
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  have hκ := (GlobalTheory.LinkKappa.kappa_props D B.L B'.L J.W₀ l.τ 1 hτ (l.κ J.W₀) (fun _ => rfl)).2.2.2.1 h₀ p
  have hact : ∀ x : GA D B.A, actO B.V₀ J.W₀ (B.o.emb (x, 1)) h₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p)) =
      (B.o.resS J.W₀).symm (0, l.κ J.W₀ (p ⬝ mt J.W₀ h₀⁻¹)) := fun x => by
    apply (B.o.resS J.W₀).injective
    rw [B.o.resS_actO, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hκ]
    simp only [actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul]
  have key : ∀ x : GA D B.A, s.om₀ (B.o.emb (x, 1), h₀)
      (a • heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p)) (s.om₀ (1, h) Ξ))
      ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = a * ψ (-symplOH J.W₀ B'.L w (p ⬝ mt J.W₀ h₀⁻¹)) *
        s.om₀ (B.o.emb (x, 1), h₀ * h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (w + p ⬝ mt J.W₀ h₀⁻¹))) := fun x => by
    rw [map_smul, s.weil₀.om_heis _ _ _ _ (s.weil₀.om_pres _ _ hΞ), hact, ← om_mul, mul_one, Pi.smul_apply, smul_eq_mul,
      heisO, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add,
      ContrHeis.symplOH_kappa, ← map_add, Prod.mk_add_mk, add_zero, ← ContrHeis.kappa_add, mul_assoc]
  unfold handBF
  simp only [key]
  rw [← star_psi_neg hψ (symplOH J.W₀ B'.L w (p ⬝ mt J.W₀ h₀⁻¹)), ← star_mul', ← star_mul', ← integral_const_mul]
  congr 2
  funext x
  ring

theorem pairKer_heis {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) {Y Y' : GA D J.W₀ → WO J.W₀ B.L → ℂ} (hY : IsQuasiFam ψ J.W₀ B.L Y)
    {Ξ : WO J.W₀ B.V₀ → ℂ} (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (a b : ℂ) (hab : a * b = 1) (p : WO J.W₀ B.L) (h : GA D J.W₀)
    (hY' : ∀ h₀ w, Y' h₀ w =
      star a * ψ (symplOH J.W₀ B.L w (p ⬝ mt J.W₀ h₀⁻¹)) * Y (h₀ * h) (w + p ⬝ mt J.W₀ h₀⁻¹))
    (h₀ : GA D J.W₀) (x : GA D B.A) :
    pairKer s vL Y' (b • heisO ψ J.W₀ B.V₀ ((B.o.resT J.W₀).symm (0, p)) (s.om₀ (h, 1) Ξ)) h₀ x =
      pairKer s vL Y Ξ (h₀ * h) x := by
  have hψ := s.weil.std
  have hT : ∀ c d : WO J.W₀ B.L, symplOH J.W₀ B.V₀ ((B.o.resT J.W₀).symm (0, c)) ((B.o.resT J.W₀).symm (0, d)) =
      symplOH J.W₀ B.L c d := by
    intro c d
    rw [B.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]
  have hact : actO J.W₀ B.V₀ h₀ (B.o.emb (x, 1)) ((B.o.resT J.W₀).symm (0, p)) =
      (B.o.resT J.W₀).symm (0, p ⬝ mt J.W₀ h₀⁻¹) := by
    apply (B.o.resT J.W₀).injective
    rw [B.o.resT_actO, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    simp only [actO_eq, mt_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
  have hF := s.weil₀.om_pres (h₀ * h, B.o.emb (x, 1)) Ξ hΞ
  have e : s.om₀ (h₀, B.o.emb (x, 1)) (b • heisO ψ J.W₀ B.V₀ ((B.o.resT J.W₀).symm (0, p)) (s.om₀ (h, 1) Ξ)) =
      b • heisO ψ J.W₀ B.V₀ ((B.o.resT J.W₀).symm (0, p ⬝ mt J.W₀ h₀⁻¹)) (s.om₀ (h₀ * h, B.o.emb (x, 1)) Ξ) := by
    rw [map_smul, s.weil₀.om_heis _ _ _ _ (s.weil₀.om_pres _ _ hΞ), hact, ← om_mul, mul_one]
  unfold pairKer
  rw [e]
  generalize s.om₀ (h₀ * h, B.o.emb (x, 1)) Ξ = F at hF
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ w,
      F ((B.o.resT J.W₀).symm (0, γ + w)) * star (Y (h₀ * h) (γ + w)) =
        F ((B.o.resT J.W₀).symm (0, w)) * star (Y (h₀ * h) w) := by
    intro γ hγ w
    have r2 : (B.o.resT J.W₀).symm (0, γ) ∈ ratMx D B.V₀.rank J.W₀.rank := by
      refine (B.o.mem_ratL_resT J.W₀ _).2 ?_
      rw [AddEquiv.apply_symm_apply]
      exact ⟨zero_mem _, hγ⟩
    obtain ⟨γ₂, hγ₂⟩ := r2
    obtain ⟨γ₁, hγ₁⟩ := hγ
    have q2 := hF.quasi γ₂ ((B.o.resT J.W₀).symm (0, w))
    have q1 := hY.quasi (h₀ * h) γ₁ w
    have e2 : ratW B.V₀ J.W₀ γ₂ = (B.o.resT J.W₀).symm (0, γ) := hγ₂
    have e1 : ratW B.L J.W₀ γ₁ = γ := hγ₁
    rw [e2, ← map_add, Prod.mk_add_mk, zero_add, hT] at q2
    rw [e1] at q1
    rw [q2, q1, star_mul', mul_mul_mul_comm, mul_star_psi hψ, one_mul]
  simp only [contractT, thPair]
  rw [← covolOne_integral_add vL.covol (fun w => F ((B.o.resT J.W₀).symm (0, w)) * star (Y (h₀ * h) w)) hper
    (p ⬝ mt J.W₀ h₀⁻¹)]
  congr 1
  funext w
  rw [hY', Pi.smul_apply, smul_eq_mul, heisO, hT, ← map_add, Prod.mk_add_mk, add_zero, star_mul', star_mul', star_star]
  have h1 := mul_star_psi hψ (symplOH J.W₀ B.L w (p ⬝ mt J.W₀ h₀⁻¹))
  generalize F _ = z
  generalize star (Y _ _) = y
  generalize star (ψ (symplOH J.W₀ B.L w (p ⬝ mt J.W₀ h₀⁻¹))) = t' at h1 ⊢
  generalize ψ (symplOH J.W₀ B.L w (p ⬝ mt J.W₀ h₀⁻¹)) = t at h1 ⊢
  linear_combination (a * b * z * y) * h1 + (z * y) * hab

theorem handFB_smul_om {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h, 1)) Ξ) = c • rTrans h (handFB s vL Y Ξ) := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rTrans]
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (x, 1)) (c • s.om₀ (1, B.o.emb (h, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (x * h, 1)) Ξ := by
    rw [map_smul, ← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, mul_one]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem per_flag {ρ : ℕ} (B : BesLev D ρ) (hψ : IsStdChar D ψ (-1)) (φ : GA D B.A → ℂ) {f : GA D B.V → ℂ}
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    B.per ψ (star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • φ) (rTrans n f) = B.per ψ φ f := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  have := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ B.vN.ν u2 (by rw [u3]; exact one_ne_zero)
    (by rw [u3]; exact ENNReal.one_ne_top)
  unfold BesLev.per besPer
  congr 1
  funext h
  have hK : ∀ γ' ∈ NFlagQ B.V B.d.e, ∀ m : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ' * m) = besFun ψ 1 B.d B.o B.ζ φ f h m := fun γ' hγ' m => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 m.2, GlobalTheory.CharLaws.psiBes_rat ψ B.d hψ.1.2.2.1 1 _ hγ'Q, one_mul,
      mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  have hm := GlobalTheory.CharLaws.embA_conj_mem B.d B.o h hn
  rw [← (GlobalTheory.fundamentalDomain_integral_mul_right B.vN.ν _ _ _ (⟨_, hm⟩ : flagN B.d) u2 hK).2]
  congr 1
  funext m
  simp only [besFun, Subgroup.coe_mul, rTrans, Pi.smul_apply, smul_eq_mul]
  rw [psiBes_mul B.d ψ 1 _ m.2 hm, GlobalTheory.CharLaws.psiBes_conj, star_mul', mul_assoc (m : GA D B.V) (_ * _ * _),
    inv_mul_cancel_right, mul_assoc (m : GA D B.V)]
  ring

theorem handInv : ∀ D : D7, GlobalTheory.FinPl.HandInv D := by
  intro D ψ σ B J B' s₁ s₂ l vL Φ₁ Φ₂ hΦ₁ hΦ₂ φ hφ g h₁ h₂
  have hψ := s₁.weil.std
  have hD : Descent D := GlobalTheory.Desc.weil_data_descend D
  have hth := GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ
  have hΨ₁ := s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁
  have hΨ₂ := s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂
  have hΞ₁ := hth.1 _ B J s₁ _ hΨ₁
  have hΞ₂ := hth.2 _ J B' s₂ _ hΨ₂
  have hY := GlobalTheory.HandFam.handBF_isQuasiFam D ψ _ B J s₁ B'.L B'.ζ B'.line l φ _ hφ hΞ₁
  refine ⟨fun r hr => ?_, fun G hG r hr => ?_⟩
  · obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hr
    obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s₁.χV s₁.χW s₁.om s₁.weil).1 B.V₀ _ B.d
    obtain ⟨hp, hc⟩ := LinkPoint.link_point D (σ + 1) (σ + 1) B B'.L B'.ζ B'.line l J.W J.W₀ J.d n hn
    have hp' : ptT J.d B.V₀ (yZero B.V₀ (σ + 1) (vecB B.o B.ζ)) n =
        (B.o.resS J.W₀).symm (0, l.κ J.W₀ (ptS J.d B'.L (zl B') n)) := by
      rw [zl, hp, ← ptT_yZero_vecB B.o J.d B.ζ n, AddEquiv.symm_apply_apply]
    have e1 : flatBF s₁ (s₁.om (g, n * J.d.emb0 h * h₁) Φ₁) =
        (star (psiFlag ψ J.d n) * ψ (-cenS J.d B'.L (zl B') n)) • heisO ψ B.V₀ J.W₀
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (ptS J.d B'.L (zl B') n)))
          (s₁.om₀ (1, h) (flatBF s₁ (s₁.om (g, h₁) Φ₁))) := by
      have e := GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ _ B J s₁ om' hom' _ hΨ₁ 1 n hn h
      have a1 : embA B.d B.o 1 = 1 := map_one _
      have a2 : B.o.emb (1, 1) = 1 := map_one _
      rw [a1, a2, ← om_mul, one_mul, show s₁.om₀ (1, 1) = 1 from map_one _, Module.End.one_apply, opA, jacT,
        cenT_yZero_vecB, hc, hp', smul_smul] at e
      exact e
    have e2 : flatFB s₂ (s₂.om (n * J.d.emb0 h * h₁, h₂) Φ₂) =
        (psiFlag ψ J.d n * ψ (cenS J.d B'.L (zl B') n)) • heisO ψ J.W₀ B'.V₀
          ((B'.o.resT J.W₀).symm (0, ptS J.d B'.L (zl B') n)) (s₂.om₀ (h, 1) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))) := by
      have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B' s₂ _ hΨ₂ h 1
      have a1 : embA B'.d B'.o 1 = 1 := map_one _
      have a2 : B'.o.emb (1, 1) = 1 := map_one _
      rw [a1, a2] at c
      rw [← c, ← flatFB_source s₂ (s₂.weil.om_pres _ _ hΨ₂) hn, ← om_mul, ← om_mul, one_mul, one_mul]
    have hab : star (psiFlag ψ J.d n) * ψ (-cenS J.d B'.L (zl B') n) *
        (psiFlag ψ J.d n * ψ (cenS J.d B'.L (zl B') n)) = 1 := by
      have b1 : psiFlag ψ J.d n * star (psiFlag ψ J.d n) = 1 := mul_star_psi hψ _
      rw [mul_mul_mul_comm, mul_comm (star _), b1, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
    funext x
    unfold Chain.hand handFB
    rw [e1, e2]
    have k := pairKer_heis s₂ vL hY hΞ₂ _ _ hab (ptS J.d B'.L (zl B') n) h
      (fun h₀ w => handBF_heis s₁ l φ hΞ₁ _ (ptS J.d B'.L (zl B') n) h h₀ w)
    simp only [k]
    exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D J.W₀ J.v0.μ J.v0.𝓕 J.v0.haar J.v0.fund
      (fun h₀ => pairKer s₂ vL _ _ h₀ x)
      (fun γ hγ h₀ => (GlobalTheory.PairKer.pairKer_law D ψ σ J B' s₂ vL _ _ hY hΞ₂).2.1 γ hγ h₀ x) h
  · obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B'.d B'.o r).1 hr
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B'.V
    have e : flatFB s₂ (s₂.om (h₁, n * embA B'.d B'.o h * h₂) Φ₂) = star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) •
        s₂.om₀ (1, B'.o.emb (h, 1)) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := by
      have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B' s₂ _ hΨ₂ 1 h
      rw [map_one] at c
      rw [← c, ← GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B' s₂ _ (s₂.weil.om_pres _ _ hΨ₂) n hn, ← om_mul, ← om_mul, one_mul, one_mul]
    have hG' : IsContAut B'.V (rTrans h₂ G) :=
      ⟨fun γ hγ x => by rw [rTrans, rTrans, mul_assoc, hG.1 γ hγ], hG.2.comp (continuous_mul_const h₂)⟩
    have eG : rTrans (n * embA B'.d B'.o h * h₂) G = rTrans n (rTrans (embA B'.d B'.o h) (rTrans h₂ G)) := by
      funext x
      simp only [rTrans, mul_assoc]
    unfold Chain.hand
    rw [e, handFB_smul_om, eG, per_flag B' hψ _ (fun γ hγ x => by simp only [rTrans, mul_assoc, hG.1 γ hγ]) hn]
    exact GlobalTheory.Core.Mi.per_rTrans D ψ σ B' _ _ h hψ (GlobalTheory.handFBLaw D ψ σ J B' s₂ vL _ _ hY hΞ₂) hG'

end GlobalTheory.FinPl.HandInvPf

end
