import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForallStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAllStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliserStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB GlobalTheory.FinPl GlobalTheory.FinPl.HandInvPf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowOneCos

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

set_option maxHeartbeats 1000000 in

theorem flatBF_source {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    ∃ c : ℂ, c ≠ 0 ∧ flatBF s (s.om (n, 1) Ψ) = c • flatBF s Ψ := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp B.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (B.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (B.d.nB b, 1) _ h1
  have e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ =
      s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D ρ := ⟨u, hu⟩
  have hq : ∀ X : Mx D ρ ρ, B.d.qS J.W c (xZero J.d ⬝ X) = 0 := fun X => by
    have h0 : adj J.d.jX ⬝ (gA J.W ⬝ (J.d.jX ⬝ X)) = 0 := by
      rw [← Matrix.mul_assoc, ← J.d.pY_eq, ← Matrix.mul_assoc, J.d.pY_jX, Matrix.zero_mul]
    rw [HypDec.qS, HypDec.symplOH_extX_extY, pairS, xZero, adj_mul, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, h0,
      Matrix.mul_zero, Matrix.mul_zero, trace_zero, map_zero]
  set y := yZero B.V₀ ρ (vecB B.o B.ζ) with hy
  set k : ℂ := ψ (Algebra.trace (AF D.host.F) (AE D) (ell D ρ ⬝ᵥ b *ᵥ ratV (vecB B.o B.ζ))) with hk
  have key : ∀ v : UX D ρ,
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) y =
        k • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) y := by
    intro v
    have ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have t1 := (FS _ h2).levi u (xZero J.d ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (xZero J.d)] at t2
    have t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
        ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [hq, AddChar.map_zero_eq_one, one_smul] at t3
    unfold evalAt
    rw [e, t1, t2, t3]
    have t4 := (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1
      ((v * u').1.1 ⬝ b) y
    have t5 : symplO B.V₀ J.W (J.d.incAdj B.V₀ y) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b)) =
        Algebra.trace (AF D.host.F) (AE D) (ell D ρ ⬝ᵥ b *ᵥ ratV (vecB B.o B.ζ)) := by
      refine (symplO_yZero J.d _ _).trans ?_
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ell_vecMul (v * u').2]
    rw [t5] at t4
    exact t4
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  refine ⟨psiUni ψ u * k, mul_ne_zero (left_ne_zero_of_mul_eq_one hu1) (GlobalTheory.FlatRInv.addChar_ne_zero ψ _), ?_⟩
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) y w ∂s.vU.ν = _ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1) y w ∂s.vU.ν
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul]
  generalize evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) y w = z
  linear_combination (-(star (psiUni ψ v.1) * k * z)) * hu1

theorem flatBF_src_ne {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {r : GA D B.V} (hr : r ∈ besGrp B.d B.o) (h : flatBF s (s.om (r, 1) Ψ) ≠ 0) :
    flatBF s Ψ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o r).1 hr
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have e := GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ ρ B J s om' hom' Ψ hΨ a 1 (one_mem _) 1
  rw [map_one, mul_one, h0, (GlobalTheory.FlatRInv.opA_eq_zero_iff ψ J.d B.o B.ζ s.om₀ 1 1 0).2 rfl, map_zero, smul_zero] at e
  obtain ⟨c, -, hc⟩ := flatBF_source s (s.weil.om_pres (embA B.d B.o a, 1) Ψ hΨ) hn
  rw [← om_mul, one_mul, e, smul_zero] at hc
  exact hc

theorem flatFB_src_ne {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) {Ψ : WO J.W B.V → ℂ}
    (hΨ : IsThetaFunO ψ J.W B.V Ψ) {r : GA D J.W} (hr : r ∈ jacGrp J.d) (h : flatFB s (s.om (r, 1) Ψ) ≠ 0) :
    flatFB s Ψ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hr
  have e := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D (GlobalTheory.Desc.weil_data_descend D) ψ σ J B s Ψ hΨ a 1
  rw [map_one, h0, map_zero] at e
  have hc := flatFB_source s (s.weil.om_pres (J.d.emb0 a, 1) Ψ hΨ) hn
  rw [← om_mul, one_mul, e, (GlobalTheory.FlatRInv.heisO_eq_zero_iff ψ _ _ _ 0).2 rfl, smul_zero] at hc
  exact hc

theorem inBig_bf {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W}
    {LW₀ : Lat J.W₀} {P : Pl D → Prop} (good : ∀ v, P v → GoodBF ψ B J LV LV₀ LW LW₀ v) (unr : ∀ v, P v → UnrAt s v)
    (sd : IsSelfDualC J.W LW) {Φ : WO B.V J.W → ℂ} (hΦ : Vac ψ B.V J.W LV LW P Φ) {g : GA D B.V} {h : GA D J.W}
    (hg : InBig B.V (besGrp B.d B.o) LV P g) (hne : flatBF s (s.om (g, h) Φ) ≠ 0) : InBig J.W (jacGrp J.d) LW P h := by
  obtain ⟨r, hr, -, g', hg', κ, hκ, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all D ψ ρ B J s LV LV₀ LW LW₀ P good unr sd Φ hΦ
  refine (h2 g' hg').1 h (flatBF_src_ne s (s.weil.om_pres _ _ hΦ.1) hr ?_)
  have e : s.om (r * g' * κ, h) Φ = s.om (r, 1) (s.om (g', h) (s.om (κ, 1) Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, mul_one]
  rwa [e, h1 κ 1 hκ ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩] at hne

theorem inBig_fb {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) {LV : Lat J.W} {LV₀ : Lat J.W₀} {LW : Lat B.V}
    {LW₀ : Lat B.V₀} {P : Pl D → Prop} (ad : ∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v) (unr : ∀ v, P v → UnrAt s v)
    (spl : ∀ v, P v → SplitCore B LW₀ v) (sdV : IsSelfDualC J.W LV) (sd : IsSelfDualC B.V LW) {Φ : WO J.W B.V → ℂ}
    (hΦ : Vac ψ J.W B.V LV LW P Φ) {g : GA D J.W} {h : GA D B.V}
    (hg : InBig J.W (jacGrp J.d) LV P g) (hne : flatFB s (s.om (g, h) Φ) ≠ 0) : InBig B.V (besGrp B.d B.o) LW P h := by
  obtain ⟨r, hr, -, g', hg', κ, hκ, rfl⟩ := hg
  have tameP : ∀ v, P v → Tame D v := fun v hv => (ad v hv).tame
  have h1 := GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd P
    (fun v hv => ⟨tameP v hv, (unr v hv).1, (unr v hv).2⟩) Φ hΦ κ 1 hκ ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩
  have e : s.om (r * g' * κ, h) Φ = s.om (r, 1) (s.om (g', h) (s.om (κ, 1) Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, mul_one]
  rw [e, h1] at hne
  replace hne := flatFB_src_ne s (s.weil.om_pres _ _ hΦ.1) hr hne
  refine GlobalTheory.T.placewise_to_adelicDecomposition_forall D B.V LW P sd (besGrp B.d B.o) h fun v hv => ?_
  obtain ⟨x, hx, h', hh', rfl⟩ := GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace D B.V h v
  refine ⟨x, hx, h', hh', rfl, ?_⟩
  have hΦv : Vac ψ J.W B.V LV LW (· = v) Φ :=
    ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd P tameP Φ).1.mp hΦ).2 v hv
  have hf : Vac ψ J.W B.V LV LW (· = v) (s.om (g', h') Φ) :=
    (GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd (· = v)
      (fun w hw => hw ▸ tameP v hv) Φ).2.1 hΦv g' (GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone D J.W P (· = v) (fun w hw => hw ▸ hv) hg') h' hh'
  have hom : s.om (g', x * h') Φ = s.om (1, x) (s.om (g', h') Φ) := by rw [← om_mul, one_mul]
  rw [hom] at hne
  obtain ⟨n, hnF, hnv, γ, hγ, k, hk, hdec, hγp⟩ :=
    (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B s LV LV₀ LW LW₀ v (ad v hv) (unr v hv) (flatFB s)
      ((GlobalTheory.FlatLawsDuality.flatLaws_all D ψ (· = v)).2 σ J B s) ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B s) _ hf).2 x hx hne
  obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split D σ B LW₀ v (tameP v hv) (ad v hv).sdW₀ (spl v hv) γ hγ hγp
  obtain ⟨r', hr', hrv, κ', hκ', heq⟩ := GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B LW LW₀ v (ad v hv).monoW n hnF hnv a₀ ha₀ κ₀ hκ₀ k hk
  exact ⟨r', hr', hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.RowOneCos

end
