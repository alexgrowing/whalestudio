import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RallisInnerProduct.ExistsCommonLevelSobolevBoundWeilCompact
import Development.AutomorphicArithmetic.ThetaCorrespondence.RallisInnerProduct.ThetaFunApproxByFockVectorsOfCartanInvolutions
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFubiniTwoLiftsModerateGrowthKernels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

section

noncomputable section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace UpperTheory.Lit.Rallis.FockFinite
open GlobalTheory
open Filter Topology

theorem mem_rel_of_isKFinVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ (μ : Measure (WO (dblSp A) B)) (𝓕 : Set (WO (dblSp A) B)), IsCovolOne (ratL B (dblSp A)) μ 𝓕 → ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ (sS : RealMat (dblSp A)) (sB : RealMat B), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) → ∀ L : (WO (dblSp A) B → ℂ) → GA D (dblSp A) → ℂ, (∀ f f', IsThetaFunO ψ (dblSp A) B f → IsThetaFunO ψ (dblSp A) B f' → L (f + f') = L f + L f') → (∀ (c : ℂ) f, IsThetaFunO ψ (dblSp A) B f → L (c • f) = c • L f) → (∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x g, L (om (x, 1) f) g = L f (g * x)) → (SobBdd ψ θ μ 𝓕 fun f x => ‖L f x‖ₑ) → ∀ R : Submodule ℂ ((GA D (dblSp A) → ℂ) × (GA D (dblSp A) → ℂ)), (∀ E, (0, E) ∈ R → E = 0) → (∀ f, IsFockVec ψ θ (dblSp A) B sS sB f → (swSec A B om ν 𝓨 f, L f) ∈ R) → ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec om (Khat A a) f → (swSec A B om ν 𝓨 f, L f) ∈ R := by
  intro D ψ A B χ om hom θ hθ ν 𝓨 hν μ 𝓕 hμ a ha hIw sS sB hsS hsB hcomm L hLadd hLsmul hLeq hLbdd R hR hFock f hf hfK

  haveI : CompactSpace (Khat A a) := isCompact_iff_compactSpace.mp (isCompact_Khat A a)
  letI : MeasurableSpace (Khat A a) := borel _
  haveI : BorelSpace (Khat A a) := ⟨rfl⟩
  set νK : Measure (Khat A a) := Measure.haar with hνK
  have hint : ∀ F : Khat A a → ℂ, Continuous F → Integrable F νK := fun F hF =>
    integrableOn_univ.mp (hF.continuousOn.integrableOn_compact isCompact_univ)

  have thSub : ∀ {u v : WO (dblSp A) B → ℂ}, IsThetaFunO ψ (dblSp A) B u → IsThetaFunO ψ (dblSp A) B v →
      IsThetaFunO ψ (dblSp A) B (u - v) := fun hu hv => by
    simpa [sub_eq_add_neg] using GlobalTheory.OrientedHeis.theta_add hu (GlobalTheory.OrientedHeis.theta_smul (-1) hv)

  let orb : (WO (dblSp A) B → ℂ) → Khat A a → WO (dblSp A) B → ℂ := fun h k => om ((k : GA D (dblSp A)), 1) h
  have hfinIff : ∀ h, IsKFinVec om (Khat A a) h ↔ FiniteDimensional ℂ (Submodule.span ℂ (Set.range (orb h))) := by
    intro h
    have : {f' : WO (dblSp A) B → ℂ | ∃ k ∈ Khat A a, f' = om (k, 1) h} = Set.range (orb h) := by
      ext f'; exact ⟨fun ⟨k, hk, e⟩ => ⟨⟨k, hk⟩, e.symm⟩, fun ⟨k, e⟩ => ⟨k, k.2, e.symm⟩⟩
    show FiniteDimensional ℂ (Submodule.span ℂ {f' | ∃ k ∈ Khat A a, f' = om (k, 1) h}) ↔ _
    rw [this]
  have thSpan : ∀ h, IsThetaFunO ψ (dblSp A) B h → ∀ v ∈ Submodule.span ℂ (Set.range (orb h)),
      IsThetaFunO ψ (dblSp A) B v := by
    intro h hh v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hom.om_pres _ _ hh
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  have kfSub : ∀ {u v}, IsKFinVec om (Khat A a) u → IsKFinVec om (Khat A a) v → IsKFinVec om (Khat A a) (u - v) := by
    intro u v hu hv
    rw [hfinIff] at hu hv ⊢
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
      _ ≤ Submodule.span ℂ (Set.range (orb u)) ⊔ Submodule.span ℂ (Set.range (orb v)))
    rintro _ ⟨k, rfl⟩
    simp only [orb, map_sub, SetLike.mem_coe]
    exact sub_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨k, rfl⟩))
  have orbCont : ∀ h, IsThetaFunO ψ (dblSp A) B h → ∀ w, Continuous fun k => orb h k w := fun h hh w =>
    (hom.om_cont h hh w).comp (continuous_subtype_val.prodMk continuous_const)

  have swAdd : ∀ {u v}, IsThetaFunO ψ (dblSp A) B u → IsThetaFunO ψ (dblSp A) B v →
      swSec A B om ν 𝓨 (u + v) = swSec A B om ν 𝓨 u + swSec A B om ν 𝓨 v := by
    intro u v hu hv; funext x
    simp only [swSec, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero, map_add, Pi.add_apply]
    exact integral_add
      (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ om hom ν 𝓨 hν _ (hom.om_pres _ _ hu)).1
      (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ om hom ν 𝓨 hν _ (hom.om_pres _ _ hv)).1
  have swSmul : ∀ (c : ℂ) u, swSec A B om ν 𝓨 (c • u) = c • swSec A B om ν 𝓨 u := by
    intro c u; funext x
    simp only [swSec, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero, map_smul, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  have swTr : ∀ u (x y : GA D (dblSp A)), swSec A B om ν 𝓨 u (x * y) = swSec A B om ν 𝓨 (om (y, 1) u) x := by
    intro u x y
    simp only [swSec]
    rw [show ((x * y : GA D (dblSp A)), (1 : GA D B)) = (x, 1) * (y, 1) by simp, map_mul, Module.End.mul_apply]

  let ρK : Khat A a →* Module.End ℂ (WO (dblSp A) B → ℂ) := om.comp ((MonoidHom.inl _ _).comp (Khat A a).subtype)
  obtain ⟨e, n, α, β, he, hβ, hker, hrep⟩ :=
    UpperTheory.Lit.Rallis.T.exists_continuous_kernel_reproducing_finite_vector (Khat A a) νK (WO (dblSp A) B) ρK f ((hfinIff f).1 hfK) (orbCont f hf)
  set P : (WO (dblSp A) B → ℂ) → WO (dblSp A) B → ℂ := fun h w => ∫ k, e k * orb h k w ∂νK with hPdef
  have hPf : P f = f := funext fun w => (hrep w).symm

  have hB : ∀ h, IsThetaFunO ψ (dblSp A) B h → IsKFinVec om (Khat A a) h →
      P h ∈ Submodule.span ℂ (Set.range (orb h)) ∧
      ∀ M : (WO (dblSp A) B → ℂ) → GA D (dblSp A) → ℂ,
        (∀ {u v}, IsThetaFunO ψ (dblSp A) B u → IsThetaFunO ψ (dblSp A) B v → M (u + v) = M u + M v) →
        (∀ (c : ℂ) u, IsThetaFunO ψ (dblSp A) B u → M (c • u) = c • M u) →
        (∀ u, IsThetaFunO ψ (dblSp A) B u → ∀ x y, M u (x * y) = M (om (y, 1) u) x) →
        ∀ x, M (P h) x = ∫ k, e k * M h (x * k) ∂νK := by
    intro h hh hK
    obtain ⟨h1, h2⟩ := UpperTheory.Lit.Rallis.T.weighted_integral_mem_span_of_finiteDimensional_orbit (Khat A a) νK _ (orb h) e he ((hfinIff h).1 hK) (orbCont h hh)
    refine ⟨h1, fun M hMa hMs hMt x => ?_⟩
    have := h2 (fun φ => M φ x)
      (fun u hu v hv => by simp only [hMa (thSpan h hh u hu) (thSpan h hh v hv), Pi.add_apply])
      (fun c u hu => by simp only [hMs c u (thSpan h hh u hu), Pi.smul_apply, smul_eq_mul])
    refine this.trans (integral_congr_ae (ae_of_all _ fun k => ?_))
    simp only [orb]
    rw [hMt h hh x k]
  have thP : ∀ h, IsThetaFunO ψ (dblSp A) B h → IsKFinVec om (Khat A a) h → IsThetaFunO ψ (dblSp A) B (P h) :=
    fun h hh hK => thSpan h hh _ (hB h hh hK).1
  have swSmul' : ∀ (c : ℂ) u, IsThetaFunO ψ (dblSp A) B u → swSec A B om ν 𝓨 (c • u) = c • swSec A B om ν 𝓨 u :=
    fun c u _ => swSmul c u
  have swTr' : ∀ u, IsThetaFunO ψ (dblSp A) B u → ∀ x y, swSec A B om ν 𝓨 u (x * y) = swSec A B om ν 𝓨 (om (y, 1) u) x :=
    fun u _ x y => swTr u x y
  have LTr : ∀ u, IsThetaFunO ψ (dblSp A) B u → ∀ x y, L u (x * y) = L (om (y, 1) u) x :=
    fun u hu x y => (hLeq u hu y x).symm
  have LAdd : ∀ {u v}, IsThetaFunO ψ (dblSp A) B u → IsThetaFunO ψ (dblSp A) B v → L (u + v) = L u + L v :=
    fun hu hv => hLadd _ _ hu hv

  have swCont : ∀ h, IsThetaFunO ψ (dblSp A) B h → Continuous (swSec A B om ν 𝓨 h) := fun h hh =>
    (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ om hom ν 𝓨 hν h hh).2

  have hKer : ∀ h, IsThetaFunO ψ (dblSp A) B h → IsKFinVec om (Khat A a) h → ∀ k₀ : Khat A a,
      swSec A B om ν 𝓨 (P h) k₀ = ∑ i, (∫ k, β i k * swSec A B om ν 𝓨 h k ∂νK) * α i k₀ := by
    intro h hh hK k₀
    rw [(hB h hh hK).2 _ swAdd swSmul' swTr' k₀]
    have e1 : ∀ k : Khat A a, e k * swSec A B om ν 𝓨 h ((k₀ : GA D (dblSp A)) * k) =
        (fun k' : Khat A a => e (k₀⁻¹ * k') * swSec A B om ν 𝓨 h k') (k₀ * k) := by
      intro k; simp only [inv_mul_cancel_left, Subgroup.coe_mul]
    rw [integral_congr_ae (ae_of_all _ e1),
      integral_mul_left_eq_self (μ := νK) (fun k' : Khat A a => e (k₀⁻¹ * k') * swSec A B om ν 𝓨 h k') k₀]
    simp_rw [hker, Finset.sum_mul]
    rw [integral_finset_sum _ fun i _ => hint _ (by
      have := hβ i; have := swCont h hh; fun_prop)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [mul_assoc]
    rw [integral_const_mul, mul_comm]
  obtain ⟨X₀, hX₀fin, hX₀⟩ := UpperTheory.Lit.Rallis.T.exists_finiteDimensional_space_of_siegelWeilSections D ψ A B χ om hom ν 𝓨 hν a hIw n α
  have inX₀ : ∀ h, IsThetaFunO ψ (dblSp A) B h → IsKFinVec om (Khat A a) h → swSec A B om ν 𝓨 (P h) ∈ X₀ :=
    fun h hh hK => hX₀ _ (thP h hh hK) _ (hKer h hh hK)

  obtain ⟨U, hUo, hfU, happ⟩ := UpperTheory.Lit.Rallis.T.thetaFun_approx_by_fockVectors_of_cartanInvolutions D ψ hom.std θ hθ (dblSp A) B μ 𝓕 hμ sS sB hsS hsB f hf
  choose g hgF hgU hgs using fun j : ℕ => happ j ((j : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top j))
  have hgK : ∀ j, IsKFinVec om (Khat A a) (g j) := fun j =>
    GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ (dblSp A) B 1 χ om sS sB hom hθ hsS hsB (Khat A a)
      (isCompact_Khat A a) hcomm (g j) (hgF j)
  have hgth : ∀ j, IsThetaFunO ψ (dblSp A) B (g j) := fun j => (hgF j).1
  have hsob : ∀ d, Tendsto (fun j => sobO ψ θ μ 𝓕 d (f - g j)) atTop (𝓝 0) := by
    intro d
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ENNReal.tendsto_inv_nat_nhds_zero
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop d] with j hj
    refine le_trans ?_ (hgs j).le
    simp only [sobO, GlobalTheory.Size.wordSum]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

  have inR : ∀ j, (swSec A B om ν 𝓨 (P (g j)), L (P (g j))) ∈ R := by
    intro j
    have hmem := (hB (g j) (hgth j) (hgK j)).1
    obtain ⟨N, hN⟩ := (hgF j).2
    have key : ∀ v ∈ Submodule.span ℂ (Set.range (orb (g j))), IsThetaFunO ψ (dblSp A) B v ∧ (swSec A B om ν 𝓨 v, L v) ∈ R := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        have hth := hom.om_pres ((k : GA D (dblSp A)), 1) _ (hgth j)
        exact ⟨hth, hFock _ ⟨hth, N, GlobalTheory.CartanFockDeg.om_keeps_fockDeg D ψ θ (dblSp A) B 1 χ om sS sB hom hθ k
          (hcomm k k.2) N (g j) (hgth j) hN⟩⟩
      | zero =>
        refine ⟨GlobalTheory.OrientedHeis.theta_zero, ?_⟩
        have h0 : swSec A B om ν 𝓨 0 = 0 := by simpa using swSmul 0 0
        have h1 : L 0 = 0 := by simpa using hLsmul 0 0 GlobalTheory.OrientedHeis.theta_zero
        rw [h0, h1]; exact R.zero_mem
      | add x y _ _ hx hy =>
        refine ⟨GlobalTheory.OrientedHeis.theta_add hx.1 hy.1, ?_⟩
        rw [swAdd hx.1 hy.1, LAdd hx.1 hy.1, ← Prod.mk_add_mk]; exact R.add_mem hx.2 hy.2
      | smul c x _ hx =>
        refine ⟨GlobalTheory.OrientedHeis.theta_smul c hx.1, ?_⟩
        rw [swSmul c x, hLsmul c x hx.1, ← Prod.smul_mk]; exact R.smul_mem c hx.2
    exact (key _ hmem).2

  obtain ⟨Ce, hCe⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuousOn
  have hfK' := hfK
  have conv : ∀ M : (WO (dblSp A) B → ℂ) → GA D (dblSp A) → ℂ,
      (∀ {u v}, IsThetaFunO ψ (dblSp A) B u → IsThetaFunO ψ (dblSp A) B v → M (u + v) = M u + M v) →
      (∀ (c : ℂ) u, IsThetaFunO ψ (dblSp A) B u → M (c • u) = c • M u) →
      (∀ u, IsThetaFunO ψ (dblSp A) B u → ∀ x y, M u (x * y) = M (om (y, 1) u) x) →
      SobBdd ψ θ μ 𝓕 (fun φ y => ‖M φ y‖ₑ) →
      ∀ x, Tendsto (fun j => M (P (g j)) x) atTop (𝓝 (M f x)) := by
    intro M hMa hMs hMt hMb x
    have hMsub : ∀ {u v}, IsThetaFunO ψ (dblSp A) B u → IsThetaFunO ψ (dblSp A) B v → M (u - v) = M u - M v := by
      intro u v hu hv
      rw [sub_eq_add_neg, ← neg_one_smul ℂ v, hMa hu (GlobalTheory.OrientedHeis.theta_smul _ hv),
        hMs _ _ hv, neg_one_smul, ← sub_eq_add_neg]
    obtain ⟨d, C, hC⟩ := hMb U hUo (Set.range fun k : Khat A a => x * (k : GA D (dblSp A)))
      (isCompact_range (continuous_const.mul continuous_subtype_val))
    have hdiff : ∀ j, M f x - M (P (g j)) x = ∫ k, e k * M (f - g j) (x * k) ∂νK := by
      intro j
      have hPsub : P f - P (g j) = P (f - g j) := by
        funext w
        simp only [hPdef, orb, map_sub, Pi.sub_apply, mul_sub]
        exact (integral_sub (hint (fun k => e k * orb f k w) (he.mul (orbCont f hf w)))
          (hint (fun k => e k * orb (g j) k w) (he.mul (orbCont (g j) (hgth j) w)))).symm
      have := (hB (f - g j) (thSub hf (hgth j)) (kfSub hfK (hgK j))).2 M hMa hMs hMt x
      rw [← this, ← hPsub, hMsub (thP f hf hfK) (thP _ (hgth j) (hgK j)), hPf, Pi.sub_apply]
    set K0 : ℝ≥0∞ := ENNReal.ofReal Ce * C * νK Set.univ with hK0
    have hK0t : K0 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
      (measure_ne_top _ _)
    have hbd : ∀ j, edist (M (P (g j)) x) (M f x) ≤ K0 * sobO ψ θ μ 𝓕 d (f - g j) := by
      intro j
      rw [edist_comm, edist_eq_enorm_sub, hdiff j]
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have hpt : ∀ k : Khat A a, ‖e k * M (f - g j) (x * k)‖ₑ ≤ ENNReal.ofReal Ce * (C * sobO ψ θ μ 𝓕 d (f - g j)) := by
        intro k
        rw [enorm_mul]
        refine mul_le_mul' ?_ (hC _ (sub_mem hfU (hgU j)) _ ⟨k, rfl⟩)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hCe k (Set.mem_univ _))
      refine (lintegral_mono hpt).trans ?_
      rw [lintegral_const, hK0]
      apply le_of_eq; ring
    rw [tendsto_iff_edist_tendsto_0]
    have hl := ENNReal.Tendsto.const_mul (hsob d) (Or.inr hK0t)
    rw [mul_zero] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => zero_le) hbd
  exact UpperTheory.Lit.Rallis.T.pointwise_limit_mem_graphRelation_of_finiteDimensional (GA D (dblSp A)) R hR X₀ hX₀fin (fun j => swSec A B om ν 𝓨 (P (g j))) (fun j => L (P (g j)))
    (swSec A B om ν 𝓨 f) (L f) (fun j => ⟨inX₀ _ (hgth j) (hgK j), inR j⟩)
    (conv _ swAdd swSmul' swTr' (UpperTheory.Lit.Rallis.T.siegelWeilSection_bounded_by_sobolevSeminorm D ψ A B χ om hom θ hθ ν 𝓨 hν μ 𝓕 hμ))
    (conv L LAdd hLsmul LTr hLbdd)
end UpperTheory.Lit.Rallis.FockFinite

end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.graphRelation_extends_from_fockVectors_to_kFinite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ (μ : Measure (WO (dblSp A) B)) (𝓕 : Set (WO (dblSp A) B)), IsCovolOne (ratL B (dblSp A)) μ 𝓕 → ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ (sS : RealMat (dblSp A)) (sB : RealMat B), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) → ∀ L : (WO (dblSp A) B → ℂ) → GA D (dblSp A) → ℂ, (∀ f f', IsThetaFunO ψ (dblSp A) B f → IsThetaFunO ψ (dblSp A) B f' → L (f + f') = L f + L f') → (∀ (c : ℂ) f, IsThetaFunO ψ (dblSp A) B f → L (c • f) = c • L f) → (∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x g, L (om (x, 1) f) g = L f (g * x)) → (SobBdd ψ θ μ 𝓕 fun f x => ‖L f x‖ₑ) → ∀ R : Submodule ℂ ((GA D (dblSp A) → ℂ) × (GA D (dblSp A) → ℂ)), (∀ E, (0, E) ∈ R → E = 0) → (∀ f, IsFockVec ψ θ (dblSp A) B sS sB f → (swSec A B om ν 𝓨 f, L f) ∈ R) → ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec om (Khat A a) f → (swSec A B om ν 𝓨 f, L f) ∈ R := by
  first | exact @UpperTheory.Lit.Rallis.FockFinite.mem_rel_of_isKFinVec | exact UpperTheory.Lit.Rallis.FockFinite.mem_rel_of_isKFinVec | (intros; apply UpperTheory.Lit.Rallis.FockFinite.mem_rel_of_isKFinVec <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section
namespace UpperTheory.Lit.Rallis.SiegelWeilFinite
open GlobalTheory

variable {D : D7}

theorem flat_zero {V : HSp D} (a : GL (Fin V.rank) (AE D)) (s₁ : ℂ) : flat V a 0 s₁ = 0 := by
  funext s g
  simp [flat, flatAd, flatH, flatOf, flatSec]

theorem flat_add {V : HSp D} (a : GL (Fin V.rank) (AE D)) (s₁ : ℂ) (Φ Ψ : GA D (dblSp V) → ℂ) :
    flat V a (Φ + Ψ) s₁ = flat V a Φ s₁ + flat V a Ψ s₁ := by
  funext s g
  simp [flat, flatAd, flatH, flatOf, flatSec, add_mul]

theorem flat_smul {V : HSp D} (a : GL (Fin V.rank) (AE D)) (s₁ c : ℂ) (Φ : GA D (dblSp V) → ℂ) :
    flat V a (c • Φ) s₁ = c • flat V a Φ s₁ := by
  funext s g
  simp [flat, flatAd, flatH, flatOf, flatSec, mul_assoc]

theorem eisValueAt_zero {V : HSp D} (s₀ : ℂ) : EisValueAt V 0 s₀ 0 := by
  refine ⟨fun s _ => ⟨fun γ _ g => rfl, fun g => by simp [EisConv, CosetConv, term]⟩, fun g => ?_⟩
  have e : eisSer V 0 g = fun _ => 0 := by
    funext s; simp [eisSer, eis, cosetSum, term]
  rw [e]
  exact ⟨_, isExtAt_const 0 s₀, analyticAt_const, rfl⟩

def valuePairs (V : HSp D) (a : GL (Fin V.rank) (AE D)) (s₀ : ℂ) :
    Submodule ℂ ((GA D (dblSp V) → ℂ) × (GA D (dblSp V) → ℂ)) where
  carrier := {p | EisValueAt V (flat V a p.1 s₀) s₀ p.2}
  add_mem' := fun {p q} hp hq => by
    show EisValueAt V (flat V a (p.1 + q.1) s₀) s₀ (p.2 + q.2)
    rw [flat_add]; exact hp.add hq
  zero_mem' := by
    show EisValueAt V (flat V a 0 s₀) s₀ 0
    rw [flat_zero]; exact eisValueAt_zero s₀
  smul_mem' := fun c p hp => by
    show EisValueAt V (flat V a (c • p.1) s₀) s₀ (c • p.2)
    rw [flat_smul]; exact hp.smul c

theorem valuePairs_graph {V : HSp D} (a : GL (Fin V.rank) (AE D)) (s₀ : ℂ) (E : GA D (dblSp V) → ℂ)
    (h : ((0 : GA D (dblSp V) → ℂ), E) ∈ valuePairs V a s₀) : E = 0 :=
  EisValueAt.unique (Φ := flat V a 0 s₀) h (by rw [flat_zero]; exact eisValueAt_zero s₀)

theorem frame_sq {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a)
    (τ : D.what₂.Tau) :
    (compAt θ τ a.1)ᴴ * (gramAt D V τ * GlobalTheory.Doubling.frameInv θ V a τ) * compAt θ τ a.1 = 1 := by
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  have e : (compAt θ τ a.1)ᴴ * (gramAt D V τ * GlobalTheory.Doubling.frameInv θ V a τ) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) := by
    simp only [GlobalTheory.Doubling.frameInv, Matrix.mul_assoc]
  rw [e, hε]
  exact GlobalTheory.Doubling.diagonal_sign_mul_self ε

variable {D : D7} {A B : HSp D}

theorem thetaMean_add {ψ : AddChar (AF D.host.F) ℂ}
    {om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} (m : Measure (GA D B))
    (hi : ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f) (autMeasure B m))
    (f f' : WO (dblSp A) B → ℂ) (hf : IsThetaFunO ψ (dblSp A) B f) (hf' : IsThetaFunO ψ (dblSp A) B f') :
    GlobalTheory.ThetaMean.thetaMean om m (f + f') = GlobalTheory.ThetaMean.thetaMean om m f + GlobalTheory.ThetaMean.thetaMean om m f' := by
  funext g
  have e : (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h (f + f')) =
      (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f) + (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f') := by
    funext q; simp [thetaKO, AutomorphicL2Unitary.descend]
  simp only [GlobalTheory.ThetaMean.thetaMean, Pi.add_apply]
  rw [e]
  rw [average_eq, average_eq, average_eq, integral_add' (hi f hf g) (hi f' hf' g), smul_add]

theorem thetaMean_smul {om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} (m : Measure (GA D B))
    (c : ℂ) (f : WO (dblSp A) B → ℂ) :
    GlobalTheory.ThetaMean.thetaMean om m (c • f) = c • GlobalTheory.ThetaMean.thetaMean om m f := by
  funext g
  have e : (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h (c • f)) = c • (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f) := by
    funext q; simp [thetaKO, AutomorphicL2Unitary.descend]
  simp only [GlobalTheory.ThetaMean.thetaMean, Pi.smul_apply]
  rw [e]
  simp only [Pi.smul_apply, average_eq, integral_smul]
  rw [smul_comm]

theorem thetaMean_om {om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)} (m : Measure (GA D B))
    (f : WO (dblSp A) B → ℂ) (x g : GA D (dblSp A)) :
    GlobalTheory.ThetaMean.thetaMean om m (om (x, 1) f) g = GlobalTheory.ThetaMean.thetaMean om m f (g * x) := by
  have e : ∀ h, thetaKO om g h (om (x, 1) f) = thetaKO om (g * x) h f := fun h => by
    simp only [thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [GlobalTheory.ThetaMean.thetaMean, e]

theorem siegelWeil_kFin : GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → A.rank < B.rank → B.rank ≤ 2 * A.rank → A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank → ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ m : Measure (GA D B), m.IsHaarMeasure → ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec om (Khat A a) f → EisValueAt A (flat A a (swSec A B om ν 𝓨 f) (sZero A B)) (sZero A B) (GlobalTheory.ThetaMean.thetaMean om m f) := by
  intro hSW hWc D ψ A B χ om hW hAB hBA hwitt a ha hI θ hθ ν 𝓨 hν m hm f hf hK
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (dblSp A) B
  have h1 : 1 ≤ A.rank := by omega

  obtain ⟨hsS, hcomm⟩ := GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ A (GlobalTheory.Doubling.frameInv θ A a) a hθ
    (fun τ => ha.isCartanInv hθ τ) (fun τ => frame_sq hθ ha τ)
  obtain ⟨b, hb⟩ := GlobalTheory.Doubling.exists_isMaj B
  have hsB : ∀ τ, IsCartanInv (gramAt D B τ) (GlobalTheory.Doubling.frameInv θ B b τ) := fun τ => hb.isCartanInv hθ τ

  have hi : ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g,
      Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO om g h f) (autMeasure B m) :=
    fun f hf g => GlobalTheory.WeilThetaInt.integrable_thetaKO hWc D A B m hm h1 (Or.inr hwitt) ψ χ om hW f hf g

  have hint := UpperTheory.Lit.Rallis.T.absThetaIntegral_le_sobolevSeminorm D ψ (dblSp A) B 1 χ om hW θ hθ μ 𝓕 hμ m hm id (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) (sobCont_id ψ θ μ 𝓕) (fun _ _ _ => rfl) (fun f hf => hi f hf 1)
  have hbdd : SobBdd ψ θ μ 𝓕 fun f x => ‖GlobalTheory.ThetaMean.thetaMean om m f x‖ₑ := by
    intro U hU K hK'
    obtain ⟨d, C, hC⟩ := hint U hU K hK'
    refine ⟨d, ‖((autMeasure B m).real Set.univ)⁻¹‖₊ * C, fun f hf x hx => ?_⟩
    calc ‖GlobalTheory.ThetaMean.thetaMean om m f x‖ₑ
        ≤ ‖((autMeasure B m).real Set.univ)⁻¹‖ₑ *
            ∫⁻ q, ‖AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO om x h f) q‖ₑ ∂autMeasure B m := by
          rw [GlobalTheory.ThetaMean.thetaMean, average_eq, enorm_smul]
          gcongr
          exact enorm_integral_le_lintegral_enorm _
      _ ≤ ‖((autMeasure B m).real Set.univ)⁻¹‖ₑ * (C * sobO ψ θ μ 𝓕 d f) := by
          gcongr; exact hC f hf x hx
      _ = _ := by rw [ENNReal.coe_mul, mul_assoc, enorm_eq_nnnorm]
  have key := UpperTheory.Lit.Rallis.T.graphRelation_extends_from_fockVectors_to_kFinite D ψ A B χ om hW θ hθ ν 𝓨 hν μ 𝓕 hμ a ha hI _ (GlobalTheory.Doubling.frameInv θ B b) hsS hsB hcomm
    (GlobalTheory.ThetaMean.thetaMean om m) (fun f f' hf hf' => thetaMean_add m hi f f' hf hf')
    (fun c f _ => thetaMean_smul m c f) (fun f _ x g => thetaMean_om m f x g) hbdd
    (valuePairs A a (sZero A B)) (valuePairs_graph a (sZero A B))
    (fun f hF => (hSW D ψ A B hAB hBA hwitt χ om hW a ha hI θ _ _ hθ hsS hsB hcomm ν 𝓨 hν m hm f hF).2) f hf hK
  exact key

end UpperTheory.Lit.Rallis.SiegelWeilFinite

end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.siegelWeil_convergent_range_kFinite_thetaFun : GlobalTheory.Published.SiegelWeilUnitaryConvergent → GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → A.rank < B.rank → B.rank ≤ 2 * A.rank → A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank → ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ m : Measure (GA D B), m.IsHaarMeasure → ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec om (Khat A a) f → EisValueAt A (flat A a (swSec A B om ν 𝓨 f) (sZero A B)) (sZero A B) (GlobalTheory.ThetaMean.thetaMean om m f) := by
  first | exact @UpperTheory.Lit.Rallis.SiegelWeilFinite.siegelWeil_kFin | exact UpperTheory.Lit.Rallis.SiegelWeilFinite.siegelWeil_kFin | (intros; apply UpperTheory.Lit.Rallis.SiegelWeilFinite.siegelWeil_kFin <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace UpperTheory.Lit.Rallis.ThetaAbsGrowth
open GlobalTheory

open GlobalTheory.KernelSeminorm GlobalTheory.FockCompare GlobalTheory.ThetaGrowth GlobalTheory.CuspDecay

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem actO_real {a : GA D S} (ha : a ∈ GinfC S) {x : WO S T} (hx : x.map (infPart D) = 0) :
    actO S T a 1 x = x := by
  have e1 : (Formalism.L2.Theta.mt S a⁻¹).map (finPart D) = 1 :=
    congrArg Units.val (show finHom S a⁻¹ = 1 from inv_mem ha)
  have e2 : (Formalism.L2.Theta.mt T 1).map (finPart D) = 1 :=
    congrArg Units.val (show finHom T 1 = 1 from map_one _)
  have e3 : (actO S T a 1 x).map (infPart D) = x.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]
  have e4 : (actO S T a 1 x).map (finPart D) = x.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.mul_one, Matrix.one_mul]
  exact Matrix.ext fun i j => GlobalTheory.DetOnto.ext_parts D (congrFun (congrFun e3 i) j) (congrFun (congrFun e4 i) j)

theorem om_real_mem_level (hW : IsWeilDatumO ψ S T χS χT om) {U : AddSubgroup (WO S T)} {f : WO S T → ℂ}
    (hf : f ∈ GlobalTheory.Size.thetaLevel ψ S T U) {a : GA D S} (ha : a ∈ GinfC S) : om (a, 1) f ∈ GlobalTheory.Size.thetaLevel ψ S T U :=
  ⟨hW.om_pres _ f hf.1, fun u hu h0 => by
    have e := hW.om_heis a 1 u f hf.1
    rw [hf.2 u hu h0, actO_real ha h0] at e
    exact e.symm⟩

theorem sobO_om_fst_le (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) {μ : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a, (sobO ψ θ μ 𝓕 d (om (a, 1) f)).toReal ≤ C * (1 + normInf θ S a) ^ d := by
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℝ, (∀ a, ‖(letter a : GlobalTheory.FockCompare.RW T S)‖ ≤ L) ∧ 0 ≤ L :=
    ⟨∑ a, ‖(letter a : GlobalTheory.FockCompare.RW T S)‖,
      fun a => Finset.single_le_sum (f := fun a => ‖(letter a : GlobalTheory.FockCompare.RW T S)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a), by positivity⟩
  have hT := GlobalTheory.RatCount.normInf_nonneg θ T 1
  obtain ⟨c0, hc0, hc0'⟩ : ∃ c0 : ℝ, c0 = normInf θ T 1 * L ∧ 0 ≤ c0 := ⟨_, rfl, by positivity⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, K = (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0) := ⟨_, rfl⟩
  refine ⟨(1 + (K : ℝ) * K * c0) ^ d * (sobO ψ θ μ 𝓕 d f).toReal, by positivity, fun y => ?_⟩
  have hH := GlobalTheory.RatCount.normInf_nonneg θ S y
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = c0 * normInf θ S y := ⟨⟨c0 * normInf θ S y, by positivity⟩, rfl⟩
  have hρ : ∀ a, ‖mov θ y⁻¹ (1 : GA D T)⁻¹ (letter a)‖ ≤ ρ := by
    intro a
    refine (norm_mov_le_normInf _ _ _).trans ?_
    rw [inv_inv, inv_one, hρdef, hc0]
    gcongr
    exact hL a
  have key := GlobalTheory.WeilSobolev.sobO_om_le hW hc hμ.1 hμ.2.1 y 1 hρ d f hf
  have hs := GlobalTheory.Size.sobO_ne_top hW.std hθ hμ.1 hμ.2.1 hf d
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hs) key).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hK]
  have hQ : ((1 + K * (K * ρ) : ℝ≥0) : ℝ) ≤ (1 + (K : ℝ) * K * c0) * (1 + normInf θ S y) := by
    push_cast
    rw [hρdef]
    have : (0 : ℝ) ≤ K := K.2
    nlinarith [mul_nonneg (mul_nonneg this this) hc0']
  calc _ ≤ ((1 + (K : ℝ) * K * c0) * (1 + normInf θ S y)) ^ d * (sobO ψ θ μ 𝓕 d f).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (NNReal.coe_nonneg _) hQ d) ENNReal.toReal_nonneg
    _ = _ := by rw [mul_pow]; ring

theorem modGrowth_of_integrable (hW : IsWeilDatumO ψ S T χS χT om) {m : Measure (GA D T)} (hm : m.IsHaarMeasure)
    (hI : ∀ f, IsThetaFunO ψ S T f → ∀ g, Integrable (descend (GQ T) fun h => thetaKO om g h f) (autMeasure T m))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    GlobalTheory.Grow.ModGrowth S fun g => ∫ q, ‖descend (GQ T) (fun h => thetaKO om g h f) q‖ ∂autMeasure T m := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  have hB := UpperTheory.Lit.Rallis.T.absThetaIntegral_le_sobolevSeminorm D ψ S T χS χT om hW θ hθ μ 𝓕 hμ m hm id (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (sobCont_id ψ θ μ 𝓕) (fun _ _ _ => rfl) (fun f hf => hI f hf 1)
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hf
  obtain ⟨V, V', hV, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std S T om (GlobalTheory.Ker.isWeak_of_datum hW)
    hW.om_cont f hf
  obtain ⟨M, hM⟩ := GlobalTheory.Mem.LiftGrow.reduction_unif hθ S
  obtain ⟨X, A, hA, hX⟩ := hM V hV
  obtain ⟨d, C, hC⟩ := hB U hU X X.finite_toSet.isCompact
  obtain ⟨C₁, hC₁, hs⟩ := sobO_om_fst_le hW hθ hμ hf d
  obtain ⟨C₂, hC₂, hcmp⟩ := GlobalTheory.Grow.height_comparison S hθ
  refine ⟨C * C₁ * (A * C₂ ^ M) ^ d, M * d, fun g => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', e, hb⟩ := hX g
  have hfa := om_real_mem_level hW hl ha
  have e1 : (fun h => thetaKO om g h f) = fun h => thetaKO om x h (om (a, 1) f) := by
    funext h
    rw [← GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hW hf h γ hγ g, e]
    have e2 : ((x * a * k, h) : GA D S × GA D T) = (x, h) * (a, 1) * (k, 1) := by simp
    unfold thetaKO
    rw [e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix k hk hk' 1 (one_mem _) (one_mem _)]
  have hn := GlobalTheory.RatCount.normInf_nonneg θ S a
  have h1 : 1 + normInf θ S a ≤ A * C₂ ^ M * GlobalTheory.Grow.height S g ^ M := by
    refine hb.trans ?_
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hcmp g).1 M) hA
  beta_reduce
  rw [e1, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
    integral_norm_eq_lintegral_enorm (hI _ hfa.1 x).1]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (GlobalTheory.Size.sobO_ne_top hW.std hθ hμ.1 hμ.2.1 hfa.1 d)) (hC _ hfa x hx)).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, pow_mul, mul_assoc, mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left ((hs a).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) h1 d) hC₁)) C.2

theorem absTheta_modGrowth : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ m : Measure (GA D B), m.IsHaarMeasure → ∀ f, IsThetaFunO ψ (dblSp A) B f → GlobalTheory.Grow.ModGrowth (dblSp A) fun g => ∫ q, ‖descend (GQ B) (fun h => thetaKO om g h f) q‖ ∂autMeasure B m :=
  fun hP D ψ A B χ om hW hA hw m hm _ hf => modGrowth_of_integrable hW hm
    (GlobalTheory.WeilThetaInt.integrable_thetaKO hP D A B m hm hA hw ψ χ om hW) hf

end UpperTheory.Lit.Rallis.ThetaAbsGrowth

end
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.doubledPair_absThetaIntegral_moderateGrowth : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ m : Measure (GA D B), m.IsHaarMeasure → ∀ f, IsThetaFunO ψ (dblSp A) B f → GlobalTheory.Grow.ModGrowth (dblSp A) fun g => ∫ q, ‖descend (GQ B) (fun h => thetaKO om g h f) q‖ ∂autMeasure B m := by
  first | exact @UpperTheory.Lit.Rallis.ThetaAbsGrowth.absTheta_modGrowth | exact UpperTheory.Lit.Rallis.ThetaAbsGrowth.absTheta_modGrowth | (intros; apply UpperTheory.Lit.Rallis.ThetaAbsGrowth.absTheta_modGrowth <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

open GlobalTheory.Cusp

namespace UpperTheory.Lit.Rallis.ThetaSq
open GlobalTheory

theorem normSq_thetaKO_modGrowth : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh → ThetaClause ψ A B χB om omh → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsThetaFunO ψ A B Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => GlobalTheory.Cusp.petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  intro hW D ψ A B χA χB om omh hom homh hTC hA hw mH hmH Φ hΦ
  obtain ⟨hφ, hid⟩ := hTC Φ Φ hΦ hΦ
  have key : ∀ g h, thetaKO om g h Φ * conj (thetaKO om g h Φ) =
      ((χB (detA A g) : Circle) : ℂ) * thetaKO omh (io A (g, g)) h (delta A B Φ Φ) := by
    intro g h
    rw [(hid g g h).2]
    have e : ((χB (detA A g) : Circle) : ℂ) * (((χB (detA A g))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g h Φ * conj (thetaKO om g h Φ))) * e
  have knorm : ∀ g h, ‖thetaKO om g h Φ‖ ^ 2 = ‖thetaKO omh (io A (g, g)) h (delta A B Φ Φ)‖ := by
    intro g h
    have := congrArg norm (key g h)
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_conj, ← sq] at this
    rw [this]
  have hleft : ∀ g, LeftInv (GQ B) fun h => thetaKO om g h Φ := fun g γ hγ h => by
    show thetaKO om g (γ * h) Φ = thetaKO om g h Φ
    have e : ((g, γ * h) : GA D A × GA D B) = (1, γ) * (g, h) := by simp
    unfold thetaKO
    rw [e, map_mul]
    exact hom.om_aut 1 (one_mem _) _ hγ _ (hom.om_pres _ _ hΦ)
  have hcont : ∀ g, Continuous fun h => thetaKO om g h Φ := fun g =>
    (hom.om_cont Φ hΦ 0).comp (Continuous.prodMk_right g)
  have hint : ∀ x, Integrable (descend (GQ B) fun h => thetaKO omh x h (delta A B Φ Φ)) (autMeasure B mH) :=
    fun x => GlobalTheory.WeilThetaInt.integrable_thetaKO hW D A B mH hmH hA hw ψ χB omh homh (delta A B Φ Φ) hφ x
  have hL2 : ∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ := by
    intro g
    refine ⟨hleft g, ?_⟩
    have hm : AEStronglyMeasurable (descend (GQ B) fun h => thetaKO om g h Φ) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ B) mH) := by
      rw [aestronglyMeasurable_quotMeasure_iff_lift, (hleft g).lift_descend]
      exact (hcont g).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hint (io A (g, g))).norm.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend]
    exact (knorm g _).symm
  refine ⟨hL2, ?_⟩
  obtain ⟨C₁, N, hC₁⟩ := UpperTheory.Lit.Rallis.T.doubledPair_absThetaIntegral_moderateGrowth hW D ψ A B χB omh homh hA hw mH hmH _ hφ
  have hE : ∀ x, ∫ q, ‖descend (GQ B) (fun h => thetaKO omh x h (delta A B Φ Φ)) q‖ ∂autMeasure B mH ≤
      C₁ * GlobalTheory.Grow.height (dblSp A) x ^ N := by
    intro x
    have := hC₁ x
    rwa [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := (integral_nonneg (fun _ => norm_nonneg _)).trans (hE 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (GlobalTheory.Grow.height_pos _ _) _)
  obtain ⟨C₂, c, hC₂⟩ := GlobalTheory.Grow.IoHeight.main D A
  have hpet : ∀ g, ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖ ≤
      ∫ q, ‖descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q‖ ∂autMeasure B mH := by
    intro g
    have e1 : petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ) =
        ((χB (detA A g) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g, g)) h (delta A B Φ Φ)) q ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g _
    rw [e1, norm_mul, Circle.norm_coe, one_mul]
    exact norm_integral_le_integral_norm _
  refine ⟨C₁ * C₂ ^ N, 2 * c * N, fun g => ?_⟩
  have h2 : GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N ≤ (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := by
    refine pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ?_ N
    have := hC₂ g g
    rwa [← sq, ← pow_mul] at this
  calc ‖petersson B mH (fun h => thetaKO om g h Φ) (fun h => thetaKO om g h Φ)‖
      ≤ C₁ * GlobalTheory.Grow.height (dblSp A) (io A (g, g)) ^ N := (hpet g).trans (hE _)
    _ ≤ C₁ * (C₂ * GlobalTheory.Grow.height A g ^ (2 * c)) ^ N := mul_le_mul_of_nonneg_left h2 hC₁0
    _ = C₁ * C₂ ^ N * GlobalTheory.Grow.height A g ^ (2 * c * N) := by
        rw [mul_pow, ← pow_mul]; ring

end UpperTheory.Lit.Rallis.ThetaSq
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

theorem _root_.UpperTheory.Lit.Rallis.T.petersson_normSq_thetaKernel_moderateGrowth : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh → ThetaClause ψ A B χB om omh → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ Φ, IsThetaFunO ψ A B Φ → (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧ GlobalTheory.Grow.ModGrowth A fun g => GlobalTheory.Cusp.petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ := by
  first | exact @UpperTheory.Lit.Rallis.ThetaSq.normSq_thetaKO_modGrowth | exact UpperTheory.Lit.Rallis.ThetaSq.normSq_thetaKO_modGrowth | (intros; apply UpperTheory.Lit.Rallis.ThetaSq.normSq_thetaKO_modGrowth <;> assumption)
end

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

open GlobalTheory.Cusp

noncomputable section

namespace UpperTheory.Lit.Rallis.RallisIPProof
open GlobalTheory

theorem volQuot_pos {D : D7} (B : HSp D) (mH : Measure (GA D B)) [mH.IsHaarMeasure] :
    0 < (autMeasure B mH).real Set.univ := by
  have hfd := isFundamentalDomain_stdDom (GQ B) mH
  have h0 : mH (stdDom (GQ B)) ≠ 0 := hfd.measure_ne_zero (NeZero.ne mH)
  have hfin : IsFiniteMeasure (autMeasure B mH) := isFiniteMeasure_autMeasure
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  have hmk : Measurable (AutomorphicL2Unitary.mk (GQ B)) := by first | fun_prop | exact measurable_quotient_mk'' | exact measurable_quotient_mk' | exact AutomorphicL2Unitary.measurable_mk _
  show (Measure.map (AutomorphicL2Unitary.mk (GQ B)) (mH.restrict (stdDom (GQ B)))) Set.univ ≠ 0
  rw [Measure.map_apply hmk MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
  exact h0

theorem rallisInnerProductConvergent_of : GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.RallisInnerProductConvergent := by
  intro hDM hSWU hWC D A B hab hb2 hw ψ χA χB ω ωd hω hωd hTC a ha hI ν 𝓕 hcov θ C hθ hSig hCart m hm hmr mH hmH U hU hUc
    _hLow Φ₁ Φ₂ hΦ₁ hΦ₂ hK f₁ hf₁ f₂ hf₂
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  have hC : GlobalTheory.Published.CuspRapidDecay := GlobalTheory.RapidDecay.cuspRapidDecay
  have ha1 : 1 ≤ A.rank := by omega
  have hw' : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by rcases hw with h | h <;> omega
  obtain ⟨hφ, hid⟩ := hTC Φ₁ Φ₂ hΦ₁ hΦ₂
  have hmem := GlobalTheory.SwSecMem.swSec_mem_degPS hW D ψ A B χB ωd hωd ν 𝓕 hcov (delta A B Φ₁ Φ₂) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := hωd.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hDM1, -, hDM3⟩ := hDM D A (by omega) a ha hI χB⁻¹ B.rank hHk (resEta_inv hωd.resT) (sZero A B)
    (swSec A B ωd ν 𝓕 (delta A B Φ₁ Φ₂)) hmem
  have hA₁ : f₁ ∈ A0 θ A C := hf₁.1
  have hA₂ : f₂ ∈ A0 θ A C := hf₂.1
  have rd : ∀ u ∈ A0 θ A C, GlobalTheory.Grow.RapidDec A u := fun u hu =>
    GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (mem_cuspForms.1 hu).1.1 (mem_cuspForms.1 hu).1.2
  have rdc : ∀ u ∈ A0 θ A C, GlobalTheory.Grow.RapidDec A (fun g => conj (u g)) := fun u hu =>
    rd _ (GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 D θ A C hθ u hu)
  obtain ⟨hBI, -⟩ := hDM3 θ hθ hSig C hCart m hm f₁ hA₁ f₂ hA₂
  have hEF := hDM1.1.1
  have hZF : GlobalTheory.Eis.IsZetaFamily A χB⁻¹ m (flat A a (swSec A B ωd ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B)) f₁ f₂ :=
    ⟨hEF, fun s hs => (hBI s hs).1⟩
  have hEV := UpperTheory.Lit.Rallis.T.siegelWeil_convergent_range_kFinite_thetaFun hSWU hWC D ψ A B χB ωd hωd hab hb2 hw' a ha hI θ hθ ν 𝓕 hcov mH hmH _ hφ hK
  obtain ⟨-, hZV⟩ := GlobalTheory.Eis.zetaHolValueAt_of_eisValueAt D A χB⁻¹ hHk m hm _ hDM1.1
    (fun g => hEF.analyticOnNhd_flat g) hDM1.2 f₁ f₂ (rd _ hA₁) (rd _ hA₂) hZF (sZero A B) _ hEV

  have hKer : ∀ Φ, IsThetaFunO ψ A B Φ →
      Continuous (Function.uncurry fun g h => thetaKO ω g h Φ) ∧
      (∀ γ ∈ GQ A, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ) ∧
      (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO ω g h Φ) ∧
      (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO ω g h Φ) fun h => thetaKO ω g h Φ) ∧
      ∀ h, GlobalTheory.Grow.ModGrowth A fun g => thetaKO ω g h Φ := by
    intro Φ hΦ
    obtain ⟨hL2, hMG⟩ := UpperTheory.Lit.Rallis.T.petersson_normSq_thetaKernel_moderateGrowth hWC D ψ A B χA χB ω ωd hω hωd hTC ha1 hw mH hmH Φ hΦ
    refine ⟨hω.om_cont Φ hΦ 0, fun γ hγ g h => ?_, hL2, hMG, fun h => ?_⟩
    · have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hΦ)
    · obtain ⟨C, N, hCN⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ A B χA χB ω hω Φ hΦ
      refine ⟨C * GlobalTheory.Grow.height B h ^ N, N, fun g => (hCN g h).trans (le_of_eq ?_)⟩
      rw [mul_pow]; ring
  obtain ⟨i₁, i₂, l₁, l₂, hss⟩ := GlobalTheory.Core.Rk.Seesaw.seesaw_fubini D A B m mH hm hmH (fun g h => thetaKO ω g h Φ₁)
    (fun g h => thetaKO ω g h Φ₂) (fun K hK => by
      rcases hK with rfl | rfl
      exacts [hKer Φ₁ hΦ₁, hKer Φ₂ hΦ₂]) (fun g => conj (f₁ g)) (fun g => conj (f₂ g)) (rdc f₁ hA₁) (rdc f₂ hA₂)

  have key : ∀ g₁ g₂ h, thetaKO ω g₁ h Φ₁ * conj (thetaKO ω g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) * thetaKO ωd (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂) := by
    intro g₁ g₂ h
    rw [(hid g₁ g₂ h).2]
    have e : ((χB (detA A g₂) : Circle) : ℂ) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO ω g₁ h Φ₁ * conj (thetaKO ω g₂ h Φ₂))) * e
  have hpet : ∀ g₁ g₂, petersson B mH (fun h => thetaKO ω g₁ h Φ₁) (fun h => thetaKO ω g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) *
        ((((autMeasure B mH).real Set.univ : ℝ) : ℂ) * ThetaMean.thetaMean ωd mH (delta A B Φ₁ Φ₂) (io A (g₁, g₂))) := by
    intro g₁ g₂
    have e1 : petersson B mH (fun h => thetaKO ω g₁ h Φ₁) (fun h => thetaKO ω g₂ h Φ₂) =
        ((χB (detA A g₂) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO ωd (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂)) q
            ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g₁ g₂ _
    rw [e1, ← measure_smul_average, ThetaMean.thetaMean, Complex.real_smul]
  have hv : (((autMeasure B mH).real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (volQuot_pos B mH).ne'
  have hval : (((autMeasure B mH).real Set.univ : ℝ) : ℂ)⁻¹ *
      petersson B mH (RallisIP.thetaLift ω m Φ₁ f₁) (RallisIP.thetaLift ω m Φ₂ f₂) =
      GlobalTheory.Eis.dblInt A χB⁻¹ m (ThetaMean.thetaMean ωd mH (delta A B Φ₁ Φ₂)) f₁ f₂ := by
    have hss' : petersson B mH (RallisIP.thetaLift ω m Φ₁ f₁) (RallisIP.thetaLift ω m Φ₂ f₂) = _ := hss
    rw [hss', GlobalTheory.Eis.dblInt, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun q => ?_)
    simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, hpet, MonoidHom.inv_apply, Circle.coe_inv, inv_inv,
      RCLike.conj_conj]
    field_simp
  refine ⟨⟨i₁, l₁⟩, ⟨i₂, l₂⟩, hZF, ?_⟩
  rw [hval]
  exact hZV.2.valueAt

end UpperTheory.Lit.Rallis.RallisIPProof

end
end

theorem UpperTheory.Lit.rallisInnerProductConvergent (h₁ : GlobalTheory.Published.DoublingMethod) (h₂ : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (h₃ : GlobalTheory.Published.WeilThetaConvergence) : GlobalTheory.Published.RallisInnerProductConvergent :=
  UpperTheory.Lit.Rallis.RallisIPProof.rallisInnerProductConvergent_of h₁ h₂ h₃
