import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepThetaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdjoinGelfandInvariantsDualPairEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPairStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantsActKernelFamilyShiftedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLiftConvergesContinuousGrowthDerivStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLiftGelfandInvariantFiniteOfFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebraStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

variable {D : D7} {θ : InfF D}

theorem IsKerSys.lift (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {V W : HSp D} {M : Type} [AddCommGroup M]
    [Module ℂ M] {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hq : IsQuot V μ 𝓕) {F : GA D V → ℂ} (hF : IsCuspForm θ V F) (f : M) :
    (∀ h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ IsAutFunSm θ W fun h => ∫ g in 𝓕, κ f g h * F g ∂μ := by
  have hD := GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms hP D θ hθ V F hF
  obtain ⟨h1, h2, ⟨N, h3⟩, h4⟩ := GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv D θ hθ V W M κ hκ μ 𝓕 hq F hD
  let L : M → GA D W → ℂ := fun f h => ∫ g in 𝓕, κ f g h * F g ∂μ
  have hd : ∀ f τ, ∀ X ∈ lieAt W τ, ∃ f', ∀ h,
      HasDerivAt (fun t : ℝ => L f (h * oneP θ W τ X t)) (L f' h) 0 := fun f τ X hX =>
    (hκ.derW τ X hX f).imp fun f' e => h4 τ X hX f f' e
  refine ⟨h1 f, ⟨fun γ hγ h => ?_, ?_, h2 f⟩, ?_, GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite D θ hθ V W M κ hκ μ 𝓕 hq F hD hF.1.zfin f, ?_⟩
  · have := fun g => hκ.left f 1 (one_mem _) γ hγ g h
    simp only [one_mul] at this
    simp only [this]
  · obtain ⟨U, U', -, hU', e⟩ := hκ.level f
    refine ⟨U', hU', fun k a b h => ?_⟩
    have := fun g => e 1 (one_mem _) (one_mem _) k a b g h
    simp only [mul_one] at this
    simp only [this]
  · refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ W (Set.range L) ?_ ?_ _ ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      exact h2 f
    · rintro _ ⟨f, rfl⟩ τ X hX
      obtain ⟨f', e⟩ := hd f τ X hX
      exact ⟨_, ⟨f', rfl⟩, e⟩
  · obtain ⟨K, hK⟩ := GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow D θ W
    refine ⟨K * N, fun l hl x => ?_⟩
    have hw : ∃ f', l.foldr (fun p φ => Rder θ W p.1 p.2 φ) (L f) = L f' := by
      induction l with
      | nil => exact ⟨f, rfl⟩
      | cons p l ih =>
        obtain ⟨f', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨f'', e'⟩ := hd f' p.1 p.2 (hl p List.mem_cons_self)
        exact ⟨f'', by rw [List.foldr_cons, e]; exact funext fun h => (e' h).deriv⟩
    obtain ⟨f', e⟩ := hw
    obtain ⟨C, hC⟩ := h3 f'
    obtain ⟨C', hC'⟩ := hK x
    refine ⟨|C| * C' ^ N, fun g hg => ?_⟩
    rw [show (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) = L f from rfl, e]
    refine (hC _).trans ?_
    rw [pow_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hC' g hg) N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _)

def matLin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A where
  toFun X := ∑ i, ∑ j, X i j • E i j
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

theorem matLin_single {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (i j : Fin n) :
    matLin E (Matrix.single i j 1) = E i j := by
  simp [matLin, Matrix.single, ite_and]

theorem isKerSys_thKer (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : GlobalTheory.Ker.IsWeak ψ S T om) (hc : OmCont ψ S T om) :
    IsKerSys θ S T (thKer ψ S T om) := by
  have cont : ∀ f, Continuous fun p : GA D S × GA D T => thKer ψ S T om f p.1 p.2 := fun f => hc f.1 f.2 0
  have left : ∀ f, ∀ γ ∈ GQ S, ∀ δ ∈ GQ T, ∀ g h, thKer ψ S T om f (γ * g) (δ * h) = thKer ψ S T om f g h := by
    intro f γ hγ δ hδ g h
    have e : om (γ * g, δ * h) = om (γ, δ) * om (g, h) := by rw [← map_mul]; rfl
    change om (γ * g, δ * h) f.1 0 = om (g, h) f.1 0
    rw [e]
    exact hw.om_aut γ hγ δ hδ _ (hw.om_pres _ _ f.2)
  have level : ∀ f, ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧
      IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → ∀ g h,
        thKer ψ S T om f (g * k) (h * k') = thKer ψ S T om f g h := by
    intro f
    obtain ⟨U, U', a, b, e⟩ := GlobalTheory.T.exists_open_level_fixing_theta_function D ψ hψ S T om hw hc f.1 f.2
    refine ⟨U, U', a, b, fun k h1 h2 k' h3 h4 g h => ?_⟩
    have e' : om (g * k, h * k') = om (g, h) * om (k, k') := by rw [← map_mul]; rfl
    change om (g * k, h * k') f.1 0 = om (g, h) f.1 0
    rw [e', Module.End.mul_apply, e k h1 h2 k' h3 h4]
  obtain ⟨x, d, hx⟩ := GlobalTheory.T.thetaKernel_lieAction_through_weylAlgebra D ψ hψ S T om hw hc θ hθ
  have derV : ∀ τ, ∀ X ∈ lieAt S τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ X t) h) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.2 X hX).elim fun _ e => ⟨_, e f⟩
  have derW : ∀ τ, ∀ X ∈ lieAt T τ, ∀ f, ∃ f', ∀ g h,
      HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om f' g h) 0 :=
    fun τ X hX f => ((hx τ).2.1 X hX).elim fun _ e => ⟨_, e f⟩
  refine ⟨cont, left, level, ?_, derV, derW, fun τ => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints D ψ hψ S T om hw θ hθ
    obtain ⟨N', hN'⟩ := GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair D θ hθ S T N
    exact ⟨N', fun f => hN' _ (left f) (level f) fun x y =>
      (hN f.1 f.2 x y).imp fun C e a ha b hb => e a ha b hb 0⟩
  · have sT : ∀ f g, thKer ψ S T om f g ∈ SmFun θ T := fun f g => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ T (Set.range fun f => thKer ψ S T om f g) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_right g)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derW τ X hX f
        exact ⟨_, ⟨f', rfl⟩, e g⟩
    have sS : ∀ f h, swapKer (thKer ψ S T om) f h ∈ SmFun θ S := fun f h => by
      refine GlobalTheory.T.mem_smoothFunctions_of_closed_rightDerivatives D θ hθ S (Set.range fun f => swapKer (thKer ψ S T om) f h) ?_ ?_ _ ⟨f, rfl⟩
      · rintro _ ⟨f, rfl⟩
        exact (cont f).comp (Continuous.prodMk_left h)
      · rintro _ ⟨f, rfl⟩ τ X hX
        obtain ⟨f', e⟩ := derV τ X hX f
        exact ⟨_, ⟨f', rfl⟩, fun g => e g h⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.T.glRel_of_canonicalCommutationRelations _ _ _ (x τ) (d τ) (hx τ).1
    obtain ⟨c, e1⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ T _ _ (thKer ψ S T om) sT τ (matLin fun i j => ∑ a, x τ (i, a) * d τ (j, a))
      (by simpa only [matLin_single] using g1) (hx τ).2.1
    obtain ⟨c', e2⟩ := GlobalTheory.T.gelfandInvariants_act_kernelFamily_shifted D θ hθ S _ _ (swapKer (thKer ψ S T om)) sS τ
      (matLin fun a b => -∑ i, x τ (i, b) * d τ (i, a)) (by simpa only [matLin_single] using g2)
      fun Y hY => ((hx τ).2.2 Y hY).imp fun _ e f h g => e f g h
    simp only [matLin_single] at e1 e2
    exact ⟨_, _, e2, e1, (GlobalTheory.T.adjoin_gelfandInvariants_dual_pair_eq _ _ _ (x τ) (d τ) (hx τ).1 c c').symm⟩

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem exists_thKer {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) {V W : HSp D}
    {χ χ' : IdC D} (ha : admitted V W χ χ') (hr : V.rank < W.rank) :
    ∃ om, GlobalTheory.Ker.IsWeak ψ V W om ∧ OmCont ψ V W om ∧
      ∀ Φ, ∃ f, ∀ g h, Wf.ker V W χ χ' Φ g h = thKer ψ V W om f g h := by
  obtain ⟨om, H, e⟩ := GlobalTheory.T.exists_orientedWeilDatum_of_adelicWeilRep_theta D ψ hψ V W χ χ' _ ha hr (Wf.core.weil V W χ χ' ha)
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W hr.le
  refine ⟨om, GlobalTheory.Ker.isWeak_of_datum H, H.om_cont, fun Φ => ⟨⟨fun x => Φ.1 (toTWsmall V W x), ?_⟩, fun g h => ?_⟩⟩
  · have := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
    simp only [hE] at this
    exact this
  · have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm

theorem liftAut : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAut D := by
  intro hP D θ hθ ψ hψ Wf V W χ χ' ha μ 𝓕 hq Φ F hF
  rcases lt_or_gt_of_ne ha.1 with hr | hr
  · obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha hr
    obtain ⟨f, e⟩ := e Φ
    simp only [e]
    exact (isKerSys_thKer hθ hψ hw hc).lift hP hθ hq hF f
  · have ha' : admitted W V χ' χ := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
    obtain ⟨om, hw, hc, e⟩ := exists_thKer hψ Wf ha' hr
    have hΦ := (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 ha.1 (mem_ThS.1 Φ.2)
    obtain ⟨f, e⟩ := e ⟨_, mem_ThS.2 hΦ⟩
    have e' : ∀ g h, Wf.ker V W χ χ' Φ g h = swapKer (thKer ψ W V om) f g h := fun g h =>
      (Wf.om_swap V W χ χ' ha g h Φ ⟨_, mem_ThS.2 hΦ⟩ (fun _ => rfl) 0).symm.trans (e h g)
    simp only [e']
    exact (isKerSys_thKer hθ hψ hw hc).swap.lift hP hθ hq hF f

end GlobalTheory.Mem.Lift

end
