import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsViaGramMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

theorem det_uni {ρ : ℕ} {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) : Matrix.GeneralLinearGroup.det u = 1 := by
  have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular bt, Units.val_one]
  exact Finset.prod_eq_one fun i _ => (hu i i).2

theorem halfMod_uni {ρ : ℕ} (n : ℕ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n u = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, det_uni hu, map_one, NNReal.coe_one, Real.one_rpow]

theorem om_mul_left {S T : HSp D} (om : Om S T) (a b : GA D S) (f : WO S T → ℂ) :
    om (a * b, 1) f = om (a, 1) (om (b, 1) f) := by
  have h : ((a * b, 1) : GA D S × GA D T) = (a, 1) * (b, 1) := by simp
  rw [h, map_mul, Module.End.mul_apply]

section Source

variable {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {χW : (AE D)ˣ →* Circle}
  {om : Om V W} {om' : Om V₀ W} {μ : Measure (Mx D W.rank ρ)} {𝓕 : Set (Mx D W.rank ρ)} {f : WO V W → ℂ}

theorem mixS_levi_uni (hF : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasS d ψ χW om om' μ 𝓕 f) {u : GL (Fin ρ) (AE D)}
    (hu : u ∈ UX D ρ) (x : Mx D W.rank ρ) :
    d.mixS W ψ μ 𝓕 (om (d.levi u, 1) f) x = d.mixS W ψ μ 𝓕 f (x ⬝ u.1) := by
  rw [hF.levi, det_uni hu, halfMod_uni _ hu, map_one, inv_one]
  simp

theorem mixS_nB_zero (hF : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasS d ψ χW om om' μ 𝓕 f) (b : Mx D ρ V₀.rank)
    (x : Mx D W.rank ρ) : d.mixS W ψ μ 𝓕 (om (d.nB b, 1) f) x 0 = d.mixS W ψ μ 𝓕 f x (x ⬝ b) := by
  rw [hF.unip]
  simp only [heisO, zero_add, GlobalTheory.MixModel.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]

theorem mixS_nC (hF : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasS d ψ χW om om' μ 𝓕 f) (c : skewA D ρ) (x : Mx D W.rank ρ)
    (w : WO V₀ W) : d.mixS W ψ μ 𝓕 (om (d.nC c, 1) f) x w = ψ (d.qS W c x) * d.mixS W ψ μ 𝓕 f x w := by
  rw [hF.centre]
  rfl

end Source

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

theorem blocks_flag {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ V₀.rank)
    (c : skewA D ρ) :
    mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 ∧
    d.pX ⬝ (mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.j0) = u.1 ⬝ b ∧
    d.pX ⬝ (mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jY) = u.1 ⬝ (c.1 - half D • (b ⬝ plus V₀ b)) := by
  have hp : d.pX ⬝ mt V (d.levi u * (d.nB b * d.nC c)) =
      u.1 ⬝ (d.pX + c.1 ⬝ d.pY + b ⬝ d.p0 - (half D • (b ⬝ plus V₀ b)) ⬝ d.pY) := by
    rw [mt_mul, mt_mul, ← Matrix.mul_assoc, d.pX_levi, Matrix.mul_assoc, ← Matrix.mul_assoc d.pX, d.pX_nB]
    simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, d.pX_nC, d.wittDecomp_projAnisotropic_unipotentSkew, d.pY_nC]

  refine ⟨?_, ?_, ?_⟩
  · rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  · rw [← Matrix.mul_assoc, hp]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, d.pX_j0, d.pY_j0, d.p0_j0, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero, sub_zero]
  · rw [← Matrix.mul_assoc, hp]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, d.pX_jY, d.pY_jY, d.p0_jY, Matrix.mul_zero,
      Matrix.mul_one, zero_add, add_zero]

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

set_option maxHeartbeats 2000000 in

theorem rat_coords {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ V₀.rank)
    (c : skewA D ρ) (hγ : d.levi u * (d.nB b * d.nC c) ∈ GQ V) :
    u.1 ∈ ratMx D ρ ρ ∧ u.1 ⬝ b ∈ ratMx D ρ V₀.rank ∧ c.1 ∈ ratMx D ρ ρ := by
  set γ := d.levi u * (d.nB b * d.nC c) with hγdef
  obtain ⟨hX, h0, hY⟩ := blocks_flag d u b c
  rw [← hγdef] at hX h0 hY
  have hM : mt V γ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V γ).1 hγ
  have hMi : mt V γ⁻¹ ∈ ratMx D V.rank V.rank := (mem_GQ_iff V γ⁻¹).1 (inv_mem hγ)
  have hpX : d.pX ∈ ratMx D ρ V.rank := rat_mem _
  have hjX : d.jX ∈ ratMx D V.rank ρ := rat_mem _
  have hj0 : d.j0 ∈ ratMx D V.rank V₀.rank := rat_mem _
  have hjY : d.jY ∈ ratMx D V.rank ρ := rat_mem _
  have hu : u.1 ∈ ratMx D ρ ρ := by
    have e : d.pX ⬝ (mt V γ ⬝ d.jX) = u.1 := by rw [hX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul hpX (ratMx_mul hM hjX)
  have hui : (u⁻¹).1 ∈ ratMx D ρ ρ := by
    have e1 : mt V γ⁻¹ ⬝ d.jX = d.jX ⬝ (u⁻¹).1 := by
      calc mt V γ⁻¹ ⬝ d.jX = mt V γ⁻¹ ⬝ (d.jX ⬝ u.1) ⬝ (u⁻¹).1 := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = d.jX ⬝ (u⁻¹).1 := by rw [← hX, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have e : d.pX ⬝ (mt V γ⁻¹ ⬝ d.jX) = (u⁻¹).1 := by rw [e1, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    rw [← e]; exact ratMx_mul hpX (ratMx_mul hMi hjX)
  have hub : u.1 ⬝ b ∈ ratMx D ρ V₀.rank := by rw [← h0]; exact ratMx_mul hpX (ratMx_mul hM hj0)
  have hb : b ∈ ratMx D ρ V₀.rank := by
    have e : (u⁻¹).1 ⬝ (u.1 ⬝ b) = b := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [← e]; exact ratMx_mul hui hub
  have hc : c.1 ∈ ratMx D ρ ρ := by
    have e : c.1 = (u⁻¹).1 ⬝ (d.pX ⬝ (mt V γ ⬝ d.jY)) + half D • (b ⬝ plus V₀ b) := by
      have h2 : (u⁻¹).1 ⬝ (u.1 ⬝ (c.1 - half D • (b ⬝ plus V₀ b))) = c.1 - half D • (b ⬝ plus V₀ b) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      rw [hY, h2, sub_add_cancel]
    have hplus : plus V₀ b ∈ ratMx D V₀.rank ρ := by
      show giA V₀ ⬝ adj b ∈ ratMx D V₀.rank ρ
      exact ratMx_mul (rat_mem (V₀.gram⁻¹)) (ratMx_adj hb)
    rw [e]
    refine add_mem (ratMx_mul hui (ratMx_mul hpX (ratMx_mul hM hjY))) ?_
    show incA D (1 / 2) • (b ⬝ plus V₀ b) ∈ ratMx D ρ ρ
    exact ratMx_smul (1 / 2) (ratMx_mul hb hplus)
  exact ⟨hu, hub, hc⟩

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

variable {D : D7}

theorem continuous_periodic_integral {X : Type} [TopologicalSpace X] {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕) (G : X → Mx D m n → ℂ)
    (hG : Continuous (Function.uncurry G)) (hper : ∀ p, ∀ γ ∈ ratMx D m n, ∀ a, G p (γ + a) = G p a) :
    Continuous fun p => ∫ a in 𝓕, G p a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hint : ∀ p, IntegrableOn (G p) 𝓕 μ := fun p => covolOne_integrableOn h (G p) (hG.uncurry_left p) (hper p)
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev : ∀ᶠ p in nhds p₀, ∀ k ∈ K, ‖G p k - G p₀ k‖ < ε / 2 :=
    hK.eventually_forall_of_forall_eventually fun k hk => by
      have hca : ContinuousAt (fun q : X × Mx D m n => ‖Function.uncurry G q - G p₀ q.2‖) (p₀, k) :=
        (hG.sub ((hG.uncurry_left p₀).comp continuous_snd)).norm.continuousAt
      have h1 : ‖Function.uncurry G (p₀, k) - G p₀ (p₀, k).2‖ < ε / 2 := by
        rw [Function.uncurry_apply_pair, sub_self, norm_zero]; exact half_pos hε
      exact hca.eventually_lt continuousAt_const h1
  filter_upwards [hev] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint p₀)]
  have hb : ∀ a ∈ 𝓕, ‖G p a - G p₀ a‖ ≤ ε / 2 := fun a _ => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hper p γ hγ a, ← hper p₀ γ hγ a]
    exact (hp _ ha).le
  have h1 : μ 𝓕 = 1 := h.2.2
  calc ‖∫ a in 𝓕, (G p a - G p₀ a) ∂μ‖ ≤ ε / 2 * _ :=
        norm_setIntegral_le_of_norm_le_const (by rw [h1]; exact ENNReal.one_lt_top) hb
    _ < ε := by simp [Measure.real, h1]; linarith

end GlobalTheory.Unf.TermLaw

namespace GlobalTheory.Unf.TermLaw

theorem term_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) b (u : UX D ρ) c, term ψ d W vS (om (d.nC c * (d.nB b * d.levi u.1), 1) Ψ) x = ψ (d.qS W c (rat x)) * d.mixS W ψ vS.μ vS.𝓕 Ψ (rat x ⬝ u.1.1) (rat x ⬝ b)) ∧ (∀ γ ∈ GQ V, γ ∈ flagN d → ∀ x x' : Matrix (Fin W.rank) (Fin ρ) D.host.E, (rat x' : Mx D W.rank ρ) = rat x ⬝ blockX d γ → term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ x') ∧ (∀ δ ∈ GQ W, ∀ x x' : Matrix (Fin W.rank) (Fin ρ) D.host.E, mt W δ ⬝ (rat x' : Mx D W.rank ρ) = rat x → term ψ d W vS (om (1, δ) Ψ) x = term ψ d W vS Ψ x') ∧ (∀ x, Continuous fun p : GA D V × GA D W => term ψ d W vS (om p Ψ) x) ∧ HasSum (term ψ d W vS Ψ) (Ψ 0) := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hMS := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ V V₀ W ρ d χV χW om om' hW hW' vS.μ vS.𝓕 vS.covol
  have hMV := (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hstd).1 V V₀ W ρ d vS.μ vS.𝓕 vS.covol
  have thP : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (om p f) := hW.om_pres
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x b u c
    simp only [term]
    rw [om_mul_left, om_mul_left, mixS_nC d (hMS _ (thP _ _ (thP _ _ hΨ))), mixS_nB_zero d (hMS _ (thP _ _ hΨ)),
      mixS_levi_uni d (hMS _ hΨ) u.2]
  · intro γ hγQ hγN x x' hx'
    obtain ⟨u, hu, b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D V V₀ ρ d).1 γ).1 hγN
    obtain ⟨hru, hrub, hrc⟩ := rat_coords d u b c hγQ
    have hblk : blockX d (d.levi u * (d.nB b * d.nC c)) = u.1 := by
      rw [blockX, (blocks_flag d u b c).1, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    rw [hblk] at hx'
    simp only [term]
    rw [om_mul_left, om_mul_left, mixS_levi_uni d (hMS _ (thP _ _ (thP _ _ hΨ))) hu, mixS_nB_zero d (hMS _ (thP _ _ hΨ)),
      mixS_nC d (hMS _ hΨ), hx']
    have hxu : rat x ⬝ u.1 ∈ ratMx D W.rank ρ := ratMx_mul (rat_mem x) hru
    have hq : ψ (d.qS W c (rat x ⬝ u.1)) = 1 :=
      (((GlobalTheory.T.mixedModelCentralTerms_via_gramMatrices D).1 V V₀ W ρ d).2.2 ψ hstd).2.1 _ hxu c hrc
    obtain ⟨β, hβ⟩ := ratMx_mul (rat_mem x) hrub
    have hθ := (hMV Ψ hΨ (rat x ⬝ u.1)).quasi β 0
    rw [add_zero, GlobalTheory.MixModel.symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at hθ
    have hβ' : ratW W V₀ β = rat x ⬝ u.1 ⬝ b := by rw [ratW_eq, Matrix.mul_assoc]; exact hβ
    rw [hβ'] at hθ
    rw [hq, one_mul, hθ]
  · intro δ hδ x x' hx
    simp only [term]
    rw [(hMS _ hΨ).target δ (rat x)]
    have e : mt W δ⁻¹ ⬝ rat x = rat x' := by rw [← hx, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    rw [e]
    exact hW'.om_aut 1 (one_mem _) δ hδ _ (hMV Ψ hΨ _)
  · intro x
    have hψc : Continuous ψ := hstd.1.1
    have hJ := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ V W χV χW om hW Ψ hΨ
    have hY : Continuous (d.extY W) := continuous_id.matrix_mul continuous_const
    have hterm : (fun p => term ψ d W vS (om p Ψ) x) = fun p => ∫ a in vS.𝓕,
        ψ (symplOH V W (d.extY W a) (d.extX W (rat x))) * om p Ψ (d.extY W a + d.extX W (rat x) + d.ext0 W 0) ∂vS.μ := by
      funext p
      simp only [term, HypDec.mixS]
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => d.integrandS_eq _ _ _ _)
    rw [hterm]
    refine continuous_periodic_integral vS.covol
      (fun p a => ψ (symplOH V W (d.extY W a) (d.extX W (rat x))) * om p Ψ (d.extY W a + d.extX W (rat x) + d.ext0 W 0))
      ?_ ?_
    · refine (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_snd) continuous_const)).mul ?_
      exact hJ.comp (continuous_fst.prodMk (((hY.comp continuous_snd).add continuous_const).add continuous_const))
    · intro p γ hγ a
      have h := d.integrandS_periodic (thP p Ψ hΨ) (rat x) 0 γ hγ a
      rwa [d.integrandS_eq, d.integrandS_eq] at h
  · have h := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hstd V V₀ W ρ d vS Ψ hΨ).2.2.2.2 0
    rw [map_zero] at h
    exact h

end GlobalTheory.Unf.TermLaw
