import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicTypeAtExtremalOfKEquivariantLoweringK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift GlobalTheory.RawLift

namespace GlobalTheory.RawLift.FockCoef

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem integrable_pair (hom : IsWeilDatumO ψ S T χS χT om) (hc : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ}
    (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) : Integrable (fun w => star (a w) * b w) (μ.restrict 𝓕) := by
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  have h := GlobalTheory.WeilInner.integrable_mul_conj (μ.restrict 𝓕) hb.cont.measurable ha.cont.measurable
    (GlobalTheory.OrientedHeis.theta_bounded hom.std hb) (GlobalTheory.OrientedHeis.theta_bounded hom.std ha)
  exact h.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)

theorem thetaInner_add_right (hom : IsWeilDatumO ψ S T χS χT om) (hc : IsCovolOne (ratL T S) μ 𝓕) {a b b' : WO S T → ℂ}
    (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) (hb' : IsThetaFunO ψ S T b') :
    thetaIP μ 𝓕 a (b + b') = thetaIP μ 𝓕 a b + thetaIP μ 𝓕 a b' := by
  unfold thetaIP
  rw [← integral_add (integrable_pair hom hc ha hb) (integrable_pair hom hc ha hb')]
  simp only [Pi.add_apply, mul_add]

theorem continuous_coef (hom : IsWeilDatumO ψ S T χS χT om) (hc : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ}
    (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    Continuous fun g : GA D T => thetaIP μ 𝓕 a (om (1, g) b) := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable T
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds g₀
  obtain ⟨c, hc'⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom b hb _
    (hN.image (Continuous.prodMk_right (1 : GA D S)))
  obtain ⟨A, hA⟩ := GlobalTheory.OrientedHeis.theta_bounded hom.std ha
  refine continuousAt_of_dominated (bound := fun _ => A * c)
    (Filter.Eventually.of_forall fun g => (integrable_pair hom hc ha (hom.om_pres _ _ hb)).aestronglyMeasurable)
    ?_ (integrable_const _) (Filter.Eventually.of_forall fun w => ?_)
  · filter_upwards [hN₀] with g hg
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hA w) (hc' _ ⟨g, hg, rfl⟩ w) (norm_nonneg _) ((norm_nonneg _).trans (hA w))
  · exact (continuous_const.mul ((hom.om_cont b hb w).comp (Continuous.prodMk_right (1 : GA D S)))).continuousAt

theorem hasDerivAt_coef (hom : IsWeilDatumO ψ S T χS χT om) (hc : IsCovolOne (ratL T S) μ 𝓕) (hθ : IsInfFam θ)
    {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) {a b b' : WO S T → ℂ}
    (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) (hb' : IsThetaFunO ψ S T b')
    (hd : ∀ g w, HasDerivAt (fun t : ℝ => om (1, g * oneP θ T τ X t) b w) (om (1, g) b' w) 0) (g : GA D T) :
    HasDerivAt (fun t : ℝ => thetaIP μ 𝓕 a (om (1, g * oneP θ T τ X t) b)) (thetaIP μ 𝓕 a (om (1, g) b')) 0 := by
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds (0 : ℝ)
  have hp : Continuous fun t : ℝ => ((1 : GA D S), g * oneP θ T τ X t) :=
    continuous_const.prodMk (continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hX))
  obtain ⟨c, hc'⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ S T χS χT om hom b' hb' _ (hN.image hp)
  obtain ⟨A, hA⟩ := GlobalTheory.OrientedHeis.theta_bounded hom.std ha
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (bound := fun _ => A * c)
    (F := fun t w => star (a w) * om (1, g * oneP θ T τ X t) b w)
    (F' := fun t w => star (a w) * om (1, g * oneP θ T τ X t) b' w) hN₀
    (Filter.Eventually.of_forall fun t => (integrable_pair hom hc ha (hom.om_pres _ _ hb)).aestronglyMeasurable)
    (integrable_pair hom hc ha (hom.om_pres _ _ hb))
    (integrable_pair hom hc ha (hom.om_pres _ _ hb')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w t ht => by
      rw [norm_mul, norm_star]
      exact mul_le_mul (hA w) (hc' _ ⟨t, ht, rfl⟩ w) (norm_nonneg _) ((norm_nonneg _).trans (hA w)))
    (integrable_const _)
    (Filter.Eventually.of_forall fun w t _ =>
      (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (φ := fun g => om (1, g) b w) (φ' := fun g => om (1, g) b' w)
        (fun g => hd g w) g t).const_mul _)).2
  simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
  exact key

theorem exists_gen (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) : ∃ L : Module.End ℂ (WO S T → ℂ),
      ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (L f) ∧
        ∀ h g w, HasDerivAt (fun t : ℝ => om (h, g * oneP θ T τ X t) f w) (om (h, g) (L f) w) 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ X hX
  refine ⟨L, fun f hf => ⟨(hL f hf).1, fun h g w => ?_⟩⟩
  have := (hL f hf).2.2.2 (h, g) w
  simpa only [Prod.mk_mul_mk, mul_one] using this

theorem smooth_coef (hom : IsWeilDatumO ψ S T χS χT om) (hc : IsCovolOne (ratL T S) μ 𝓕) (hθ : IsInfFam θ)
    {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn T θ fun g => thetaIP μ 𝓕 a (om (1, g) b) := by
  refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T
    {φ | ∃ b, IsThetaFunO ψ S T b ∧ φ = fun g => thetaIP μ 𝓕 a (om (1, g) b)} ?_ ?_ _ ⟨b, hb, rfl⟩
  · rintro φ ⟨b, hb, rfl⟩
    exact continuous_coef hom hc ha hb
  · rintro φ ⟨b, hb, rfl⟩ τ X hX
    obtain ⟨L, hL⟩ := exists_gen hom hθ τ hX
    exact ⟨_, ⟨L b, (hL b hb).1, rfl⟩, hasDerivAt_coef hom hc hθ hX ha hb (hL b hb).1 ((hL b hb).2 1)⟩

theorem exists_op (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ) : ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f →
      (∀ h w, RderC θ T τ Z (fun g => om (h, g) f w) = fun g => om (h, g) (L f) w) ∧
      ∀ μ 𝓕, IsCovolOne (ratL T S) μ 𝓕 → ∀ a, IsThetaFunO ψ S T a →
        RderC θ T τ Z (fun g => thetaIP μ 𝓕 a (om (1, g) f)) = fun g => thetaIP μ 𝓕 a (om (1, g) (L f)) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  obtain ⟨L₁, e1⟩ := exists_gen hom hθ τ h1
  obtain ⟨L₂, e2⟩ := exists_gen hom hθ τ h2
  refine ⟨L₁ + Complex.I • L₂, fun f hf => ⟨fun h w => ?_, fun μ 𝓕 hc a ha => ?_⟩⟩
  · funext g
    simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply]
    rw [((e1 f hf).2 h g w).deriv, ((e2 f hf).2 h g w).deriv]
    simp
  · funext g
    simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply]
    rw [(hasDerivAt_coef hom hc hθ h1 ha hf (e1 f hf).1 ((e1 f hf).2 1) g).deriv,
      (hasDerivAt_coef hom hc hθ h2 ha hf (e2 f hf).1 ((e2 f hf).2 1) g).deriv,
      LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
      thetaInner_add_right hom hc ha (hom.om_pres _ _ (e1 f hf).1)
        (GlobalTheory.OrientedHeis.theta_smul _ (hom.om_pres _ _ (e2 f hf).1)), thetaInner_smul_right, smul_eq_mul]

variable {Sp : D.what₂.Tau → SPar}

def Killed (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (M : DSModel T Sp) (f : WO S T → ℂ) : Prop :=
  ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h w, RderC θ T τ Z (fun g => om (h, g) f w) = 0

theorem Killed.coef (hom : IsWeilDatumO ψ S T χS χT om) (hc : IsCovolOne (ratL T S) μ 𝓕) (hθ : IsInfFam θ)
    {M : DSModel T Sp} {a f : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hf : IsThetaFunO ψ S T f) (hk : Killed om θ M f)
    (τ : D.what₂.Tau) (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ) (hZ : Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ) :
    RderC θ T τ Z (fun g => thetaIP μ 𝓕 a (om (1, g) f)) = 0 := by
  obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
  rw [(hL f hf).2 μ 𝓕 hc a ha]
  funext g
  have e : om (1, g) (L f) = 0 := funext fun w => congrFun (((hL f hf).1 1 w).symm.trans (hk τ Z hZ 1 w)) g
  simp [e, thetaIP]

open GlobalTheory.FockKill GlobalTheory.FockIndep GlobalTheory.OrientedHeis in

theorem killed_of_harmonic (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (kS : S.SigOK) (kT : T.SigOK)
    (BS : D.what₂.Tau → Mt S.rank) (hBS : ∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) (M : DSModel T Sp)
    (p : D.what₂.Tau → ℕ) (hp : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) (P : PolF D T.rank S.rank)
    (hP : ∀ τ, ∀ a b : Fin T.rank, p τ ≤ (a : ℕ) → (b : ℕ) < p τ →
      ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) :
    Killed om θ M (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) := by
  intro τ Z hZ h w
  have hψ := hom.std
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨h1, h2⟩ := pMinus_laws hZ
  obtain ⟨ha, eY⟩ := parts (GlobalTheory.SmoothAutCheck.gramAt_unit T τ) (hT τ) h1 h2
  obtain ⟨lX, lY⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  unfold RderC
  unfold conjAt at lX lY ⊢
  rw [eY] at lY ⊢
  generalize (1 / 2 : ℂ) • (Z + -((gramAt D T τ)⁻¹ * Zᴴ * gramAt D T τ)) = X at ha lX lY
  obtain ⟨GX, hX⟩ : ∃ G, IsGen ψ om θ τ X G := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lX
  obtain ⟨GY, hY⟩ : ∃ G, IsGen ψ om θ τ (Complex.I • (cart M τ * X)) G :=
    GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lY
  have hφ : IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) :=
    pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
      (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
  have key := gen_kill hψ hθ hB (hp τ) hX hY lX lY ha hf (hv τ)
    (gen_kill_vac hom hθ kS kT hS hT hX hY lX lY ha hf hv) (hP τ)
  generalize pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P = φ at key hφ
  funext g
  have a1 := ((hX φ hφ).2.2.2 (h, g) w).deriv
  have a2 := ((hY φ hφ).2.2.2 (h, g) w).deriv
  simp only [Prod.mk_mul_mk, mul_one] at a1 a2
  have a3 := congrFun (congrArg (om (h, g)) key) w
  rw [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, map_zero] at a3
  simp only [Pi.add_apply, Pi.smul_apply, Rder]
  rw [a1, a2]
  exact a3

def killedSub (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (M : DSModel T Sp) {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (pt : Y →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) : Submodule ℂ Y where
  carrier := {P | Killed om θ M (pt P)}
  add_mem' := by
    intro P Q hP hQ τ Z hZ h w
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h w
    have b := hQ τ Z hZ h w
    rw [(hL _ (hpt _)).1] at a b ⊢
    funext g
    have a' := congrFun a g
    have b' := congrFun b g
    simp only [map_add, Pi.add_apply, Pi.zero_apply] at a' b' ⊢
    rw [a', b', add_zero]
  zero_mem' := by
    intro τ Z _ h w
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    rw [(hL _ (hpt _)).1]
    funext g
    simp
  smul_mem' := by
    intro r P hP τ Z hZ h w
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h w
    rw [(hL _ (hpt _)).1] at a ⊢
    funext g
    have a' := congrFun a g
    simp only [map_smul, Pi.smul_apply, Pi.zero_apply] at a' ⊢
    rw [a', smul_zero]

open GlobalTheory.DefLift.LowerKill GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate in

theorem values_killed (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (M : DSModel T Sp) (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (c : CoefA S) (hc : c.Is) (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ))
    (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) (Δ : PolF D T.rank S.rank)
    (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank) (hio : IsIoW θ M c om (fun P => pt P) Δ io)
    (hΔ : Killed om θ M (pt Δ)) (v : ∀ ρ, lowT M ρ) (w : c.W) :
    Killed om θ M (pt (io (PiTensorProduct.tprod ℂ v) w)) := by
  classical
  obtain ⟨hS, hK, v₀, w₀, hv₀, hw₀, e₀⟩ := hio
  beta_reduce at hS hK
  let N := killedSub hom hθ M pt hpt
  have step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N := by
    obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    suffices hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤
        N.comap (io (PiTensorProduct.tprod ℂ v₀)) by
      intro w
      refine (((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top :
        w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))
      have hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
        show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N
        rw [e₀]
        exact hΔ
      rw [h0, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw₀
      exact zero_ne_one hw₀
    · rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := hd g
      intro τ Z hZ h y
      have e : (fun g => om (h, g) (pt (io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x))) y) =
          fun g => om (h * u, g) (pt (io (PiTensorProduct.tprod ℂ v₀) x)) y := by
        funext g
        rw [map_mul, hc.1 a ha, one_mul, ← hS u hu]
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e]
      exact hx τ Z hZ (h * u) y
  let B : MultilinearMap ℂ (fun τ => lowT M τ) (PolF D T.rank S.rank) :=
    (io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)
  refine mem_of_translates h1 h2 B N v₀ (fun ρ h0 => ?_) (step1 w) ?_ v
  · have := hv₀ ρ
    rw [h0] at this
    simp at this
  · intro ρ k hk v u hu hv τ Z hZ h y
    have e : (fun g => om (h, g) (pt (B (Function.update v ρ u))) y) =
        rTr T (atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) fun g => om (h, g) (pt (B v)) y := by
      funext g
      have := hK ρ k hk v u hu w
      show om (h, g) (pt (io (PiTensorProduct.tprod ℂ (Function.update v ρ u)) w)) y =
        om (h, g * atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) y
      rw [← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e, RderC_rTr hθ (isRealPt_atTau hθ ρ (frame_mem_UH M ρ hk)), hv τ _ (adAt_mem_pMinus hθ M ρ τ hk hZ) h y]
    rfl

theorem thetaInner_star (a b : WO S T → ℂ) : star (thetaIP μ 𝓕 a b) = thetaIP μ 𝓕 b a := by
  unfold thetaIP
  rw [Complex.star_def, ← integral_conj]
  congr 1
  funext w
  simp [mul_comm]

theorem holAd_coef (hom : IsWeilDatumO ψ S T χS χT om) (hcv : IsCovolOne (ratL T S) μ 𝓕) (hθ : IsInfFam θ)
    (M : DSModel T Sp) (hM : HolShape M) {wt : D.what₂.Tau → Fin T.rank → ℤ} (hw : WtIs M wt)
    (c : CoefA S) (hc : c.Is) (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ))
    (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) (Δ : PolF D T.rank S.rank)
    (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank) (hio : IsIoW θ M c om (fun P => pt P) Δ io)
    (hΔ : Killed om θ M (pt Δ)) (v : ∀ ρ, lowT M ρ) (hv : IsExtVec M fun ρ => (v ρ : M.sm ρ)) (w : c.W)
    {a : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) :
    HolAd θ M wt fun g => thetaIP μ 𝓕 a (om (1, g) (pt (io (PiTensorProduct.tprod ℂ v) w))) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D T Sp M hM
  let U₀ : LowT M →ₗ[ℂ] (GA D T → ℂ) :=
    { toFun := fun e g => thetaIP μ 𝓕 a (om (1, g) (pt (io e w)))
      map_add' := fun e e' => by
        funext g
        simp only [map_add, LinearMap.add_apply, Pi.add_apply]
        exact thetaInner_add_right hom hcv ha (hom.om_pres _ _ (hpt _)) (hom.om_pres _ _ (hpt _))
      map_smul' := fun r e => by
        funext g
        simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        exact thetaInner_smul_right _ _ _ _ _ }
  let U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M := U₀.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hU : ∀ e, U e = fun g => thetaIP μ 𝓕 a (om (1, g) (pt (io (PiTensorProduct.tprod ℂ e) w))) := fun _ => rfl
  refine GlobalTheory.KMapHol.holAd_of_kEquiv D θ T Sp M wt hθ hM hw h1 h2 U (fun e => smooth_coef hom hcv hθ ha (hpt _))
    (fun τ k hk e u hu => ?_)
    (fun τ Z hZ e => (values_killed hom hθ M h1 h2 c hc pt hpt Δ io hio hΔ e w).coef hom hcv hθ ha (hpt _) τ Z hZ) v hv
  funext g
  have := hio.2.1 τ k hk e u hu w
  beta_reduce at this
  simp only [hU, rTr]
  rw [← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

open GlobalTheory.HolDict.InterpolationCoefficientsInL2 in

theorem coef_eq (hom : IsWeilDatumO ψ S T χS χT om) (hcv : IsCovolOne (ratL T S) μ 𝓕) (hθ : IsInfFam θ)
    (M : DSModel T Sp) (hS : HolShape M) {w : D.what₂.Tau → Fin T.rank → ℤ} (hW : WtIs M w) {v : M.Vec}
    (hv : IsExtVec M v) {J : WO S T → ℂ} (hJ : IsThetaFunO ψ S T J)
    (hφ : ∀ a, IsThetaFunO ψ S T a → HolAd θ M w fun g => thetaIP μ 𝓕 a (om (1, g) J)) (u₀ : GA D T) (hu₀ : u₀ ∈ GinfC T) :
    thetaIP μ 𝓕 J (om (1, u₀) J) =
      thetaIP μ 𝓕 J J * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (Formalism.L2.Pj.archM T (θ τ) u₀) (v τ : M.H τ)⟫_ℂ := by
  classical
  refine (GlobalTheory.RealLift.exists_real_lift D θ T hθ).elim fun L hL => ?_
  have hL1 := hL.1
  have hLmul := hL.2.1
  have hUG := hL.2.2.2.1
  have hLinv := hL.2.2.2.2.1
  have hB := (GlobalTheory.HolDict.holFn_coef_extVec D θ T Sp M w v hθ hS hW hv).1
  have hBt := (GlobalTheory.HolDict.holFn_coef_extVec D θ T Sp M w v hθ hS hW hv).2
  have hO : ∀ τ, OrthFr (gramAt D T τ) (nNeg (M.ε τ)) (x0Mat M τ) :=
    fun τ => ((GlobalTheory.HolDict.ModelRep.model_rep D T Sp M τ).2.2.2 hS).1
  have hU : ∀ τ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D T τ)) (M.rep τ) :=
    fun τ => (GlobalTheory.HolDict.ModelRep.model_rep D T Sp M τ).2.1
  have htm : ∀ s, torEl (x0Mat M) s ∈ UG (gramAt D T) := fun s => by
    simpa using TorusLaw.mul_torEl_mem hO s (one_mem_UG (Hm := gramAt D T))
  have hL0 : L 1 = 1 := by
    have h := hLmul 1 one_mem_UG 1 one_mem_UG
    rw [mul_one] at h
    exact mul_left_cancel (a := L 1) (by rw [← h, mul_one])
  have h11 : om (1, 1) J = J := by
    rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply]
  have horb : ∀ a, IsThetaFunO ψ S T a →
      HolFn (gramAt D T) (fun τ => nNeg (M.ε τ)) (x0Mat M) w fun u => thetaIP μ 𝓕 a (om (1, L u) J) := by
    intro a ha
    obtain ⟨f, hf, hfx⟩ := hφ a ha 1
    refine holFn_congr hf fun u hu => ?_
    have := hfx _ (hL1 u hu).1
    beta_reduce at this
    rw [one_mul] at this
    rw [this]
    congr 1
    funext τ
    exact (hL1 u hu).2 τ
  have htor : ∀ s a, IsThetaFunO ψ S T a →
      thetaIP μ 𝓕 a (om (1, L (torEl (x0Mat M) s)) J) = torCh w s * thetaIP μ 𝓕 a J := by
    intro s a ha
    obtain ⟨h1, h2⟩ := GlobalTheory.HolDict.smFn_and_killedFn_of_holFn _ _ _ _ _ _ hO _ (horb a ha)
    have := GlobalTheory.HolDict.torus_law_of_killed _ _ _ _ _ _ hO _ h1 h2 1 one_mem_UG s
    beta_reduce at this
    rwa [one_mul, hL0, h11] at this
  have key := eq_const_mul hO (thetaIP μ 𝓕 J J) (horb J hJ) hB
    (fun u hu s => by
      beta_reduce
      have e : om (1, L (torEl (x0Mat M) s * u)) J = om (1, L (torEl (x0Mat M) s)) (om (1, L u) J) := by
        rw [hLmul _ (htm s) _ hu, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      have a1 := htor s _ (hom.om_pres (1, L (torEl (x0Mat M) s)) _ (hom.om_pres (1, L u) _ hJ))
      rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (hom.om_pres _ _ hJ) hJ] at a1
      have a2 := congrArg star a1
      rw [star_mul', thetaInner_star, thetaInner_star] at a2
      have a3 : torCh w s * star (torCh w s) = 1 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_torCh]; simp
      rw [e, a2, ← mul_assoc, a3, one_mul])
    (fun u hu s => by
      have a2 : ∀ τ, ⟪(v τ : M.H τ), M.rep τ ((torEl (x0Mat M) s * u) τ) (v τ : M.H τ)⟫_ℂ =
          (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) * ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := by
        intro τ
        refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ)
          ((hU τ).1.2 _ (htm s τ) _ (hu τ))).trans ?_
        exact inner_iso_eigen _ ((hU τ).2.1 _ (htm s τ)) (norm_prod_exp _ _) (hBt s τ) _
      exact (Finset.prod_congr rfl fun τ _ => a2 τ).trans Finset.prod_mul_distrib)
    (by beta_reduce; rw [hL0, h11])
    (Finset.prod_eq_one fun τ _ => by
      refine (congrArg (fun T : M.H τ →L[ℂ] M.H τ => ⟪(v τ : M.H τ), T (v τ : M.H τ)⟫_ℂ) (hU τ).1.1).trans ?_
      change ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
      simp)
    _ (hUG u₀)
  beta_reduce at key
  rwa [hLinv u₀ hu₀] at key

set_option maxHeartbeats 1000000 in

theorem coef_extremal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), Formalism.IndefR.FWT.IsExtVec (R.MW i (sg0 D A)) (fun ρ => ((v ρ : (R.MW i (sg0 D A)).sm ρ))) → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hR _ i t μ 𝓕 hcv v hext w u hu
  have hm := hR.models
  have hω := hR.thP.ωP
  have hv := hR.thP.vP
  have hp := hR.thP.pt_theta
  have hio := hR.thP.ioP
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hp i t 1
    rwa [RealDat.ptP, GlobalTheory.DefLift.ThetaMap.pureTensorO_one] at this
  obtain ⟨hM, wt, hw⟩ := GlobalTheory.DefLift.holShape_fixed D G Pl0 T A Ks R hm.order i
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 ≤ (Vc D i).rank := fun τ => by
    have e := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    have e' := rank_Wc i
    have := r_le_V i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e
    omega
  have hΔ := killed_of_harmonic (hω i t) hm.inf (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hm.BV i) (R.MW i (sg0 D A)) (fun τ => ((Wc D i).sig (tauE D τ)).1) (hm.order i) (R.vP i t) hth
    (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) hth) (RealDat.Delta i)
    (fun τ => GlobalTheory.T.mixed_laplacian_kills_product_of_minors D _ _ _ _ _ _ hpq τ)
  exact coef_eq (hω i t) hcv hm.inf _ hM hw hext (hp i t _) (fun a ha =>
    holAd_coef (hω i t) hcv hm.inf _ hM hw _ (hm.cV i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
        (R.vP i t)) (hp i t) _ _ (hio i t) hΔ v hext w ha) u hu

end GlobalTheory.RawLift.FockCoef

end
