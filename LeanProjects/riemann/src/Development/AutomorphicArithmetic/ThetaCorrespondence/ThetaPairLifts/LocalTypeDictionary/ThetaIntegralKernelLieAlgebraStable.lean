import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareCommutativityProjection
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ThetaKFactor
open MeasureTheory GlobalTheory.SquareComm
variable {D : D7}
private theorem thetaKernel_right_translate {M X : HSp D} (ω : GlobalTheory.Grid.WRep M X) (g : GA D M) (h h' : GA D X) (Φ : WO M X → ℂ) :
    thetaKO ω g h (ω (1, h') Φ) = thetaKO ω g (h * h') Φ := by
  show ω (g, h) (ω (1, h') Φ) 0 = ω (g, h * h') Φ 0
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
private theorem theta_integral_right_translate {M X : HSp D} (ω : GlobalTheory.Grid.WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (h' : GA D X)
    (Φ : WO M X → ℂ) (h : GA D X) : thetaInt ω ν 𝓕 (ω (1, h') Φ) h = thetaInt ω ν 𝓕 Φ (h * h') := by
  simp only [thetaInt, thetaKernel_right_translate]
private theorem theta_integral_zero {M X : HSp D} (ω : GlobalTheory.Grid.WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) :
    thetaInt ω ν 𝓕 0 = 0 := by
  funext h
  simp [thetaInt, thetaKO]
private theorem theta_integral_add {M X : HSp D} (ω : GlobalTheory.Grid.WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (Φ Ψ : WO M X → ℂ)
    (hΦ : ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν) (hΨ : ∀ h, IntegrableOn (fun g => thetaKO ω g h Ψ) 𝓕 ν) :
    thetaInt ω ν 𝓕 (Φ + Ψ) = thetaInt ω ν 𝓕 Φ + thetaInt ω ν 𝓕 Ψ := by
  funext h
  have e : (fun g => thetaKO ω g h (Φ + Ψ)) = fun g => thetaKO ω g h Φ + thetaKO ω g h Ψ := by
    funext g; simp [thetaKO]
  simp only [thetaInt, Pi.add_apply]
  rw [show (fun g => thetaKO ω g h (Φ + Ψ)) = _ from e, integral_add (hΦ h) (hΨ h)]
private theorem theta_integral_smul {M X : HSp D} (ω : GlobalTheory.Grid.WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M)) (c : ℂ)
    (Φ : WO M X → ℂ) : thetaInt ω ν 𝓕 (c • Φ) = c • thetaInt ω ν 𝓕 Φ := by
  funext h
  simp [thetaInt, thetaKO, integral_const_mul]
private theorem exists_haar_fundamental_domain (V : HSp D) : ∃ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), IsHaarFD V ν 𝓕 := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.2
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V (Measure.haar) inferInstance
  exact ⟨_, 𝓕, inferInstance, h𝓕⟩
end GlobalTheory.ThetaKFactor
namespace GlobalTheory.ThetaKFactor
open MeasureTheory GlobalTheory.SquareComm
variable {D : D7}
theorem integrable_theta_of_mem_kFiniteVectors (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : GlobalTheory.ChainFr.Fr W) (B : GlobalTheory.ChainFr.Fr X)
    {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    (hν : IsHaarFD W ν 𝓕) {ωA : GlobalTheory.Grid.WRep W X} (hω : GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA)
    {Φ : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (h : GA D X) :
    IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := by
  obtain ⟨p, q, hsig, hbig, -⟩ := hT.sig
  have hlt : X.rank < 2 * (W.rank - p) := by have := hT.rank; omega
  obtain ⟨N, C, hC⟩ := _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence hP.siegelSetUnitary hP D ψ θ hθ true W X β (β / α) ωA hω p
    ⟨D.eTau.symm 1, (hsig _).1⟩ hlt ν 𝓕 hν Φ (GlobalTheory.TripleWeilTransfer.isThetaFunO_of_mem_algF hψ hθ true A B hΦ)
  exact (hC h).1
theorem exists_kFactor_of_thetaIntegral (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁)
    (B : GlobalTheory.ChainFr.Fr X) {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν : Measure (GA D W)}
    {𝓕 : Set (GA D W)} (hν : IsHaarFD W ν 𝓕) {ωA ωB Pi rf rl p p'}
    (hM : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') :
    ∃ J₀ : Pi →ₗ[ℂ] (GA D X → ℂ), ∀ Φ ∈ algF ψ θ true A B, thetaInt ωA ν 𝓕 Φ = J₀ (p Φ) := by
  obtain ⟨ν₁, 𝓕₁, hν₁⟩ := exists_haar_fundamental_domain W₁
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁
    ωA ωB Pi rf rl p p' hM
  obtain ⟨Φ₀, -, hrel, -, hI⟩ := hc 0 (Submodule.zero_mem _)
  have hrelker : finRel ωB (algF ψ θ false A₁ B) ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    simp [LinearMap.mem_ker, hM.mapB.invf u hu Ψ hΨ]
  have hp0 : p' Φ₀ = 0 := by
    have := hrelker hrel
    simpa using this
  have hker : ∀ Φ ∈ algF ψ θ true A B, p Φ = 0 → thetaInt ωA ν 𝓕 Φ = 0 := by
    intro Φ hΦ hpΦ
    rw [hI Φ hΦ (by rw [hpΦ, hp0]), ← hI 0 (Submodule.zero_mem _) (by rw [map_zero, hp0]), theta_integral_zero]
  let S := algF ψ θ true A B
  let L : S →ₗ[ℂ] (GA D X → ℂ) :=
    { toFun := fun Φ => thetaInt ωA ν 𝓕 Φ.1
      map_add' := fun Φ Ψ => theta_integral_add ωA ν 𝓕 Φ.1 Ψ.1
        (_root_.GlobalTheory.ThetaKFactor.integrable_theta_of_mem_kFiniteVectors hP hψ hθ A B hT hν hM.weilA Φ.2)
        (_root_.GlobalTheory.ThetaKFactor.integrable_theta_of_mem_kFiniteVectors hP hψ hθ A B hT hν hM.weilA Ψ.2)
      map_smul' := fun c Φ => theta_integral_smul ωA ν 𝓕 c Φ.1 }
  let pS : S →ₗ[ℂ] Pi := p ∘ₗ S.subtype
  have hsurj : Function.Surjective pS := by
    intro x
    have hx : x ∈ S.map p := by rw [hM.mapA.onto]; trivial
    obtain ⟨Φ, hΦ, rfl⟩ := Submodule.mem_map.1 hx
    exact ⟨⟨Φ, hΦ⟩, rfl⟩
  have hle : LinearMap.ker pS ≤ LinearMap.ker L := by
    intro Φ hΦ
    exact hker Φ.1 Φ.2 hΦ
  refine ⟨(LinearMap.ker pS).liftQ L hle ∘ₗ (pS.quotKerEquivOfSurjective hsurj).symm.toLinearMap, fun Φ hΦ => ?_⟩
  have e : (pS.quotKerEquivOfSurjective hsurj).symm (p Φ) = Submodule.Quotient.mk ⟨Φ, hΦ⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.liftQ_apply]
  rfl
private theorem hasDerivAt_integral_second_derivative {G : Type} [MeasurableSpace G] (μ : Measure G) [SFinite μ] (F F' F'' : ℝ → G → ℂ)
    (hd : ∀ g t, HasDerivAt (fun s => F s g) (F' t g) t) (hd' : ∀ g t, HasDerivAt (fun s => F' s g) (F'' t g) t)
    (hc : ∀ g, Continuous fun t => F'' t g) (hm : Measurable fun p : G × ℝ => F'' p.2 p.1)
    (hi : ∀ t, Integrable (F t) μ) (hi' : Integrable (F' 0) μ) (hi'' : ∀ t, Integrable (F'' t) μ) (C : ℝ)
    (hC : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∫ g, ‖F'' t g‖ ∂μ ≤ C) :
    HasDerivAt (fun t => ∫ g, F t g ∂μ) (∫ g, F' 0 g ∂μ) 0 := by
  set ν : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1) with hν
  have hsm : AEStronglyMeasurable (fun p : G × ℝ => F'' p.2 p.1) (μ.prod ν) := hm.aestronglyMeasurable
  have hI : Integrable (fun p : G × ℝ => F'' p.2 p.1) (μ.prod ν) := by
    refine (integrable_prod_iff' hsm).2 ⟨.of_forall fun t => hi'' t, ?_⟩
    refine Integrable.mono' (integrable_const C) (hm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (.of_forall fun t ht => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun g => norm_nonneg _)]
    exact hC t ht
  have hB : Integrable (fun g => ‖F' 0 g‖ + ∫ u, ‖F'' u g‖ ∂ν) μ := hi'.norm.add hI.integral_norm_prod_left
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ)) (F := F) (F' := F')
    (bound := fun g => ‖F' 0 g‖ + ∫ u, ‖F'' u g‖ ∂ν) (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)
    (.of_forall fun t => (hi t).aestronglyMeasurable) (hi 0) hi'.aestronglyMeasurable
    (.of_forall fun g t ht => ?_) hB (.of_forall fun g t _ => hd g t)).2
  have e : ∫ u in (0 : ℝ)..t, F'' u g = F' t g - F' 0 g :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => F' s g) (fun u _ => hd' g u)
      ((hc g).intervalIntegrable _ _)
  have h1 : ‖∫ u in (0 : ℝ)..t, F'' u g‖ ≤ ∫ u, ‖F'' u g‖ ∂ν := by
    refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_
    refine setIntegral_mono_set ((hc g).norm.integrableOn_Icc) (.of_forall fun u => norm_nonneg _) ?_
    refine HasSubset.Subset.eventuallyLE (Set.uIoc_subset_uIcc.trans ?_)
    exact Set.uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht
  have e2 : F' t g = F' 0 g + ∫ u in (0 : ℝ)..t, F'' u g := by rw [e]; ring
  rw [e2]
  exact (norm_add_le _ _).trans (by gcongr)
private theorem hasDerivAt_theta_integral {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {ε : Bool} {M X : HSp D}
    {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X} (hω : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) {ν : Measure (GA D M)}
    {𝓕 : Set (GA D M)} (hν : IsHaarFD M ν 𝓕) (hmod : ∀ Φ, IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X Φ → ModInt θ ω ν 𝓕 Φ)
    {τ : D.what₂.Tau} {Y : Matrix (Fin X.rank) (Fin X.rank) ℂ} (hY : Y ∈ lieAt X τ) {Φ : WO M X → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X Φ) (h : GA D X) :
    HasDerivAt (fun t : ℝ => thetaInt ω ν 𝓕 Φ (h * oneP θ X τ Y t))
      (thetaInt ω ν 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT (V := GlobalTheory.Grid.sgn ε M) θ (ω.toSgn ε) τ Y Φ) h) 0 := by
  have hω' : IsWeilDatumO ψ (GlobalTheory.Grid.sgn ε M) X χ χ' (ω.toSgn ε) := hω
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D X
  have hν1 := hν.1
  obtain ⟨ht, hd⟩ := GlobalTheory.Chain.LiftReg.tame_dOmT hθ hω' hY
  have hth : ∀ f, IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f →
      IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X (GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT (V := GlobalTheory.Grid.sgn ε M) θ (ω.toSgn ε) τ Y f) := fun f hf => ht.theta (x := f) hf
  have hco : Continuous fun t : ℝ => h * oneP θ X τ Y t := continuous_const.mul (GlobalTheory.Mem.Lift.continuous_oneP hθ hY)
  have hder : ∀ f, IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f → ∀ (g : GA D M) (t : ℝ),
      HasDerivAt (fun s : ℝ => thetaKO ω g (h * oneP θ X τ Y s) f)
        (thetaKO ω g (h * oneP θ X τ Y t) (GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT (V := GlobalTheory.Grid.sgn ε M) θ (ω.toSgn ε) τ Y f)) t := by
    intro f hf g t
    have h1 := hd f hf ((GlobalTheory.Grid.ofSgn ε M).symm g, h * oneP θ X τ Y t) 0
    rw [← sub_self t] at h1
    have h2 := HasDerivAt.comp_sub_const t t h1
    refine h2.congr_of_eventuallyEq (.of_forall fun s => ?_)
    simp only [Prod.mk_mul_mk, mul_one, mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hY, add_sub_cancel]
    rfl
  have hcont : ∀ f, IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f →
      Continuous fun p : GA D M × ℝ => thetaKO ω p.1 (h * oneP θ X τ Y p.2) f := fun f hf =>
    (hω'.om_cont f hf 0).comp
      (((GlobalTheory.Grid.continuous_ofSgn_symm ε M).comp continuous_fst).prodMk (hco.comp continuous_snd))
  set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT (V := GlobalTheory.Grid.sgn ε M) θ (ω.toSgn ε) τ Y Φ with e₁
  have hΦ₁ := hth Φ hΦ
  set Φ₂ := GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT (V := GlobalTheory.Grid.sgn ε M) θ (ω.toSgn ε) τ Y Φ₁ with e₂
  have hΦ₂ := hth Φ₁ hΦ₁
  obtain ⟨N₀, C₀, h₀⟩ := hmod Φ hΦ
  obtain ⟨N₁, C₁, h₁⟩ := hmod Φ₁ hΦ₁
  obtain ⟨N, C, h₂⟩ := hmod Φ₂ hΦ₂
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.Grow.height_comparison (V := X) hθ
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
    ((GlobalTheory.Grow.continuous_height X).comp hco).continuousOn
  have key := hasDerivAt_integral_second_derivative (ν.restrict 𝓕) (fun t g => thetaKO ω g (h * oneP θ X τ Y t) Φ)
    (fun t g => thetaKO ω g (h * oneP θ X τ Y t) Φ₁) (fun t g => thetaKO ω g (h * oneP θ X τ Y t) Φ₂)
    (hder Φ hΦ) (hder Φ₁ hΦ₁) (fun g => (hcont Φ₂ hΦ₂).comp (Continuous.prodMk_right g)) (hcont Φ₂ hΦ₂).measurable
    (fun t => (h₀ _).1) (h₁ _).1 (fun t => (h₂ _).1) (max C 0 * (c * K) ^ N) fun t htt => by
      refine (h₂ _).2.trans ?_
      have a1 : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X (h * oneP θ X τ Y t) : ℝ) ≤ c * K :=
        (hc _).1.trans (mul_le_mul_of_nonneg_left (hK ⟨t, htt, rfl⟩) hc0.le)
      have a2 : (0 : ℝ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X (h * oneP θ X τ Y t) := NNReal.coe_nonneg _
      exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ a2 a1 N) (pow_nonneg a2 N) (le_max_right _ _)
  simpa only [thetaInt, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] using key
theorem thetaIntegral_kernel_lieAlgebra_stable (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁)
    (B : GlobalTheory.ChainFr.Fr X) {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν : Measure (GA D W)}
    {𝓕 : Set (GA D W)} (hν : IsHaarFD W ν 𝓕) {ωA ωB Pi rf rl p p'}
    (hM : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') (J₀ : Pi →ₗ[ℂ] (GA D X → ℂ))
    (hJ : ∀ Φ ∈ algF ψ θ true A B, thetaInt ωA ν 𝓕 Φ = J₀ (p Φ)) (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (hY : Y ∈ lieAt X τ) (x : Pi) (hx : J₀ x = 0) : J₀ (rl τ Y x) = 0 := by
  have hx' : x ∈ (algF ψ θ true A B).map p := by rw [hM.mapA.onto]; trivial
  obtain ⟨Φ, hΦ, rfl⟩ := Submodule.mem_map.1 hx'
  obtain ⟨Φ', hΦ', hD⟩ := hM.mapA.stabX.2 τ Y hY Φ hΦ
  rw [← hM.mapA.eql τ Y hY Φ hΦ Φ' hΦ' hD, ← hJ Φ' hΦ']
  have hth := GlobalTheory.TripleWeilTransfer.isThetaFunO_of_mem_algF hψ hθ true A B hΦ
  have hω' : IsWeilDatumO ψ (GlobalTheory.Grid.sgn true W) X β (β / α) (ωA.toSgn true) := hM.weilA
  have e : Φ' = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT (V := GlobalTheory.Grid.sgn true W) θ (ωA.toSgn true) τ Y Φ := by
    funext z
    have h1 := (GlobalTheory.Chain.LiftReg.tame_dOmT hθ hω' hY).2 Φ hth 1 z
    simp only [one_mul, map_one, Module.End.one_apply] at h1
    exact (hD z).unique h1
  obtain ⟨a, b, hsig, hbig, -⟩ := hT.sig
  have hlt : X.rank < 2 * (W.rank - a) := by have := hT.rank; omega
  funext h
  have h2 := hasDerivAt_theta_integral hθ hM.weilA hν
    (_root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence hP.siegelSetUnitary hP D ψ θ hθ true W X β (β / α) ωA hM.weilA a
      ⟨D.eTau.symm 1, (hsig _).1⟩ hlt ν 𝓕 hν) hY hth h
  rw [hJ Φ hΦ, hx] at h2
  rw [e]
  exact h2.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
theorem thetaIntegral_eq_zero_or_injective (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁)
    (B : GlobalTheory.ChainFr.Fr X) {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν : Measure (GA D W)}
    {𝓕 : Set (GA D W)} (hν : IsHaarFD W ν 𝓕) {ωA ωB Pi rf rl p p'}
    (hM : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') (J₀ : Pi →ₗ[ℂ] (GA D X → ℂ))
    (hJ : ∀ Φ ∈ algF ψ θ true A B, thetaInt ωA ν 𝓕 Φ = J₀ (p Φ)) : J₀ = 0 ∨ Function.Injective J₀ := by
  have hf : ∀ g ∈ GfC X, ∀ x ∈ LinearMap.ker J₀, rf g x ∈ LinearMap.ker J₀ := by
    intro g hg x hx
    have hx' : x ∈ (algF ψ θ true A B).map p := by rw [hM.mapA.onto]; trivial
    obtain ⟨Φ, hΦ, rfl⟩ := Submodule.mem_map.1 hx'
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hM.mapA.eqf g hg Φ hΦ, ← hJ _ (hM.mapA.stabX.1 g hg Φ hΦ)]
    funext h
    rw [theta_integral_right_translate, hJ Φ hΦ, hx]
    rfl
  have hl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ LinearMap.ker J₀, rl τ Y x ∈ LinearMap.ker J₀ :=
    fun τ Y hY x hx => _root_.GlobalTheory.ThetaKFactor.thetaIntegral_kernel_lieAlgebra_stable hP hψ hθ A A₁ B hT hν hM J₀ hJ τ Y hY x hx
  rcases hM.irred.2 (LinearMap.ker J₀) hf hl with h | h
  · exact Or.inr (LinearMap.ker_eq_bot.1 h)
  · exact Or.inl (LinearMap.ker_eq_top.1 h)
end GlobalTheory.ThetaKFactor
end
theorem _root_.GlobalTheory.T.thetaIntegral_factors_through_kType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (q : PolF D X.rank W.rank →ₗ[ℂ] Pr), ∀ α β : (AE D)ˣ →* Circle,
      GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)), GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 →
      ∀ ωA : GlobalTheory.Grid.WRep W X, GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA →
      ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true A B f →
        ∃ (Pf : ModuleCat.{0} ℂ) (y : Pf) (J : Pr ⊗[ℂ] Pf →ₗ[ℂ] (GA D X → ℂ)), (J = 0 ∨ Function.Injective J) ∧
          ∀ P, GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 (GlobalTheory.SquareComm.fockF ψ θ true A B f P) = J (q P ⊗ₜ y) := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, q, q', -, -, hq⟩ := _root_.GlobalTheory.T.twisted_local_factors_match hP.howeDualityReal hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  refine ⟨Pr, q, fun α β hT hab ν 𝓕 hν ωA hωA f hf => ?_⟩
  obtain ⟨hex, hsplit⟩ := hq α β hT hab
  obtain ⟨ωA₀, ωB, Pi₀, rf₀, rl₀, p₀, p₀', hM₀⟩ := id hex
  obtain ⟨Pi, rf, rl, p, p', hM⟩ := _root_.GlobalTheory.TripleWeilTransfer.triple_exists_matching hP.howeDualityReal hP hK hL D ψ θ hψ hθ W W₁ X
    A A₁ B α β hT hex ωA ωB hωA hM₀.weilB
  obtain ⟨Pf, r, r', e, -, -, he, -⟩ := hsplit ωA ωB Pi rf rl p p' hM
  obtain ⟨J₀, hJ⟩ := _root_.GlobalTheory.ThetaKFactor.exists_kFactor_of_thetaIntegral hP hK hL hψ hθ A A₁ B hT hν hM
  refine ⟨Pf, r f, J₀ ∘ₗ e.toLinearMap, ?_, fun P => ?_⟩
  · rcases _root_.GlobalTheory.ThetaKFactor.thetaIntegral_eq_zero_or_injective hP hψ hθ A A₁ B hT hν hM J₀ hJ with h | h
    · exact Or.inl (by rw [h, LinearMap.zero_comp])
    · exact Or.inr (h.comp e.injective)
  · rw [hJ _ (Submodule.subset_span ⟨f, P, hf, rfl⟩), he f hf P]
    rfl
end
