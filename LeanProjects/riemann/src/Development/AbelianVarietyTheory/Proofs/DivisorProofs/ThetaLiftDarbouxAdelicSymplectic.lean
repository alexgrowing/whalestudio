import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFrameCharacterFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesOrthonormalJStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOperStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAcStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurEquivariantIsometryScalarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqScalarCharacterOfDoubleCoverUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticQuadraticOperatorEqSumSymplecticDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadraticStatement

noncomputable section

namespace GlobalTheory.ArchRep

section Real

open MeasureTheory Filter Topology GlobalTheory.RealWeil Matrix

theorem hasDerivAt_of_sq {χ : ℝ → ℂ} {a : ℂ} (hc : ContinuousAt χ 0) (h0 : χ 0 = 1)
    (h : HasDerivAt (fun t => χ t ^ 2) a 0) : HasDerivAt χ (a / 2) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at h ⊢
  have h1 : Tendsto (fun t => χ t + 1) (𝓝[≠] 0) (𝓝 2) := by
    have := (hc.tendsto.add_const 1).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [h0, one_add_one_eq_two] at this
  refine (h.div h1 two_ne_zero).congr' ?_
  filter_upwards [h1.eventually_ne two_ne_zero] with t ht
  simp only [zero_add, h0, Pi.div_apply, Complex.real_smul]
  field_simp
  ring

variable {l : Type} [Fintype l] [DecidableEq l]

theorem continuous_sch {G : Type} [Group G] [TopologicalSpace G] {pr : G →* Matrix.symplecticGroup l ℝ}
    {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)} {omS : G →* (Sch l →L[ℂ] Sch l)}
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume) (hpr : Continuous pr)
    (h2 : ∀ v, Continuous fun g => om g v) (lam : Sch l →L[ℂ] ℂ) (f : Sch l) : Continuous fun g => lam (omS g f) := by
  have hm : Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) := continuous_subtype_val.comp hpr
  have key : ∀ A ∈ weylAlg l, ∀ f, Continuous fun g => schwartzToL2 l (A (omS g f)) := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, Continuous fun g => schwartzToL2 l (A (omS g f))) ?_ ?_ ?_ ?_ ?_ hA
    · intro f
      simpa only [h4, ContinuousLinearMap.one_apply, schwartzToL2_apply] using h2 (f.toLp 2 volume)
    · intro A w ih f
      simp only [toLp_dRho_omS h3 h4]
      refine continuous_finset_sum _ fun a _ => Continuous.smul (Complex.continuous_ofReal.comp ?_) (ih _)
      exact (continuous_apply a).comp
        (((continuous_const.matrix_mul hm.matrix_transpose).matrix_mul continuous_const).neg.matrix_mulVec continuous_const)
    · intro f
      simp only [ContinuousLinearMap.zero_apply]
      exact continuous_const
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact Λ.continuous.comp (continuous_pi fun i => key _ (hA i) f)

theorem realRep (hMp : GlobalTheory.Published.RealMetaplecticRepresentation) {G : Type} [Group G] [TopologicalSpace G]
    (s : G →* Matrix.symplecticGroup l ℝ) (hs : Continuous s) (ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l))
    (hc : ∀ v, Continuous fun g => ω g v)
    (hi : ∀ g w v, ω g (rho w v) = rho ((s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (ω g v)) :
    ∃ (ρ : G →* (Sch l →L[ℂ] Sch l)) (η : G → ℂ), (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      (∀ g w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(ρ g f₁) = rhoFun ((s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(ρ g f)) ∧
      (∀ g (f₁ f₂ : Sch l), ∫ x, star (ρ g f₁ x) * ρ g f₂ x = ∫ x, star (f₁ x) * f₂ x) ∧
      (∀ (L : Sch l →L[ℂ] ℂ) f, Continuous fun g => L (ρ g f)) ∧
      ∀ γ : ℝ → G, Continuous γ → γ 0 = 1 → ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ,
        (∀ t, (s (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) → ∀ a : ℂ,
        HasDerivAt (fun t => η (γ t)) a 0 → ∀ (L : Sch l →L[ℂ] ℂ) f,
          HasDerivAt (fun t => L (ρ (γ t) f)) (L (quad X f) + a / 2 * L f) 0 := by
  rcases isEmpty_or_nonempty l with hl | hl
  · refine ⟨1, fun _ => 1, fun _ _ => (mul_one _).symm, continuous_const, fun _ => one_ne_zero, fun g w f f₁ h => ?_,
      fun _ _ _ => rfl, fun L f => (continuous_const : Continuous fun _ : G => L f), fun γ _ _ X _ _ a ha L f => ?_⟩
    · rw [Subsingleton.elim ((s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) w]
      exact h
    · have h0 : a = 0 := ha.unique (hasDerivAt_const _ _)
      have hq : quad X f = 0 := by simp [quad]
      rw [h0, hq]
      simpa using hasDerivAt_const (0 : ℝ) (L f)
  obtain ⟨G', _, _, _, pr, om, omS, ⟨hcov, hsurj, ε, -, hker, hε⟩, h2, h3, h4, h5, h6⟩ := hMp l
  have hinj : Function.Injective fun f : Sch l => (f.toLp 2 volume : L2 l) := SchwartzMap.injective_toLp 2 volume
  have hsm : ∀ (c : ℂ) (f : Sch l), ((c • f).toLp 2 volume : L2 l) = c • f.toLp 2 volume := fun c f =>
    (schwartzToL2 l).map_smul c f
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.MetaplecticScalarDeriv.exists_schwartz_one l
  have hv₀ : (f₀.toLp 2 volume : L2 l) ≠ 0 := fun h => by
    have : f₀ = 0 := hinj (h.trans (schwartzToL2 l).map_zero.symm)
    rw [this] at hf₀
    exact zero_ne_one hf₀
  haveI : Nontrivial (L2 l) := nontrivial_of_ne _ _ hv₀
  have hχ : ∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v := fun g g' h => by
    obtain ⟨a, ha⟩ := GlobalTheory.T.schur_equivariant_isometry_scalar l (ω g * om g'⁻¹) fun w v => by
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, Function.comp_apply, h3, hi, mulVec_mulVec, ← h,
        ← Submonoid.coe_mul, ← map_mul, mul_inv_cancel, map_one, Submonoid.coe_one, one_mulVec]
    refine ⟨a, fun v => ?_⟩
    rw [← ha, ← Function.comp_apply (f := ⇑(ω g * om g'⁻¹)), ← LinearIsometryEquiv.coe_mul, mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, mul_one]
  obtain ⟨η, hη1, hη2, hη3, hη4⟩ := GlobalTheory.T.sq_scalar_character_of_double_cover_unitary G G' _ (L2 l) pr s om ω ε hcov hsurj (fun g hg => (hker g).1 hg) hε hs h2
    hc hχ
  choose lf hlf using fun g => hsurj (s g)
  choose a ha using fun g => hχ g (lf g) (hlf g)
  have hl0 : ∀ g (f : Sch l), ω g (f.toLp 2 volume) = ((a g • omS (lf g)) f).toLp 2 volume := fun g f => by
    rw [ha, h4, ContinuousLinearMap.smul_apply, hsm]
  let ρ : G →* (Sch l →L[ℂ] Sch l) :=
    { toFun := fun g => a g • omS (lf g)
      map_one' := ContinuousLinearMap.ext fun f => hinj (by
        beta_reduce
        rw [← hl0, map_one]
        rfl)
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => hinj (by
        beta_reduce
        rw [ContinuousLinearMap.mul_apply, ← hl0, ← hl0, ← hl0, map_mul]
        rfl) }
  have hl1 : ∀ g (f : Sch l), ω g (f.toLp 2 volume) = (ρ g f).toLp 2 volume := hl0
  clear_value ρ
  refine ⟨ρ, η, hη1, hη2, hη3, fun g => GlobalTheory.MetaplecticScalarDeriv.intertwine_fun l _ (ω g) (ρ g) (hi g) (hl1 g),
    fun g f₁ f₂ => ?_, continuous_sch hi hl1 hs hc, fun γ hγ hγ0 X hX hγX b hb L f => ?_⟩
  · have e1 := SchwartzMap.inner_toL2_toL2_eq (ρ g f₁) (ρ g f₂) volume
    have e2 := SchwartzMap.inner_toL2_toL2_eq f₁ f₂ volume
    simp only [RCLike.inner_apply] at e1 e2
    simp only [Complex.star_def, mul_comm (starRingEnd ℂ _)]
    rw [← e1, ← e2, ← hl1, ← hl1, LinearIsometryEquiv.inner_map_map]
  · obtain ⟨δ, hδc, hδ0, -, hδX, hδd⟩ := h6 X hX
    have hpr : ∀ t, pr (δ t) = s (γ t) := fun t => Subtype.ext ((hδX t).trans (hγX t).symm)
    choose χ hχ' using fun t => hχ (γ t) (δ t) (hpr t)
    have e1 : ∀ t, ρ (γ t) f = χ t • omS (δ t) f := fun t => hinj (by
      beta_reduce
      rw [← hl1, hχ', h4, hsm])
    have hin : inner ℂ (f₀.toLp 2 volume : L2 l) (f₀.toLp 2 volume) ≠ 0 := inner_self_ne_zero.2 hv₀
    have e2 : χ = fun t => inner ℂ (om (δ t) (f₀.toLp 2 volume)) (ω (γ t) (f₀.toLp 2 volume)) /
        inner ℂ (f₀.toLp 2 volume : L2 l) (f₀.toLp 2 volume) := funext fun t => by
      rw [hχ', inner_smul_right, LinearIsometryEquiv.inner_map_map, mul_div_cancel_right₀ _ hin]
    have hχc : Continuous χ := by
      rw [e2]
      exact (((h2 _).comp hδc).inner ((hc _).comp hγ)).div_const _
    have hχ0 : χ 0 = 1 := by
      rw [e2]
      simp only [hδ0, hγ0, map_one, LinearIsometryEquiv.coe_one, id_eq]
      exact div_self hin
    have hd := hasDerivAt_of_sq hχc.continuousAt hχ0 (a := b) (by
      simpa only [fun t => hη4 _ _ _ (hpr t) (hχ' t)] using hb)
    have hd2 := (metaplectic_schwartz_smooth h3 h4 h5).2.2 L X hX δ hδ0 hδX hδd f
    simp only [e1, map_smul, smul_eq_mul]
    refine (hd.mul hd2).congr_deriv ?_
    rw [hχ0, hδ0, map_one, ContinuousLinearMap.one_apply]
    ring

end Real

section Haar

open MeasureTheory

theorem haar_coords {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ} [MeasurableSpace V] [BorelSpace V]
    [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure] (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, ∀ F : V → ℂ, ∫ y, F y ∂μ = k • ∫ x, F (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ), fun F => ?_⟩
  have h1 : ∫ y, F y ∂μ = ∫ x, F (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, F (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def]

end Haar

theorem sumPl_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ w, Module.End ℂ (V w)) (c : ι → ℂ) :
    GlobalTheory.RealLift.sumPl (fun w => L w + c w • 1) = GlobalTheory.RealLift.sumPl L + (∑ w, c w) • 1 := by
  have h1 : ∀ w, GlobalTheory.RealLift.atPl w (1 : Module.End ℂ (V w)) = 1 := fun w => by
    rw [GlobalTheory.RealLift.atPl, Module.End.one_eq_id, Function.update_eq_self w (fun i => (LinearMap.id : V i →ₗ[ℂ] V i))]
    exact PiTensorProduct.map_id
  simp only [GlobalTheory.RealLift.sumPl, GlobalTheory.RealLift.PolRangePf.atPl_add', GlobalTheory.RealLift.PolRangePf.atPl_smul', h1,
    Finset.sum_add_distrib, Finset.sum_smul]

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.RealWeil GlobalTheory.ArchUniq

theorem archRep : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines σ JB, ∀ Y, IsGen τ C γ Y → ∀ (T : Tens F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  intro hP hDer _ F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨n, θ, φ, φ₀, hp, hq, hφ, hφu⟩ := GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_frames F E σ α β κ P Q R S τ JA JB d a b A C hCM hFr
  obtain ⟨k, hkc, hkC, hkJ, hcan⟩ := GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_orthonormal_J F E σ β R S τ JB b C hCM hFr.2.2
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨ω, hωc, hωi⟩ := GlobalTheory.T.exists_oscillator_action_normalising_schrodingerOperators _ _ P Q R S φ hφ (GlobalTheory.T.continuous_rho_apply _) (UG (cA σ) JB) k hkc hkJ
  obtain ⟨s, hsc, hsφ⟩ := GlobalTheory.T.exists_continuous_symplecticHom_of_indefiniteUnitary _ _ P Q R S φ hφ (UG (cA σ) JB) k hkc hkJ
  obtain ⟨ρ, η, hη1, hη2, hη3, hρi, hρu, hρc, hρd⟩ := realRep hP.realMetaplecticRepresentation s hsc ω hωc fun g w v => by
    obtain ⟨c, rfl⟩ := φ.surjective w
    rw [hsφ, hωi]
  obtain ⟨kk, hkk⟩ := GlobalTheory.T.archimedean_frame_character_factorization hP F E σ β R S τ JB b C hCM hFr.2.2 η (fun g h _ _ => hη1 g h) hη2.continuousOn
    fun g _ => hη3 g
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑θ.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑θ := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  clear_value toE toV
  have hS := SchrTransport.schr_coords (trP F κ) θ φ₀ hp hq
  let ρ' : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ) :=
    { toFun := fun g => toV ∘L ρ g ∘L toE
      map_one' := ContinuousLinearMap.ext fun f => by
        rw [map_one]
        exact hVE f
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => by
        simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hEV] }
  have hρ' : ∀ g f, ρ' g f = toV (ρ g (toE f)) := fun _ _ => rfl
  clear_value ρ'
  refine ⟨ρ', fun w => kk w / 2, fun g _ => ⟨fun u hu f f₁ hf h => ?_, fun ν hν f₁ f₂ => ?_⟩, fun L f => ?_,
    fun γ hγ Y hY T L => ?_⟩
  · choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    obtain ⟨c, hc⟩ : ∃ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ, ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ :=
      ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, fun w => by
        have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
        rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    have hu' : At (evI F) (actB (cA σ) g u) := fun t ht => by
      rw [actB, ← Matrix.smul_mul, hu t ht, Matrix.zero_mul]
    have hc' : ∀ w, (actB (cA σ) g u).map (piInf (τ w)) = A w * (c w * (k g w)ᵀ) * (C w)ᵀ := fun w => by
      rw [actB, Matrix.map_mul, hc, Matrix.transpose_map, Matrix.mul_assoc, ← Matrix.transpose_mul, hkC,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have e1 : ⇑f₁ = schrF (trP F κ) (locV (d.e u).1, locV (d.e u).2) ⇑f := by
      funext y
      have := congrFun ((GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ u hu f fun _ => 1).symm.trans (hf fun _ => 1)) (liftV y)
      simpa [pureA, liftV] using this.symm
    have e2 : ⇑(toE f₁) = rhoFun (φ c) ⇑(toE f) := by
      have := hS (locV (d.e u).1, locV (d.e u).2) ⇑(toE f)
      rw [← htoV, hVE, ← e1, ← hφu u c hu hc] at this
      rw [htoE, this]
      funext x
      simp
    have e3 := hρi g _ _ _ e2
    rw [hsφ, hφu _ _ hu' hc'] at e3
    rw [GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ _ hu', hρ', hρ', htoV, htoV, hS, e3]
  · haveI : BorelSpace ({w : InfinitePlace F // w.IsReal} → ℝ) := Pi.borelSpace
    haveI : BorelSpace ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.borelSpace
    haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
    obtain ⟨r, hr⟩ := haar_coords ν θ
    rw [hr, hr]
    congr 1
    simp only [hρ', htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hρu]
    simp only [htoE, Function.comp_apply]
  · simp only [hρ']
    exact (hρc (L ∘L toV) (toE f)).continuousOn
  · have hkY : ∀ (t : ℝ) w, k (γ (Multiplicative.ofAdd t)) w = NormedSpace.exp (t • Y w) := fun t w =>
      hcan w _ _ ((hkC _ w).symm.trans (hY t w))
    have hYu : ∀ w, Y w ∈ upq R S := fun w => GlobalTheory.RealLiftGen.mem_upq_of (Y w) fun t => by
      have := congrArg (fun X => X.map star) (hkJ (γ (Multiplicative.ofAdd t)) w)
      simp only [GlobalTheory.RealLiftGen.map_star_mul, GlobalTheory.RealLiftGen.Jm_map_star, hkY] at this
      refine Eq.trans ?_ this
      congr 2
      ext i j
      simp
    obtain ⟨Z, hZ, hZφ, hZe⟩ := GlobalTheory.T.exists_symplecticLie_of_indefiniteUnitaryLie_rightAction _ _ P Q R S φ hφ Y hYu
    have hsZ : ∀ t : ℝ, (s (γ (Multiplicative.ofAdd t)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        NormedSpace.exp (t • Z) := fun t => Matrix.toLin'.injective (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := φ.surjective v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hsφ, hZe]
      simp only [hkY])
    have hd := hρd (fun t => γ (Multiplicative.ofAdd t)) (hγ.1.comp continuous_ofAdd) (by simp) Z hZ hsZ _
      (hkk γ hγ Y hY) (L ∘L toV) (toE (Φ T))
    obtain ⟨D, hD⟩ := hDer F E σ α β κ ψ JA JB d hψ
    have hΨ : ∀ c T, (toE.toLinearMap ∘ₗ Φ) (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) ((toE.toLinearMap ∘ₗ Φ) T) := by
      intro c T
      obtain ⟨u, ⟨hu, hc⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM fun w => A w * c w * (C w)ᵀ
      have e1 := (GlobalTheory.RealLift.actsLaws F κ (Φ T) _ _).2.2.2.2 _ (hΦ.2 u hu c hc T) (hD u hu (Φ T)).1
      ext x
      obtain ⟨y, rfl⟩ := θ.surjective x
      have e2 := SchrTransport.dRho_coords (trP F κ) θ φ₀ hp hq (locV (d.e u).1, locV (d.e u).2) (Φ T) (toE (Φ T))
        (by rw [← htoV, hVE]) y
      rw [← hφu u c hu hc] at e2
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [← e2, e1, htoE, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact (hD u hu (Φ T)).2 y
    have e3 := GlobalTheory.T.fockToSchwartz_intertwines_metaplecticQuadratic GlobalTheory.T.metaplecticQuadraticOperator_eq_sum_symplectic_dual GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic _ _ P Q R S φ hφ _ hΨ Y hYu Z hZφ T
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at e3
    simp only [hρ']
    refine hd.congr_deriv ?_
    rw [e3, sumPl_add_smul]
    simp only [ContinuousLinearMap.comp_apply, hVE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, smul_eq_mul, Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.ArchRep

end
