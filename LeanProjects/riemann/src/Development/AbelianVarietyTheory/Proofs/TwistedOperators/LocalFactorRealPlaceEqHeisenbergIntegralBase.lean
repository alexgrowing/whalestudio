import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumProjectorRangeAnnihilatedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorVacuumEqSmulBasePointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergSmoothRapidSuperpositionTranslatesStatement

noncomputable section

namespace GlobalTheory.RealLocOp

section Abstract

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ContDiff

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {ρ : W → B →L[ℂ] B}

theorem sm_heis (om : W →L[ℝ] W →L[ℝ] ℝ) (h : IsHeis (fun x y => om x y) ρ) (a : W) {f : B} (hf : Sm ρ f) :
    Sm ρ (ρ a f) := by
  unfold Sm
  simp only [h.2.1]
  refine ContDiff.smul (Complex.contDiff_exp.comp (contDiff_const.mul ?_))
    (ContDiff.comp hf (contDiff_id.add contDiff_const))
  exact Complex.ofRealCLM.contDiff.comp (om.flip a).contDiff

omit [NormedSpace ℝ W] in
theorem heis_comm {om : W → W → ℝ} (h : IsHeis om ρ) {u v : W} (h1 : om u v = 0) (h2 : om v u = 0) (f : B) :
    ρ u (ρ v f) = ρ v (ρ u f) := by
  rw [h.2.1, h.2.1, h1, h2, add_comm]

theorem dH_comm_line (A : B →L[ℂ] B) (w : W) {f : B} (hA : ∀ t : ℝ, ρ (t • w) (A f) = A (ρ (t • w) f)) (hf : Sm ρ f)
    (hAf : Sm ρ (A f)) : dH ρ w (A f) = A (dH ρ w f) := by
  refine (hasDerivAt_dH w hAf).unique ?_
  simp only [hA]
  exact (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH w hf)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ W] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}

theorem exists_superpos (om : W →L[ℝ] W →L[ℝ] ℝ) (hom : ∀ x, om x x = 0) (hρ : IsHeis (fun x y => om x y) ρ)
    (hJ : ∀ x, J (J x) = -x) (E : V →L[ℝ] W) (hE : ∀ x y, om (E x) (E y) = omJ J x y) {x f₀ : B} (hx : Sm ρ x)
    (h0 : f₀ ≠ 0)
    (hline : ∀ A : B →L[ℂ] B,
      (∀ C : B →L[ℂ] B, (∀ v f, C (ρ (E v) f) = ρ (E v) (C f)) → ∀ f, C (A f) = A (C f)) → Sm ρ (A x) →
      (∀ z, dH ρ (E z) (A x) + I • dH ρ (E (J z)) (A x) = 0) → ∃ c : ℂ, A x = c • f₀) :
    ∃ c : V → ℂ, Continuous c ∧ (∀ n : ℕ, Integrable fun y => ‖y‖ ^ n * ‖c y‖) ∧ x = ∫ u, c u • ρ (E u) f₀ := by
  have h : IsHeis (omJ J) fun v => ρ (E v) := UnitaryOsc.isHeis_comp hρ E hE
  have hg : Good h x := Osc.good_of_sm hJ h (ContDiff.comp (g := fun v => ρ v x) hx E.contDiff)
  obtain ⟨l, hl⟩ := SeparatingDual.exists_eq_one (R := ℂ) h0
  have key : ∀ u, proj h (ρ (E (-u)) x) = l (proj h (ρ (E (-u)) x)) • f₀ := by
    intro u
    have hs : Sm ρ (proj h (ρ (E (-u)) x)) :=
      GlobalTheory.T.heisenberg_smooth_rapid_superposition_translates W V volume B om ρ hom hρ E gau continuous_gau Osc.integrable_pow_gau _ (sm_heis om hρ _ hx)
    obtain ⟨c, hc⟩ := hline ((proj h).comp (ρ (E (-u))))
      (fun C hC f => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Osc.proj_comm h C hC, hC]) hs
      fun z => by
        have := GlobalTheory.T.vacuumProjector_range_annihilated V B J _ hJ h (ρ (E (-u)) x) z
        unfold dH at this
        rwa [UnitaryOsc.fderiv_comp_clm hs, UnitaryOsc.fderiv_comp_clm hs] at this
    rw [ContinuousLinearMap.comp_apply] at hc
    rw [hc, map_smul, hl, smul_eq_mul, mul_one]
  have hc : Continuous fun u => l (proj h (ρ (E (-u)) x)) :=
    l.continuous.comp ((proj h).continuous.comp (Osc.cont_neg h x))
  refine ⟨_, hc, fun n => ?_, ?_⟩
  · refine Integrable.mono' ((hg n).const_mul ‖l‖) ((continuous_norm.pow n).mul hc.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (by positivity), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (l.le_opNorm _) (by positivity)
  · refine (hg.inversion hJ).symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    simp only
    rw [← map_smul, ← key]

end Abstract

section Mat

open Matrix GlobalTheory.RealWeil

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

def atPl (τ : O) (y : Matrix (Fin m) (Fin n) ℂ) : (Fin m × Fin n) × O → ℂ :=
  vecL (Pi.single τ y : O → Fin m → Fin n → ℂ)

omit [Fintype O] in
theorem cpt_atPl (τ τ' : O) (y : Matrix (Fin m) (Fin n) ℂ) :
    cpt (atPl τ y) τ' = (Pi.single τ y : O → Matrix (Fin m) (Fin n) ℂ) τ' := rfl

omit [Fintype O] in
theorem smul_atPl (τ : O) (t : ℝ) (y : Matrix (Fin m) (Fin n) ℂ) : t • atPl τ y = atPl τ (t • y) := by
  funext p
  show t • cpt (atPl τ y) p.2 p.1.1 p.1.2 = cpt (atPl τ (t • y)) p.2 p.1.1 p.1.2
  rw [cpt_atPl, cpt_atPl]
  by_cases h : p.2 = τ
  · rw [h, Pi.single_eq_same, Pi.single_eq_same]; rfl
  · simp [Pi.single_eq_of_ne h]

def emb (τ : O) : ((Fin m × Fin n) × Unit → ℂ) →L[ℝ] ((Fin m × Fin n) × O → ℂ) :=
  vecL ∘L ContinuousLinearMap.single ℝ (fun _ : O => Fin m → Fin n → ℂ) τ ∘L
    ContinuousLinearMap.proj (φ := fun _ : Unit => Fin m → Fin n → ℂ) () ∘L unvecL

omit [Fintype O] in
theorem emb_apply (τ : O) (v : (Fin m × Fin n) × Unit → ℂ) : emb τ v = atPl τ (cpt v ()) := rfl

theorem form_emb (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) (τ : O)
    (x y : (Fin m × Fin n) × Unit → ℂ) :
    star (emb τ y) ⬝ᵥ blk b a *ᵥ emb τ x = star y ⬝ᵥ blk (fun _ => b τ) (fun _ => a τ) *ᵥ x := by
  rw [star_dotProduct_eq, star_dotProduct_eq, Finset.sum_eq_single τ, Finset.univ_unique, Finset.sum_singleton]
  · rw [cpt_blk, cpt_blk, emb_apply, emb_apply, cpt_atPl, cpt_atPl, Pi.single_eq_same, Pi.single_eq_same]
  · intro τ' _ h
    rw [emb_apply, cpt_atPl, Pi.single_eq_of_ne h]
    simp
  · simp

theorem form_ne (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) {τ τ' : O} (h : τ ≠ τ')
    (x y : Matrix (Fin m) (Fin n) ℂ) : star (atPl τ y) ⬝ᵥ blk b a *ᵥ atPl τ' x = 0 := by
  rw [star_dotProduct_eq]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  rw [cpt_blk, cpt_atPl, cpt_atPl]
  by_cases e : ρ = τ
  · rw [Pi.single_eq_of_ne (e ▸ h : ρ ≠ τ')]
    simp
  · rw [Pi.single_eq_of_ne e]
    simp

end Mat

section Theta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped TensorProduct ComplexOrder Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem exists_om (S T : HSp D) : ∃ om : (Ix S T → ℂ) →L[ℝ] (Ix S T → ℂ) →L[ℝ] ℝ,
    (∀ x, om x x = 0) ∧ ∀ x y, om x y = (star y ⬝ᵥ HM S T *ᵥ x).im := by
  let B₀ : (Ix S T → ℂ) →ₗ[ℝ] (Ix S T → ℂ) →ₗ[ℝ] ℝ := -(GlobalTheory.VacUnique.omO S T).compl₁₂ unvecL.toLinearMap unvecL.toLinearMap
  let om : (Ix S T → ℂ) →L[ℝ] (Ix S T → ℂ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)
  have e : ∀ x y, om x y = (star y ⬝ᵥ HM S T *ᵥ x).im := by
    intro x y
    rw [im_HM x y]
    rfl
  refine ⟨om, fun x => ?_, e⟩
  rw [e]
  exact IsHermitian.im_star_dotProduct_mulVec_self (A := HM S T) HM_herm x

theorem coe_dH_atPl (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : BB ψ S T}
    (hG : GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) G) (τ : D.what₂.Tau) (y : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : WO S T) :
    ev _ _ w (dH (rhoV hψ σ S T) (atPl τ y) G) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ y G.1 w := by
  refine (ev_fderiv hψ G hG (atPl τ y) w).trans ?_
  have e : ∀ t : ℝ, iotaV σ S T (t • atPl τ y) = lineAt θ τ y t := fun t => by
    rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ y t]
    rfl
  simp only [e]
  rfl

theorem isFockVacAt_iff (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : BB ψ S T}
    (hG : GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) G) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    IsFockVacAt (heisO ψ S T) θ τ J G.1 ↔ ∀ y,
      dH (rhoV hψ σ S T) (atPl τ y) G + Complex.I • dH (rhoV hψ σ S T) (atPl τ (J y)) G = 0 := by
  refine forall_congr' fun y => ?_
  have e : ∀ w, ev _ _ w (dH (rhoV hψ σ S T) (atPl τ y) G + Complex.I • dH (rhoV hψ σ S T) (atPl τ (J y)) G) =
      annih (heisO ψ S T) θ τ J y G.1 w := fun w => by
    rw [map_add, map_smul, coe_dH_atPl h hψ hG, coe_dH_atPl h hψ hG]
    rfl
  refine ⟨fun hv => QB_ext fun w => ?_, fun hv => funext fun w => ?_⟩
  · rw [← ev_apply, e, hv]
    rfl
  · rw [← e, hv, map_zero]
    rfl

theorem idem_comp (hθ : IsInfFam θ) (τ : D.what₂.Tau) : θ τ (infPart D (idem D (.inr τ))) = 1 := by
  have := D.sp.cm.totReal
  have h := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ) (θ τ) (hθ τ).1 (hθ τ).2 (Pi.single (plTau D τ) 1) 1
  rw [RingHom.map_one, mul_one] at h
  refine h.trans ((GlobalTheory.InfAdeleCM.ext_apply _ _).trans ?_)
  change InfinitePlace.Completion.extensionEmbedding (plTau D τ)
    ((Pi.single (plTau D τ) 1 : ∀ w : InfinitePlace D.host.F, w.Completion) (plTau D τ)) = _
  rw [Pi.single_eq_same, map_one]

theorem wAt_iotaV (h : Chart θ σ) (τ : D.what₂.Tau) (y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    wAt (.inr τ) (iotaV σ S T (atPl τ y)) = iotaV σ S T (atPl τ y) := by
  funext i j
  refine sub_eq_zero.1 (h.ext _ ?_ fun τ' => ?_)
  · have e : finPart D (iotaV σ S T (atPl τ y) i j) = 0 := congrFun (congrFun (real_iotaV h _) i) j
    rw [RingHom.map_sub, wAt, RingHom.map_mul, e, mul_zero, sub_zero]
  · rw [RingHom.map_sub, RingHom.map_sub, wAt, RingHom.map_mul, RingHom.map_mul]
    by_cases e : τ' = τ
    · subst e
      rw [idem_comp h.inf, one_mul, sub_self]
    · have e1 : θ τ' (infPart D (iotaV σ S T (atPl τ y) i j)) = cpt (atPl τ y) τ' i j :=
        congrFun (congrFun (congrFun (h.pi_iota T S (unvecL (atPl τ y))) τ') i) j
      rw [e1, cpt_atPl, Pi.single_eq_of_ne e]
      simp

theorem exists_ip {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) (G : BB ψ S T) :
    ∃ l : BB ψ S T →L[ℂ] ℂ, ∀ F, l F = ipO μ 𝓕 F.1 G.1 := by
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have : IsProbabilityMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hμ.2.2⟩
  have hb : ∀ (F : BB ψ S T) w, ‖F.1 w * (starRingEnd ℂ) (G.1 w)‖ ≤ ‖G‖ * ‖F‖ := fun F w => by
    rw [norm_mul, Complex.norm_conj, mul_comm]
    exact mul_le_mul (norm_ev_le w G) (norm_ev_le w F) (norm_nonneg _) (norm_nonneg _)
  have hi : ∀ F : BB ψ S T, Integrable (fun w => F.1 w * (starRingEnd ℂ) (G.1 w)) (μ.restrict 𝓕) := fun F =>
    Integrable.of_bound (F.1.continuous.mul (Complex.continuous_conj.comp G.1.continuous)).aestronglyMeasurable _
      (Filter.Eventually.of_forall (hb F))
  refine ⟨LinearMap.mkContinuous
    { toFun := fun F => ipO μ 𝓕 F.1 G.1
      map_add' := fun F F' => ?_
      map_smul' := fun a F => ?_ } ‖G‖ fun F => ?_, fun F => rfl⟩
  · unfold ipO
    rw [← integral_add (hi F) (hi F')]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => add_mul _ _ _)
  · unfold ipO
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => mul_assoc _ _ _)
  · refine (norm_integral_le_of_norm_le_const (μ := μ.restrict 𝓕) (Filter.Eventually.of_forall (hb F))).trans_eq ?_
    rw [probReal_univ, mul_one]

theorem exists_coord (τ : D.what₂.Tau) {sS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : IsCartanInv (gramAt D S τ) sS) (hT : IsCartanInv (gramAt D T τ) sT) :
    ∃ (E : EuclideanSpace ℂ ((Fin T.rank × Fin S.rank) × Unit) →L[ℝ] (Ix S T → ℂ))
      (J : EuclideanSpace ℂ ((Fin T.rank × Fin S.rank) × Unit) ≃ₗᵢ[ℝ] EuclideanSpace ℂ ((Fin T.rank × Fin S.rank) × Unit)),
      (∀ x, J (J x) = -x) ∧ (∀ x y, (star (E y) ⬝ᵥ HM S T *ᵥ E x).im = omJ J x y) ∧ (∀ z, ∃ y, E z = atPl τ y) ∧
        ∀ y, ∃ z, E z = atPl τ y ∧ E (J z) = atPl τ (cplxO sS sT y) := by
  obtain ⟨E, J, hJ, hEJ, hE⟩ := GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution ((Fin T.rank × Fin S.rank) × Unit)
    (blk (fun _ => ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ) • gramAt D T τ) fun _ => (gramAt D S τ)⁻¹)
    (blk (fun _ => sT) fun _ => sS)
    (by
      rw [blk_conjTranspose, conjTranspose_smul, GlobalTheory.SmoothForms.RealPts.gramAt_herm, conjTranspose_nonsing_inv,
        GlobalTheory.SmoothForms.RealPts.gramAt_herm]
      simp)
    (by
      rw [blk_mul, hS.1, hT.1]
      exact blk_one)
    (by
      rw [blk_mul]
      refine blk_posDef (fun _ => ?_) fun _ => ?_
      · rw [Matrix.smul_mul]
        exact hT.2.2.smul (two_im_pos τ)
      · rw [← GlobalTheory.RealSymplForm.cartan_inv_mul hS]
        exact hS.2.2.inv)
  obtain ⟨E', hE'⟩ : ∃ E' : EuclideanSpace ℂ ((Fin T.rank × Fin S.rank) × Unit) →L[ℝ] (Ix S T → ℂ),
      ∀ z, E' z = emb τ (E z) := ⟨emb τ ∘L E, fun _ => rfl⟩
  refine ⟨E', J, hJ, fun x y => by rw [hE', hE', HM, form_emb, hE], fun z => ⟨_, (hE' z).trans (emb_apply _ _)⟩,
    fun y => ⟨E.symm (vecL fun _ => y), ?_, ?_⟩⟩
  · rw [hE', E.apply_symm_apply, emb_apply]
    rfl
  · rw [hE', hEJ, E.apply_symm_apply, emb_apply]
    have := cpt_blk (fun _ : Unit => sT) (fun _ => sS) (vecL fun _ => y) ()
    exact congrArg (fun z => atPl τ (Complex.I • z)) this

theorem fix_iff (hψ : IsStdChar D ψ (-1)) (u : WO S T) (F : BB ψ S T) :
    heisO ψ S T u F.1 = F.1 ↔ rhoB hψ u F = F :=
  ⟨fun e => QB_ext fun w => by rw [coe_rhoB, e], fun e => by rw [← coe_rhoB hψ, e]⟩

theorem rhoV_comm (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {τ τ' : D.what₂.Tau} (ht : τ' ≠ τ)
    (y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ) (F : BB ψ S T) :
    rhoV hψ σ S T (atPl τ' y') (rhoV hψ σ S T (atPl τ y) F) = rhoV hψ σ S T (atPl τ y) (rhoV hψ σ S T (atPl τ' y') F) := by
  refine heis_comm (isHeis_rhoB (S := S) (T := T) h hψ) ?_ ?_ F
  · rw [HM, form_ne _ _ (Ne.symm ht), Complex.zero_im]
  · rw [HM, form_ne _ _ ht, Complex.zero_im]

variable {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem line (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {X F₀ : BB ψ S T} (hb : IsBase ψ θ S T sS sT ΛS ΛT F₀.1)
    {τ : D.what₂.Tau} (hx : IsLocal ψ θ S T sS sT ΛS ΛT (.inr τ) X.1) (A : BB ψ S T →L[ℂ] BB ψ S T)
    (hA : ∀ C : BB ψ S T →L[ℂ] BB ψ S T,
      (∀ y f, C (rhoV hψ σ S T (atPl τ y) f) = rhoV hψ σ S T (atPl τ y) (C f)) → C (A X) = A (C X))
    (hs : GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) (A X))
    (hann : ∀ y, dH (rhoV hψ σ S T) (atPl τ y) (A X) +
      Complex.I • dH (rhoV hψ σ S T) (atPl τ (cplxO (sS τ) (sT τ) y)) (A X) = 0) : ∃ c : ℂ, A X = c • F₀ := by
  have sm := sm_of_theta h hψ X hx.1
  have h1 : ∀ {u : WO S T}, u.map (infPart D) = 0 → heisO ψ S T u X.1 = X.1 →
      heisO ψ S T u (A X).1 = (A X).1 := fun hu e =>
    (fix_iff hψ _ _).2 (by rw [hA _ fun v => rhoB_comm h hψ hu _, (fix_iff hψ _ _).1 e])
  obtain ⟨U, hU, hl⟩ := hx.1.level
  have h2 := isLatVac_mono (latO_mono (P := fun _ => True) fun _ _ => Sum.inl_ne_inr) hx.2.1
  obtain ⟨a, ha⟩ := GlobalTheory.T.restrictedTensor_vacuum_eq_smul_basePoint D ψ θ S T sS sT ΛS ΛT _ hb (A X).1
    (theta_of_sm h hψ _ hs ⟨U, hU, fun u hu h0 => h1 h0 (hl u hu h0)⟩)
    ⟨fun u hu => h1 (GlobalTheory.SplitScalar.latO_fin (AddSubgroup.nsmul_mem _ hu 2)) (h2.1 u hu),
      fun e he u hu hh => h1 (GlobalTheory.SplitScalar.latO_fin hu) (h2.2 e he u hu hh)⟩
    fun τ' => (isFockVacAt_iff h hψ hs τ' _).2 fun y => by
      by_cases ht : τ' = τ
      · subst ht
        exact hann y
      · have hd : ∀ y, dH (rhoV hψ σ S T) (atPl τ' y) (A X) = A (dH (rhoV hψ σ S T) (atPl τ' y) X) := fun y =>
          dH_comm_line A _ (fun t => hA _ fun v f => by rw [smul_atPl, rhoV_comm h hψ ht]) sm hs
        rw [hd, hd, ← map_smul, ← map_add,
          (isFockVacAt_iff h hψ sm τ' _).1 (hx.2.2 τ' fun e => ht (Sum.inr_injective e)) y, map_zero]
  exact ⟨a, QB_ext fun w => congrFun ha w⟩

theorem isLocOp_integral (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ν : Measure V) (E : V →L[ℝ] (Ix S T → ℂ)) {τ : D.what₂.Tau}
    (hE : ∀ z, ∃ y, E z = atPl τ y) {c : V → ℂ} (hc : Continuous c)
    (hci : ∀ n : ℕ, Integrable (fun y => ‖y‖ ^ n * ‖c y‖) ν) (F₀ : BB ψ S T) :
    IsLocOp ψ S T μ 𝓕 F₀.1 (.inr τ) (∫ u, c u • rhoV hψ σ S T (E u) F₀ ∂ν : BB ψ S T).1 := by
  have lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨om, hom, e⟩ := exists_om S T
  have hρ : IsHeis (fun x y => om x y) (rhoV hψ σ S T) := by
    simp only [e]
    exact isHeis_rhoB h hψ
  have hint : ∀ F : BB ψ S T, Integrable (fun u => c u • rhoV hψ σ S T (E u) F) ν := fun F => by
    refine Integrable.mono' ((hci 0).mul_const ‖F‖)
      (hc.smul ((hρ.2.2.2 F).comp E.continuous)).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_smul, hρ.2.2.1, pow_zero, one_mul]
  have hip : ∀ (F : BB ψ S T) g, IsThetaFunO ψ S T g →
      ipO μ 𝓕 (∫ u, c u • rhoV hψ σ S T (E u) F ∂ν : BB ψ S T).1 g =
        ∫ u, c u * ipO μ 𝓕 (heisO ψ S T (wAt (.inr τ) (iotaV σ S T (E u))) F.1) g ∂ν := by
    intro F g hg
    obtain ⟨G, rfl⟩ := lift g hg
    obtain ⟨l, hl⟩ := exists_ip hμ G
    rw [← hl, ← l.integral_comp_comm (hint F)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    obtain ⟨y, hy⟩ := hE u
    simp only
    rw [map_smul, hl, coe_rhoV, hy, wAt_iotaV h, smul_eq_mul]
  refine ⟨fun φ => ∫ u, c u * φ (iotaV σ S T (E u)) ∂ν, fun a φ => ?_, fun f hf => ?_, hip F₀⟩
  · simp only [mul_left_comm _ a, integral_const_mul]
  · obtain ⟨F, rfl⟩ := lift f hf
    obtain ⟨U, hU, hl⟩ := hf.level
    refine ⟨_, theta_of_sm h hψ _ (GlobalTheory.T.heisenberg_smooth_rapid_superposition_translates _ _ ν _ om _ hom hρ E c hc hci F (sm_of_theta h hψ F hf))
      ⟨U, hU, fun u hu h0 => (fix_iff hψ _ _).2 ?_⟩, hip F⟩
    refine ((rhoB hψ u).integral_comp_comm (hint F)).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_))
    have e1 := rhoB_comm h hψ h0 (E v) F
    rw [(fix_iff hψ u F).1 (hl u hu h0)] at e1
    exact (map_smul _ _ _).trans (congrArg (c v • ·) e1)

set_option maxHeartbeats 800000 in

theorem isLocOp_coord (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {X F₀ : BB ψ S T} (hb : IsBase ψ θ S T sS sT ΛS ΛT F₀.1)
    {τ : D.what₂.Tau} (hx : IsLocal ψ θ S T sS sT ΛS ΛT (.inr τ) X.1) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (E : V →L[ℝ] (Ix S T → ℂ)) (J : V ≃ₗᵢ[ℝ] V)
    (hJ : ∀ x, J (J x) = -x) (hE : ∀ x y, (star (E y) ⬝ᵥ HM S T *ᵥ E x).im = omJ J x y) (h1 : ∀ z, ∃ y, E z = atPl τ y)
    (h2 : ∀ y, ∃ z, E z = atPl τ y ∧ E (J z) = atPl τ (cplxO (sS τ) (sT τ) y)) :
    IsLocOp ψ S T μ 𝓕 F₀.1 (.inr τ) X.1 := by
  obtain ⟨om, hom, e⟩ := exists_om S T
  have hρ : IsHeis (fun x y => om x y) (rhoV hψ σ S T) := by
    simp only [e]
    exact isHeis_rhoB h hψ
  borelize V
  have h0 : F₀ ≠ 0 := fun h0 => base_ne_zero hb (by rw [h0]; rfl)
  obtain ⟨c, hc, hci, hX⟩ := exists_superpos om hom hρ hJ E (fun x y => (e _ _).trans (hE x y))
    (sm_of_theta h hψ X hx.1) h0 fun A hA hs hann => by
      refine line h hψ hb hx A (fun C hC => hA C (fun v f => ?_) X) hs fun y => ?_
      · obtain ⟨y, hy⟩ := h1 v
        exact hy ▸ hC y f
      · obtain ⟨z, e1, e2⟩ := h2 y
        exact e1 ▸ e2 ▸ hann z
  have := isLocOp_integral h hψ hμ volume E h1 hc hci F₀
  rwa [← hX] at this

theorem isLocOp_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inr τ) x → IsLocOp ψ S T μ 𝓕 f₀ (.inr τ) x := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ τ x hx
  have hψ := base_std hb
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart (base_inf hb)
  have lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨X, rfl⟩ := lift x hx.1
  obtain ⟨F₀, rfl⟩ := lift f₀ (base_theta hb)
  obtain ⟨E, J, hJ, hE, h1, h2⟩ := exists_coord τ (hb.1 τ) (hb.2.1 τ)
  exact isLocOp_coord h hψ hμ hb hx E J hJ hE h1 h2

end Theta

end GlobalTheory.RealLocOp

end
