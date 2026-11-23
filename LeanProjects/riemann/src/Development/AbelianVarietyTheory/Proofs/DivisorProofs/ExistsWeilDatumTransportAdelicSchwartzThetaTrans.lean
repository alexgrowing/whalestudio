import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySchroedingerOpenFiniteSubgrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergOperatorThetaTransformRealLiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOneParaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesRationalMatricesOntoRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSupporStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseAdelicThetaTransformRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslatesStatement
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform GlobalTheory.SWQ Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTransform

section Coord

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {N : ℕ}
  {e : WO S T ≃ₗ[AF D.host.F] VA D.host.F N}

theorem heisO_comp (he : ∀ w w', symplO S T w w' = symV (e w) (e w')) (u : WO S T) (f : VA D.host.F N → ℂ) :
    heisO ψ S T u (f ∘ e) = heisV ψ (e u) f ∘ e := by
  funext w
  simp only [heisO, heisV, Function.comp_apply, symplOH, he, map_add, invOf_two_eq]

theorem heisV_comp_symm (he : ∀ w w', symplO S T w w' = symV (e w) (e w')) (u : VA D.host.F N) (f : WO S T → ℂ) :
    heisV ψ u (f ∘ e.symm) = heisO ψ S T (e.symm u) f ∘ e.symm := by
  funext w
  simp only [heisO, heisV, Function.comp_apply, symplOH, he, map_add, invOf_two_eq, LinearEquiv.apply_symm_apply]

theorem isThetaFunO_thV (hψ : IsStdChar D ψ (-1)) (he : ∀ w w', symplO S T w w' = symV (e w) (e w'))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : Fin N → D.host.F,
      e (incM D.host.F x) = (rat y, rat z))
    {Φ : (Fin N → AF D.host.F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N)) :
    IsThetaFunO ψ S T (thV ψ Φ ∘ e) := by
  have hR : IsTotallyReal D.host.F := inferInstance
  obtain ⟨hc, -, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N), Continuous (thV ψ Φ ∘ e) := fun Φ hΦ =>
    (GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay D.host.F N ψ hR hψ.1 Φ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace D.host.F N Φ hΦ)).comp hc
  refine ⟨fun γ w => ?_, ?_, hcont Φ hΦ, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    have h' : e (ratW T S γ) = (rat y, rat z) := h
    simp only [Function.comp_apply, map_add, symplOH, he, h', ← invOf_two_eq]
    exact quasiV_thV ψ hψ.1.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_schroedinger_open_finite_subgroup D.host.F N ψ hR hψ.1 Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisO_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · refine GlobalTheory.T.contDiff_of_heisenbergDerivativeClosedClass D ψ hψ S T {f | ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N), f = thV ψ Φ ∘ e} ?_ ?_ _ ⟨Φ, hΦ, rfl⟩
    · rintro _ ⟨Φ, hΦ, rfl⟩
      exact hcont Φ hΦ
    · rintro _ ⟨Φ, hΦ, rfl⟩ M hM hM0
      obtain ⟨Φ', hΦ', hd⟩ := GlobalTheory.T.hasDerivAt_heisenbergOperator_thetaTransform_realLine D.host.F N ψ hR hψ.1 Φ hΦ (e.toLinearMap.toAddMonoidHom.comp M)
        ⟨hc.comp hM, fun t => (hfin _).1 (hM0 t)⟩
      refine ⟨_, ⟨Φ', hΦ', rfl⟩, fun w => ?_⟩
      simp only [heisO_comp he]
      exact hd (e w)

theorem thV_injOn {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}
    (hR : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin N))
    (hΦ' : Φ' ∈ GlobalTheory.WeilM.schA F (Fin N)) (h : thV ψ Φ = thV ψ Φ') : Φ = Φ' := by
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists F hR ψ hψ N (half F N) half_ne_zero
  refine eq_of_theta_rho F N ψ lam ν _ hC Φ Φ' (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ hΦ) (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ' hΦ') fun x y => ?_
  have := congrFun h (x, y)
  rwa [thV_eq_th, thV_eq_th] at this

theorem exists_thV_eq (hψ : IsStdChar D ψ (-1)) (he : ∀ w w', symplO S T w w' = symV (e w) (e w'))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : Fin N → D.host.F,
      e (incM D.host.F x) = (rat y, rat z))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin N), thV ψ Φ ∘ e = f := by
  have hR : IsTotallyReal D.host.F := inferInstance
  obtain ⟨-, hc, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts D T.rank S.rank N e
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists D.host.F hR ψ hψ.1 N (half D.host.F N) half_ne_zero
  obtain ⟨-, -, -, -, 𝓓, -, hD, h1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain D.host.F N ν hC.2.2.2.1
  let 𝒱 : Set (VA D.host.F N → ℂ) := {g | ∃ f, IsThetaFunO ψ S T f ∧ g = f ∘ e.symm}
  have hV : ∀ g ∈ 𝒱, Continuous g ∧ QuasiV ψ g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨hf.cont.comp hc, fun a b w => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := GlobalTheory.T.adelicCoordinates_rationalMatrices_onto_rational D T.rank S.rank N e hrat a b
      have hx' : e.symm (rat a, rat b) = ratW T S x := by rw [← hx]; exact e.symm_apply_apply _
      have hx'' : e (ratW T S x) = (rat a, rat b) := hx
      simp only [Function.comp_apply, map_add, hx', hf.quasi, symplOH, he, hx'', invOf_two_eq,
        LinearEquiv.apply_symm_apply]
    · obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
      exact ⟨C, fun w => hC _⟩
  have hder : ∀ g ∈ 𝒱, ∀ M : ℝ →+ VA D.host.F N, IsRealLine M → ∃ g' ∈ 𝒱, ∀ x,
      HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) g) x) (invV ψ ν 𝓓 g' x) 0 := by
    rintro _ ⟨f, hf, rfl⟩ M hM
    let L : ℝ →+ WO S T := e.symm.toLinearMap.toAddMonoidHom.comp M
    have hL : Continuous L := hc.comp hM.1
    have hL0 : ∀ t, (L t).map (finPart D) = 0 := fun t => (hfin _).2 (by
      have : e (L t) = M t := e.apply_symm_apply _
      rw [this]; exact hM.2 t)
    have hf' := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hL hL0 hf).2
    refine ⟨_, ⟨_, hf', rfl⟩, ?_⟩
    obtain ⟨c1, -, C₁, hC₁⟩ := hV _ ⟨f, hf, rfl⟩
    obtain ⟨c2, -, C₂, hC₂⟩ := hV _ ⟨_, hf', rfl⟩
    refine GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam D.host.F N ψ lam ν hC 𝓓 hD h1 _ _ (max C₁ C₂) c1 c2 (fun w => (hC₁ w).trans (le_max_left _ _))
      (fun w => (hC₂ w).trans (le_max_right _ _)) M hM.1 fun w s => ?_
    simp only [heisV_comp_symm he]
    exact GlobalTheory.WeilVacMove.hasDerivAt_line hψ hL hL0 hf (e.symm w) s
  have hmem : f ∘ e.symm ∈ 𝒱 := ⟨f, hf, rfl⟩
  have hlev : LevelV ψ (f ∘ e.symm) := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap e.symm.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 h0' => ?_⟩
    rw [heisV_comp_symm he, hU (e.symm u) hu ((hinf _).2 (by rw [e.apply_symm_apply]; exact ⟨h0, h0'⟩))]
  obtain ⟨hl, hs⟩ := GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support D.host.F N ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).2.1 hlev
  have hS : invV ψ ν 𝓓 (f ∘ e.symm) ∈ GlobalTheory.WeilM.schA D.host.F (Fin N) :=
    GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz D.host.F N _ hl hs (GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates D.host.F N ψ lam ν hC 𝓓 hD h1 𝒱 hV hder
      (GlobalTheory.T.inverseAdelicThetaTransform_rapid_decay D.host.F N ψ lam ν hC 𝓓 hD h1 𝒱 (fun g hg => (hV g hg).2) hder) _ hmem)
  refine ⟨_, hS, ?_⟩
  rw [GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic D.host.F N ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).1 (hV _ hmem).2.1 (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace D.host.F N _ hS)]
  funext w
  simp

end Coord

theorem exists_transport {V W G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Monoid G]
    (p : Submodule ℂ V) (Θ : p →ₗ[ℂ] W) (hΘ : Function.Injective Θ) (ω : G →* Module.End ℂ W)
    (hω : ∀ g, ∀ x ∈ LinearMap.range Θ, ω g x ∈ LinearMap.range Θ) :
    ∃ om : G →* Module.End ℂ V, ∀ g (x : p), ∃ h : om g x ∈ p, Θ ⟨om g x, h⟩ = ω g (Θ x) := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  let E := LinearEquiv.ofInjective Θ hΘ
  let A := Submodule.prodEquivOfIsCompl p q hq
  let r : G → Module.End ℂ p := fun g => E.symm.conj ((ω g).restrict (hω g))
  have hr : ∀ g x, Θ (r g x) = ω g (Θ x) := fun g x => by
    have : ∀ y : LinearMap.range Θ, Θ (E.symm y) = y := fun y => by
      conv_rhs => rw [← E.apply_symm_apply y]
      rfl
    simp only [r, LinearEquiv.conj_apply_apply, this]
    rfl
  have r1 : r 1 = 1 := LinearMap.ext fun x => hΘ (by rw [hr, map_one]; rfl)
  have rm : ∀ g h, r (g * h) = r g * r h := fun g h => LinearMap.ext fun x => hΘ (by
    rw [hr, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr, hr])
  refine ⟨⟨⟨fun g => A.conj ((r g).prodMap LinearMap.id), ?_⟩, fun g h => ?_⟩, fun g x => ?_⟩
  · ext v
    simp [r1, LinearEquiv.conj_apply_apply, Module.End.one_eq_id]
  · ext v
    simp [rm, LinearEquiv.conj_apply_apply]
  · have h : A.conj ((r g).prodMap LinearMap.id) (x : V) = r g x := by
      simp [A, LinearEquiv.conj_apply_apply]
    refine ⟨by rw [MonoidHom.coe_mk, OneHom.coe_mk, h]; exact (r g x).2, ?_⟩
    rw [← hr]
    congr 1
    exact Subtype.ext h

theorem exists_transport' {V W G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Monoid G]
    (p : Submodule ℂ V) (Θ : V → W) (P : W → Prop) (hadd : ∀ x ∈ p, ∀ y ∈ p, Θ (x + y) = Θ x + Θ y)
    (hsm : ∀ (c : ℂ) x, Θ (c • x) = c • Θ x) (hinj : ∀ x ∈ p, ∀ y ∈ p, Θ x = Θ y → x = y)
    (hon : ∀ f, P f ↔ ∃ x ∈ p, Θ x = f) (ω : G →* Module.End ℂ W) (hω : ∀ g f, P f → P (ω g f)) :
    ∃ om : G →* Module.End ℂ V, ∀ g, ∀ x ∈ p, om g x ∈ p ∧ Θ (om g x) = ω g (Θ x) := by
  let L : p →ₗ[ℂ] W :=
    { toFun := fun x => Θ x.1
      map_add' := fun x y => hadd _ x.2 _ y.2
      map_smul' := fun c x => hsm c x.1 }
  have hmem : ∀ f, f ∈ LinearMap.range L ↔ P f := fun f =>
    ⟨fun ⟨x, h⟩ => (hon f).2 ⟨x.1, x.2, h⟩, fun hf => let ⟨x, hx, h⟩ := (hon f).1 hf; ⟨⟨x, hx⟩, h⟩⟩
  obtain ⟨om, hom⟩ := exists_transport p L (fun x y h => Subtype.ext (hinj _ x.2 _ y.2 h)) ω
    fun g f hf => (hmem _).2 (hω g f ((hmem f).1 hf))
  exact ⟨om, fun g x hx => let ⟨h1, h2⟩ := hom g ⟨x, hx⟩; ⟨h1, h2⟩⟩

open scoped Classical in

theorem comp_mem_schA {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : (fun x : κ' → AF F => Φ (x ∘ σ)) ∈ GlobalTheory.WeilM.schA F κ' := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let A : (κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
      (LinearEquiv.funCongrLeft ℝ (mixedEmbedding.mixedSpace F) σ).toContinuousLinearEquiv
    let B : (κ' → Af F) ≃ₜ (κ → Af F) := (Homeomorph.piCongrLeft (Y := fun _ => Af F) σ).symm
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A f, g ∘ B,
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩, ?_⟩
    rfl
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h => exact Submodule.smul_mem _ c h

theorem thV_add {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} {N : ℕ}
    (hR : IsTotallyReal F) (hψ : IsCharAF F ψ) {Φ Φ' : (Fin N → AF F) → ℂ} (hΦ : Decay Φ) (hΦ' : Decay Φ') :
    thV ψ (Φ + Φ') = thV ψ Φ + thV ψ Φ' := by
  funext w
  have hs : ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      Summable fun ξ : Fin N → F => GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i) := fun Φ hΦ => by
    refine Summable.of_norm ?_
    simp only [GlobalTheory.WeilM.schr, norm_mul, hψ.2.1, one_mul]
    exact (GlobalTheory.decay_integrable_periodise F N hR Φ hΦ).2.1 w.1
  rw [Pi.add_apply, thV, thV, thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.thetaSum,
    ← (hs Φ hΦ).tsum_add (hs Φ' hΦ')]
  exact tsum_congr fun ξ => mul_add _ _ _

section Pair

variable {D : D7} {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
  {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {ξ : AE D}

theorem symplO_eq_symp (hA : JA = T.gramᵀ) (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (x y : WO S T) : symplO S T x y =
      GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y := by
  unfold symplO GlobalTheory.WeilM.symp hO GlobalTheory.WeilM.hTens
  congr 1
  have h : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := fun j l => by
    have := congrFun (congrFun hB j) l
    rw [← map_mul]
    exact this
  have hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig z = cA D z := fun z => rfl
  simp only [Finset.mul_sum, hc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  have h' : incM D.host.F JA d c = incA D (T.gram c d) := by rw [hA]; rfl
  rw [h']
  linear_combination (-(x d a * incA D (T.gram c d) * cA D (y c b))) * h a b

theorem mem_GA_target (hA : JA = T.gramᵀ) (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)) :
    a.1 ∈ HR (AF D.host.F) D.sp.cm.sig T.gram := by
  have h := congrArg Matrix.transpose a.2
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h
  subst hA
  exact h

def contra {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] : GL n A →* GL n A where
  toFun g := ⟨(g⁻¹).1ᵀ, g.1ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp only [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

theorem contra_rel {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (c : A →+* A) {G H J : Matrix n n A} {ξ x : A}
    (hGH : G * H = 1) (hx : IsUnit x) (hJ : ξ • J = x • H) (b : GL n A) (h0 : b.1ᵀ * J * b.1.map c = J) :
    (b⁻¹).1.map c * G * (b⁻¹).1ᵀ = G := by
  have hHG : H * G = 1 := mul_eq_one_comm.1 hGH
  have h1 : b.1ᵀ * H * b.1.map c = H := by
    have h2 : b.1ᵀ * (ξ • J) * b.1.map c = ξ • J := by rw [Matrix.mul_smul, Matrix.smul_mul, h0]
    rw [hJ, Matrix.mul_smul, Matrix.smul_mul] at h2
    exact hx.smul_left_cancel.1 h2
  have h3 : (b⁻¹).1.map c * b.1.map c = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h4 : (b⁻¹).1ᵀ * b.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h5 : (b⁻¹).1.map c * G * (b⁻¹).1ᵀ * H = 1 := by
    conv_lhs => rw [← h1]
    calc _ = (b⁻¹).1.map c * (G * (((b⁻¹).1ᵀ * b.1ᵀ) * H)) * b.1.map c := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h4, Matrix.one_mul, hGH, Matrix.mul_one, h3]
  calc _ = (b⁻¹).1.map c * G * (b⁻¹).1ᵀ * H * G := by rw [Matrix.mul_assoc _ H G, hHG, Matrix.mul_one]
    _ = G := by rw [h5, Matrix.one_mul]

theorem mem_GA_source (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    contra b.1 ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := by
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hGH : S.gram.map (incA D) * (S.gram⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : IsUnit (incA D D.host.xi0) := (IsUnit.mk0 _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hB' : ξ • incM D.host.F JB = incA D D.host.xi0 • (S.gram⁻¹).map (incA D) := by
    rw [hB]
    ext i j
    exact map_mul (incA D) _ _
  exact contra_rel (cA D) hGH hx hB' b.1 b.2

def pairHom (hA : JA = T.gramᵀ) (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) :
    GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* GA D S × GA D T where
  toFun p := ((⟨contra p.2.1, mem_GA_source hB p.2⟩ : HR (AF D.host.F) D.sp.cm.sig S.gram),
    (⟨p.1.1, mem_GA_target hA p.1⟩ : HR (AF D.host.F) D.sp.cm.sig T.gram))
  map_one' := Prod.ext (Subtype.ext (map_one contra)) rfl
  map_mul' p q := Prod.ext (Subtype.ext (map_mul contra p.2.1 q.2.1)) rfl

theorem pairHom_eq (hA : JA = T.gramᵀ) (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) (g : GA D S) (h : GA D T)
    (hh : mt T h = a.1.1) (hg : mt S g = (b⁻¹).1.1ᵀ) : pairHom hA hB (a, b) = (g, h) :=
  Prod.ext (Subtype.ext (Units.ext hg.symm)) (Subtype.ext (Units.ext hh.symm))

variable {ψ : AddChar (AF D.host.F) ℂ} {κ : Type} [Fintype κ]
  (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)

def numCoord {N : ℕ} (σ : κ ≃ Fin N) : WO S T ≃ₗ[AF D.host.F] VA D.host.F N :=
  co.e.trans ((LinearEquiv.funCongrLeft _ _ σ.symm).prodCongr (LinearEquiv.funCongrLeft _ _ σ.symm))

theorem numCoord_apply {N : ℕ} (σ : κ ≃ Fin N) (w : WO S T) :
    numCoord co σ w = ((co.e w).1 ∘ σ.symm, (co.e w).2 ∘ σ.symm) := rfl

theorem thetaTr_eq {N : ℕ} (σ : κ ≃ Fin N) (Φ : (κ → AF D.host.F) → ℂ) :
    GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = thV ψ (fun x => Φ (x ∘ σ)) ∘ numCoord co σ := by
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, thV, Function.comp_apply, GlobalTheory.WeilM.thetaSum, numCoord_apply]
  rw [← (Equiv.arrowCongr σ (Equiv.refl D.host.F)).tsum_eq]
  refine tsum_congr fun η => ?_
  have e : (fun i => algebraMap D.host.F (AF D.host.F) (Equiv.arrowCongr σ (Equiv.refl D.host.F) η i)) =
      (fun i => algebraMap D.host.F (AF D.host.F) (η i)) ∘ σ.symm := rfl
  rw [e]
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, comp_equiv_dotProduct_comp_equiv]
  congr 2
  funext i
  simp

theorem thetaTr_bij (hψ : IsStdChar D ψ (-1)) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) :
    (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (Φ + Φ') =
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ + GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ') ∧
    (∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ' → Φ = Φ') ∧
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔
      ∃ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  have he : ∀ w w', symplO S T w w' = symV (numCoord co σ w) (numCoord co σ w') := fun w w' => by
    rw [symplO_eq_symp hA hB, co.form]
    simp only [symV, numCoord_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : Fin (Fintype.card κ) → D.host.F,
      numCoord co σ (incM D.host.F x) = (rat y, rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ σ.symm, z ∘ σ.symm, by rw [numCoord_apply, h]; rfl⟩
  refine ⟨fun Φ hΦ Φ' hΦ' => ?_, fun Φ hΦ Φ' hΦ' h => ?_, fun f => ⟨fun hf => ?_, ?_⟩⟩
  · simp only [thetaTr_eq co σ]
    exact congrArg (· ∘ numCoord co σ) (thV_add hR hψ.1 (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace _ _ _ (comp_mem_schA σ hΦ))
      (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace _ _ _ (comp_mem_schA σ hΦ')))
  · simp only [thetaTr_eq co σ] at h
    have h2 := thV_injOn hR hψ.1 (comp_mem_schA σ hΦ) (comp_mem_schA σ hΦ')
      ((numCoord co σ).surjective.injective_comp_right h)
    funext x
    simpa [Function.comp_def] using congrFun h2 (x ∘ σ.symm)
  · obtain ⟨Φ, hΦ, h⟩ := exists_thV_eq hψ he hr hf
    refine ⟨_, comp_mem_schA σ.symm hΦ, ?_⟩
    rw [thetaTr_eq co σ, ← h]
    congr 2
    funext x
    simp [Function.comp_def]
  · rintro ⟨Φ, hΦ, rfl⟩
    rw [thetaTr_eq co σ]
    exact isThetaFunO_thV hψ he hr (comp_mem_schA σ hΦ)

theorem thetaTr_smul (c : ℂ) (Φ : (κ → AF D.host.F) → ℂ) :
    GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (c • Φ) = c • GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ := by
  funext w
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
    Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

end Pair

theorem exists_isTransport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∃ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om := by
  intro D ψ hψ S T χS χT _ _ _ _ JA JB ξ hA hB κ _ co hrat ω hω
  obtain ⟨hadd, hinj, hon⟩ := thetaTr_bij co hψ hA hB hrat
  obtain ⟨om, hom⟩ := exists_transport' _ _ _ hadd (thetaTr_smul co) hinj hon (ω.comp (pairHom hA hB))
    fun p f hf => hω.om_pres _ f hf
  refine ⟨om, ?_⟩
  unfold GlobalTheory.WeilSchrodinger.IsTransport
  intro a b g h hh hg Φ hΦ
  have e : (ω.comp (pairHom hA hB)) (a, b) = ω (g, h) := congrArg ω (pairHom_eq hA hB a b g h hh hg)
  have h2 := hom (a, b) Φ hΦ
  exact ⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩

end GlobalTheory.ThetaTransform

end
