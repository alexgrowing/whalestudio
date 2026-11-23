import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LieSum

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Mem.LiftGen Filter
open scoped Topology Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem hasDerivAt_apply {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) {f : ℝ → WO S T → ℂ}
    (e : ∀ t, ((u t).1 : WO S T → ℂ) = f t) (w : WO S T) :
    HasDerivAt (fun t => f t w) ((A.1 : WO S T → ℂ) w) 0 := by
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (e t) w).symm)

theorem theta_nOp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (hψ : IsStdChar D ψ (-1)) (X : Matrix (Ix S T) (Ix S T) ℂ) (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1)
    (l : ℂ) : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + l • F).1 := by
  obtain ⟨x, d, -, hxd⟩ := GlobalTheory.Mem.Lift.exists_isCCR_theta D θ σ h ψ hψ S T
  have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
  rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
  exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem l hF)

theorem isLittleO_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) :
    (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t := by
  have h : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  rw [hasDerivAt_iff_isLittleO] at h
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => sub_zero t)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]

theorem hasDerivAt_of_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (h : (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t) :
    HasDerivAt (fun t => Φ (u t)) (Φ A) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => (sub_zero t).symm)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]

set_option maxHeartbeats 2000000 in

theorem image_deriv_add {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (z₁ : u₃ 0 = u₁ 0) (zv : v 0 = A₂)
    (hnorm : ∀ t : ℝ, ‖Φ (u₃ t - u₁ t - (t : ℂ) • v t)‖ = ‖Φ (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖) :
    Φ A₃ = Φ (A₁ + A₂) := by
  have hid : ∀ t : ℝ, u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂) = (u₃ t - u₁ t - (t : ℂ) • v t) +
      (t : ℂ) • (v t - v 0) + (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
    rw [z₁, zv]
    simp only [smul_sub, smul_add]
    abel
  have hD : HasDerivAt (fun t => Φ (u₃ t)) (Φ (A₁ + A₂)) 0 := by
    apply hasDerivAt_of_rem
    have o1 := isLittleO_rem Φ d₁
    have o2' := (isLittleO_rem Φ d₂).norm_left
    have o2 : (fun t : ℝ => Φ (u₃ t - u₁ t - (t : ℂ) • v t)) =o[𝓝 0] fun t => t := by
      rw [← Asymptotics.isLittleO_norm_left]
      exact o2'.congr_left fun t => (hnorm t).symm
    have hg : Tendsto (fun t => Φ (v t - v 0)) (𝓝 0) (𝓝 0) := by
      have := ((Φ.continuous.tendsto _).comp dv.continuousAt).sub_const (Φ (v 0))
      rw [sub_self] at this
      refine this.congr fun t => ?_
      simp only [Function.comp, map_sub]
    have o3 : (fun t : ℝ => Φ ((t : ℂ) • (v t - v 0))) =o[𝓝 0] fun t => t := by
      have := (Asymptotics.isBigO_refl (fun t : ℝ => t) (𝓝 0)).smul_isLittleO
        ((Asymptotics.isLittleO_one_iff ℝ).2 hg)
      refine this.congr (fun t => ?_) (fun t => ?_)
      · beta_reduce
        rw [map_smul, Complex.coe_smul]
      · simp
    have hΦ : ∀ t : ℝ, Φ (u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂)) = Φ (u₃ t - u₁ t - (t : ℂ) • v t) +
        Φ ((t : ℂ) • (v t - v 0)) + Φ (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
      rw [hid t, map_add, map_add]
    exact ((o2.add o3).add o1).congr_left fun t => (hΦ t).symm
  have h3 : HasDerivAt (fun t => Φ (u₃ t)) (Φ A₃) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) d₃
  exact h3.unique hD

set_option maxHeartbeats 2000000 in

theorem sum_of_curves (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (γ₁ γ₂ : ℝ → GA D S × GA D T) (h₁ : γ₁ 0 = 1) (h₂ : γ₂ 0 = 1)
    (F : WO S T → ℂ) (hF : IsThetaFunO ψ S T F) {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (e₁ : ∀ t, ((u₁ t).1 : WO S T → ℂ) = om (γ₁ t) F)
    (e₂ : ∀ t, ((u₂ t).1 : WO S T → ℂ) = om (γ₂ t) F)
    (e₃ : ∀ t, ((u₃ t).1 : WO S T → ℂ) = om (γ₁ t * γ₂ t) F)
    (ev : ∀ t, ((v t).1 : WO S T → ℂ) = om (γ₁ t) A₂.1)
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (hA₂ : IsThetaFunO ψ S T A₂.1) : (A₃.1 : WO S T → ℂ) = A₁.1 + A₂.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hk : ∀ (p : GA D S × GA D T) (a b : BB ψ S T), IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro p a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have z₁ : u₃ 0 = u₁ 0 := QB_ext fun x => congrFun
    (by rw [e₃, e₁, h₁, h₂, one_mul] : ((u₃ 0).1 : WO S T → ℂ) = (u₁ 0).1) x
  have z₂ : ((u₂ 0).1 : WO S T → ℂ) = F := by rw [e₂, h₂, map_one, Module.End.one_apply]
  have zv : v 0 = A₂ := QB_ext fun x => congrFun
    (by rw [ev, h₁, map_one, Module.End.one_apply] : ((v 0).1 : WO S T → ℂ) = A₂.1) x
  have th₂ : ∀ t, IsThetaFunO ψ S T (u₂ t).1 := fun t => by rw [e₂]; exact hW.om_pres _ _ hF
  have hnorm : ∀ t : ℝ, ‖toL2 _ _ (μ.restrict 𝓕) (u₃ t - u₁ t - (t : ℂ) • v t)‖ =
      ‖toL2 _ _ (μ.restrict 𝓕) (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖ := fun t => by
    have ea : ((u₃ t - u₁ t - (t : ℂ) • v t).1 : WO S T → ℂ) =
        ((u₃ t).1 : WO S T → ℂ) - (u₁ t).1 - (t : ℂ) • ((v t).1 : WO S T → ℂ) := rfl
    have eb : ((u₂ t - u₂ 0 - (t : ℂ) • A₂).1 : WO S T → ℂ) =
        ((u₂ t).1 : WO S T → ℂ) - (u₂ 0).1 - (t : ℂ) • (A₂.1 : WO S T → ℂ) := rfl
    refine hk (γ₁ t) _ _ ?_ ?_
    · rw [eb]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (th₂ t) (th₂ 0)) ((thetaSub ψ S T).smul_mem _ hA₂)
    · rw [ea, eb, z₂, e₃, e₁, ev, e₂, map_mul, Module.End.mul_apply, map_sub, map_sub, map_smul]
  have key : toL2 _ _ (μ.restrict 𝓕) A₃ = toL2 _ _ (μ.restrict 𝓕) (A₁ + A₂) :=
    image_deriv_add _ d₁ d₂ d₃ dv z₁ zv hnorm
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (A₃ - (A₁ + A₂))
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((A₃ - (A₁ + A₂)).1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (A₃ - (A₁ + A₂)).1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  exact sub_eq_zero.1 h5

end GlobalTheory.Mem.LieSum

set_option maxHeartbeats 2000000 in
open Classical in

theorem GlobalTheory.Mem.LieSum.hasDerivAt_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  intro D V W θ ψ χS χT ω τ hθ hω X hX Y hY F F₁ F₂ hF h₁ h₂ z
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hc := hω.om_cont
  let γ₁ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, 1)
  let γ₂ : ℝ → GA D V × GA D W := fun t => (1, oneP θ W τ Y t)
  let γ₃ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, oneP θ W τ Y t)
  have hγ : ∀ t, γ₃ t = γ₁ t * γ₂ t := fun t => by
    simp only [γ₁, γ₂, γ₃, Prod.mk_mul_mk, mul_one, one_mul]
  have m₁ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₁ t) k l)
      (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k l) 0 := fun k l => by
    simp only [γ₁, GlobalTheory.RealWeil.mM_apply, GlobalTheory.Mem.Lift.WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one,
      GlobalTheory.WeilVacMove.compAt_one, GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ (GlobalTheory.Mem.Lift.WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  have m₂ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₂ t) k l)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) k l) 0 := fun k l => by
    simp only [γ₂, GlobalTheory.RealWeil.mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _
  have m₃ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₃ t) k l)
      (∑ j, (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k j * GlobalTheory.RealWeil.mM θ V W (γ₂ 0) j l +
        GlobalTheory.RealWeil.mM θ V W (γ₁ 0) k j * GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) j l)) 0 :=
    fun k l => by
      simp only [hγ, map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (m₁ k j).mul (m₂ j l)
  obtain ⟨l₁, g₁⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₁
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk continuous_const)
    (fun s t => by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, one_mem _⟩) _ m₁
  obtain ⟨l₂, g₂⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₂
    (continuous_const.prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨one_mem _, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₂
  obtain ⟨l₃, g₃⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₃
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₃]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₃
  have eF := GlobalTheory.RealWeil.coe_toB hψ F hF
  have hFb : IsThetaFunO ψ V W (GlobalTheory.RealWeil.toB hψ F hF).1 := by rw [eF]; exact hF
  obtain ⟨u₁, e₁, d₁⟩ := g₁ _ hFb
  obtain ⟨u₂, e₂, d₂⟩ := g₂ _ hFb
  obtain ⟨u₃, e₃, d₃⟩ := g₃ _ hFb
  have hA₂ := GlobalTheory.Mem.LieSum.theta_nOp h hψ (GlobalTheory.RealWeil.blk (Pi.single τ Y) fun _ => 1) _ hFb l₂
  obtain ⟨v, ev, dv⟩ := g₁ _ hA₂
  rw [eF] at e₁ e₂ e₃
  have k₁ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₁ e₁ z
  have k₂ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₂ e₂ z
  have k₃ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₃ e₃ z
  have hs := GlobalTheory.Mem.LieSum.sum_of_curves hψ hW γ₁ γ₂
    (by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl)
    (by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl) F hF e₁ e₂ (fun t => by rw [e₃, hγ]) ev d₁ d₂ d₃ dv hA₂
  rw [hs, Pi.add_apply, k₁.unique (h₁ z), k₂.unique (h₂ z)] at k₃
  exact k₃
