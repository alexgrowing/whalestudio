import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCompactKinfAndConj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobolevCauchyTendstoSmoothLimitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSizeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightRealFrameElementLeHsPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeTranslateNearOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeDifferenceQuotientStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix Filter
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom
open scoped ENNReal NNReal Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspFrechet

variable {D : D7} {θ : InfFam D} {V : HSp D} {U : Subgroup (GA D V)} {N : ℕ}

theorem growthSob_RderC_le (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (d : ℕ) : growthSob θ V d N (RderC θ V τ Z φ) ≤
      (∑ a : Fin V.rank × Fin V.rank, ‖Z a.1 a.2‖ₑ) * growthSob θ V (d + 1) N φ := by
  classical
  rw [RderC_eq_sum_glDer hθ hs, Finset.sum_mul]
  have hm : ∀ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ ∈ SmFun θ V := fun a =>
    Submodule.smul_mem _ _ ((linOnSm_RderC τ _).mem _ hs)
  generalize (Finset.univ : Finset (Fin V.rank × Fin V.rank)) = s
  induction s using Finset.induction_on with
  | empty =>
    have := growthSob_smul (θ := θ) (φ := φ) 0 d N
    rw [zero_smul, enorm_zero, zero_mul] at this
    simp [this]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine (growthSob_add_le (hm a) (sum_mem fun b _ => hm b) d N).trans (add_le_add ?_ ih)
    rw [growthSob_smul]
    exact mul_le_mul' le_rfl (wordSum_letter_le d _ φ)

variable (θ N) in

def cuspSub (hU : IsOpen (U : Set (GA D V))) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | Continuous φ ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧
    φ ∈ SmFun θ V ∧ IsCuspFun V φ ∧ ∀ d, growthSob θ V d N φ ≠ ⊤}
  add_mem' := fun {φ ψ} ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ =>
    ⟨a1.add b1, fun γ h g => by simp only [Pi.add_apply, a2 γ h, b2 γ h],
      fun k h h' g => by simp only [Pi.add_apply, a3 k h h', b3 k h h'], add_mem a4 b4,
      (GlobalTheory.Mem.Th.isCuspFun_closed D V φ ψ ⟨a2, ⟨U, hU, a3⟩, a1⟩ ⟨b2, ⟨U, hU, b3⟩, b1⟩ a5 b5).1,
      fun d => ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨a6 d, b6 d⟩) (growthSob_add_le a4 b4 d N)⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, fun _ _ _ _ => rfl, zero_mem _,
    fun _ _ _ _ _ _ _ _ => by simp, fun d => by
      have := growthSob_smul (θ := θ) (V := V) (φ := 0) 0 d N
      rw [zero_smul, enorm_zero, zero_mul] at this
      simp [this]⟩
  smul_mem' := fun c φ ⟨a1, a2, a3, a4, a5, a6⟩ =>
    ⟨a1.const_smul c, fun γ h g => by simp only [Pi.smul_apply, a2 γ h],
      fun k h h' g => by simp only [Pi.smul_apply, a3 k h h'], Submodule.smul_mem _ c a4,
      (GlobalTheory.Mem.Th.isCuspFun_closed D V φ φ ⟨a2, ⟨U, hU, a3⟩, a1⟩ ⟨a2, ⟨U, hU, a3⟩, a1⟩ a5 a5).2.1 c,
      fun d => (growthSob_smul c d N).trans_ne (ENNReal.mul_ne_top enorm_ne_top (a6 d))⟩

variable {hU : IsOpen (U : Set (GA D V))}

theorem rTr_mem_cuspSub (hθ : IsInfFam θ) {h : GA D V} (hh : h ∈ GinfC V) {φ : GA D V → ℂ} (hφ : φ ∈ cuspSub θ N hU) :
    rTr V h φ ∈ cuspSub θ N hU := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hφ
  refine ⟨a1.comp (continuous_mul_const h), fun γ hγ g => ?_, fun k h1 h2 g => ?_, rTr_mem_smFun hθ h a4,
    (GlobalTheory.Mem.Th.isCuspFun_closed D V φ φ ⟨a2, ⟨U, hU, a3⟩, a1⟩ ⟨a2, ⟨U, hU, a3⟩, a1⟩ a5 a5).2.2.1 h, fun d => ?_⟩
  · simp only [rTr, mul_assoc, a2 γ hγ]
  · simp only [rTr]
    rw [mul_assoc, ← comm_of_mem V hh h2, ← mul_assoc, a3 k h1 h2]
  · obtain ⟨C, m, hC⟩ := GlobalTheory.T.moderateGrowthSobolevSize_rightTranslate_polyBound D θ hθ V d N
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (a6 d))
      (hC h hh φ a4)

theorem Rder_mem_cuspSub (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    {φ : GA D V → ℂ} (hφ : φ ∈ cuspSub θ N hU) : Rder θ V τ X φ ∈ cuspSub θ N hU := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := id hφ
  have b1 : Continuous (Rder θ V τ X φ) := continuous_rWord hθ a4 a1 ((unifModGrowth_iff_growthSob hθ a4).2 ⟨N, a6⟩)
    (l := [(τ, X)]) fun p hp => by rw [List.mem_singleton.1 hp]; exact hX
  have b2 : ∀ γ ∈ GQ V, ∀ g, Rder θ V τ X φ (γ * g) = Rder θ V τ X φ g := fun γ hγ =>
    rWord_left (θ := θ) (a2 γ hγ) [(τ, X)]
  refine ⟨b1, b2, fun k h1 h2 g => ?_, Rder_mem a4 hX, ?_, fun d => ?_⟩
  · have e : rTr V k φ = φ := funext (a3 k h1 h2)
    exact (congrFun (Rder_rTr_fin h2 τ X φ) g).symm.trans (by rw [e])
  · have hm : ∀ t : ℝ, ((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) ∈ cuspSub θ N hU := fun t =>
      Submodule.smul_mem _ _ (sub_mem (rTr_mem_cuspSub hθ (atTau_mem V τ _) hφ) hφ)
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall fun n =>
        (Nat.one_div_pos_of_nat (α := ℝ)).ne'⟩
    exact GlobalTheory.T.isCuspFun_of_tendsto_moderateGrowthSize D V N _ _ (fun n => ⟨(hm _).1, (hm _).2.1, (hm _).2.2.2.2.1⟩) b1 b2
      ((GlobalTheory.T.tendsto_moderateGrowthSize_differenceQuotient D θ hθ V τ N X hX φ a4 (a6 2)).comp ht)
  · rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top) (a6 _))
      (growthSob_RderC_le hθ a4 τ X d)

variable (θ N hU) in

def Sp : Type := cuspSub θ N hU

instance : AddCommGroup (Sp θ N hU) := inferInstanceAs (AddCommGroup (cuspSub θ N hU))

instance : Module ℂ (Sp θ N hU) := inferInstanceAs (Module ℂ (cuspSub θ N hU))

variable (θ N hU) in

def incl : Sp θ N hU →ₗ[ℂ] (GA D V → ℂ) := (cuspSub θ N hU).subtype

theorem incl_mem (x : Sp θ N hU) : incl θ N hU x ∈ cuspSub θ N hU := x.2

theorem incl_sm (x : Sp θ N hU) : incl θ N hU x ∈ SmFun θ V := (incl_mem x).2.2.2.1

theorem incl_fin (x : Sp θ N hU) (d : ℕ) : growthSob θ V d N (incl θ N hU x) ≠ ⊤ := (incl_mem x).2.2.2.2.2 d

theorem incl_injective : Function.Injective (incl θ N hU) := Subtype.val_injective

variable (θ N hU) in

def sem (d : ℕ) : Seminorm ℂ (Sp θ N hU) :=
  Seminorm.of (fun x => (growthSob θ V d N (incl θ N hU x)).toReal)
    (fun x y => by
      rw [map_add, ← ENNReal.toReal_add (incl_fin x d) (incl_fin y d)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨incl_fin x d, incl_fin y d⟩)
        (growthSob_add_le (incl_sm x) (incl_sm y) d N))
    fun c x => by rw [map_smul, growthSob_smul, ENNReal.toReal_mul, toReal_enorm]

instance : UniformSpace (Sp θ N hU) := (SeminormFamily.addGroupFilterBasis (sem θ N hU)).uniformSpace

instance : IsUniformAddGroup (Sp θ N hU) := (SeminormFamily.addGroupFilterBasis (sem θ N hU)).isUniformAddGroup

theorem withSem : WithSeminorms (sem θ N hU) := ⟨rfl⟩

instance : ContinuousSMul ℂ (Sp θ N hU) := withSem.continuousSMul

theorem tendsto_iff {α : Type} {F : Filter α} {u : α → Sp θ N hU} {y : Sp θ N hU} : Tendsto u F (𝓝 y) ↔
    ∀ d, Tendsto (fun a => growthSob θ V d N (incl θ N hU (u a - y))) F (𝓝 0) := by
  rw [withSem.tendsto_nhds]
  refine forall_congr' fun d => ?_
  rw [← ENNReal.tendsto_toReal_iff (fun _ => incl_fin _ d) ENNReal.zero_ne_top, ENNReal.toReal_zero,
    Metric.tendsto_nhds]
  simp only [dist_zero_right, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  rfl

theorem tendsto_zero_iff {α : Type} {F : Filter α} {u : α → Sp θ N hU} : Tendsto u F (𝓝 0) ↔
    ∀ d, Tendsto (fun a => growthSob θ V d N (incl θ N hU (u a))) F (𝓝 0) := by
  simp only [tendsto_iff, sub_zero]

theorem tendsto_apply_of_size {α : Type} {F : Filter α} {u : α → GA D V → ℂ} {f : GA D V → ℂ}
    (h : Tendsto (fun a => growthSize V N (u a - f)) F (𝓝 0)) (g : GA D V) : Tendsto (fun a => u a g) F (𝓝 (f g)) := by
  have h1 : Tendsto (fun a => ENNReal.ofReal (‖u a g - f g‖ / height V g ^ N)) F (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) fun a =>
      le_iSup (fun g => ENNReal.ofReal (‖(u a - f) g‖ / height V g ^ N)) g
  have hp := pow_pos (height_pos V g) N
  have h2 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1).mul_const (height V g ^ N)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [ENNReal.toReal_zero, zero_mul] at h2
  refine h2.congr fun a => ?_
  rw [Function.comp, ENNReal.toReal_ofReal (by positivity), div_mul_cancel₀ _ hp.ne']

instance : T2Space (Sp θ N hU) := by
  have : T1Space (Sp θ N hU) := withSem.T1_of_separating fun x hx => ⟨0, fun h0 => hx (incl_injective (funext fun g => ?_))⟩
  · infer_instance
  have h1 : growthSob θ V 0 N (incl θ N hU x) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right (incl_fin x 0)
  rw [growthSob, wordSum_zero] at h1
  simpa using (growthSize_le_iff (C := 0) le_rfl).1 (h1.le.trans zero_le) g

theorem completeSpace (hθ : IsInfFam θ) : CompleteSpace (Sp θ N hU) := by
  have := (withSem (θ := θ) (N := N) (hU := hU)).firstCountableTopology
  have : (_root_.uniformity (Sp θ N hU)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
  have h1 := hu.tendsto_uniformity
  rw [uniformity_eq_comap_nhds_zero_swapped, tendsto_comap_iff] at h1
  obtain ⟨f, f1, f2, f3⟩ := GlobalTheory.T.growthSobolev_cauchy_tendsto_smooth_limit D θ hθ V N (fun n => incl θ N hU (u n))
    (fun n => ⟨(incl_mem _).1, incl_sm _, incl_fin _⟩) fun d => by
      simpa only [Function.comp, map_sub, Prod.map] using tendsto_zero_iff.1 h1 d
  have f0 := f3 0
  simp only [growthSob, wordSum_zero] at f0
  have p := tendsto_apply_of_size f0
  have l : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g := fun γ hγ g =>
    tendsto_nhds_unique (p _) ((p g).congr fun n => ((incl_mem _).2.1 γ hγ g).symm)
  refine ⟨⟨f, f1, l, fun k h1 h2 g => tendsto_nhds_unique (p _) ((p g).congr fun n => ((incl_mem _).2.2.1 k h1 h2 g).symm),
    f2, GlobalTheory.T.isCuspFun_of_tendsto_moderateGrowthSize D V N _ f (fun n => ⟨(incl_mem _).1, (incl_mem _).2.1, (incl_mem _).2.2.2.2.1⟩) f1 l f0,
    fun d => ?_⟩, tendsto_iff.2 f3⟩
  obtain ⟨n, hn⟩ := ((f3 d).eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
  have e : f = incl θ N hU (u n) + (-1 : ℂ) • (incl θ N hU (u n) - f) := by simp
  rw [e]
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨incl_fin _ d, ?_⟩)
    (growthSob_add_le (incl_sm _) (Submodule.smul_mem _ _ (sub_mem (incl_sm _) f2)) d N)
  rw [growthSob_smul]
  exact ENNReal.mul_ne_top enorm_ne_top hn.ne

theorem continuous_of_le (T : Sp θ N hU →ₗ[ℂ] Sp θ N hU) (h : ∀ d, ∃ (d' : ℕ) (c : ℝ≥0∞), c ≠ ⊤ ∧
    ∀ x, growthSob θ V d N (incl θ N hU (T x)) ≤ c * growthSob θ V d' N (incl θ N hU x)) : Continuous T := by
  refine continuous_of_continuousAt_zero T ?_
  rw [ContinuousAt, map_zero]
  refine tendsto_zero_iff.2 fun d => ?_
  obtain ⟨d', c, hc, h⟩ := h d
  have := ENNReal.Tendsto.const_mul (tendsto_zero_iff.1 (tendsto_id (x := 𝓝 (0 : Sp θ N hU))) d') (a := c) (Or.inr hc)
  rw [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le) h

variable (N hU) in

def act (hθ : IsInfFam θ) (h : GinfC V) : Sp θ N hU →L[ℂ] Sp θ N hU where
  toLinearMap := (rTrLin h.1).restrict fun _ hx => rTr_mem_cuspSub hθ h.2 hx
  cont := continuous_of_le _ fun d => by
    obtain ⟨C, m, hC⟩ := GlobalTheory.T.moderateGrowthSobolevSize_rightTranslate_polyBound D θ hθ V d N
    exact ⟨d, _, ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, fun x => hC h.1 h.2 _ (incl_sm x)⟩

theorem RderC_mem_cuspSub (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {φ : GA D V → ℂ} (hφ : φ ∈ cuspSub θ N hU) : RderC θ V τ Z φ ∈ cuspSub θ N hU :=
  add_mem (Rder_mem_cuspSub hθ (GlobalTheory.SmoothAutCheck.parts_mem V τ Z).1 hφ)
    (Submodule.smul_mem _ _ (Rder_mem_cuspSub hθ (GlobalTheory.SmoothAutCheck.parts_mem V τ Z).2 hφ))

variable (N hU) in

def derL (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ →ₗ[ℂ] Sp θ N hU →ₗ[ℂ] Sp θ N hU :=
  LinearMap.mk₂ ℂ (fun Z x => ⟨RderC θ V τ Z (incl θ N hU x), RderC_mem_cuspSub hθ τ Z (incl_mem x)⟩)
    (fun Z Z' x => incl_injective (RderC_add hθ (incl_sm x) τ Z Z'))
    (fun c Z x => incl_injective (RderC_smul hθ (incl_sm x) τ c Z))
    (fun Z x y => incl_injective ((linOnSm_RderC τ Z).add _ (incl_sm x) _ (incl_sm y)))
    fun c Z _ => incl_injective ((linOnSm_RderC τ Z).smul c _)

theorem incl_derL (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : Sp θ N hU) :
    incl θ N hU (derL N hU hθ τ Z x) = RderC θ V τ Z (incl θ N hU x) := rfl

variable (N hU) in

def der (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Sp θ N hU →L[ℂ] Sp θ N hU where
  toLinearMap := derL N hU hθ τ Z
  cont := continuous_of_le _ fun d => ⟨d + 1, _, ENNReal.sum_ne_top.2 fun _ _ => enorm_ne_top, fun x =>
    growthSob_RderC_le hθ (incl_sm x) τ Z d⟩

theorem continuous_derL (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : Sp θ N hU) :
    Continuous fun Z => derL N hU hθ τ Z x :=
  ((derL N hU hθ τ).flip x).continuous_of_finiteDimensional

theorem derL_act (hθ : IsInfFam θ) (h : GinfC V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : Sp θ N hU) : derL N hU hθ τ Z (act N hU hθ h x) = act N hU hθ h (derL N hU hθ τ (adAt θ h.1 τ Z) x) :=
  incl_injective (RderC_rTr hθ ⟨h.2, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V h.1⟩ τ Z _)

theorem tendsto_act_zero (hθ : IsInfFam θ) {α : Type} {F : Filter α} {h : α → GinfC V} {z : α → Sp θ N hU}
    (hh : Tendsto (fun a => (h a).1) F (𝓝 1)) (hz : Tendsto z F (𝓝 0)) :
    Tendsto (fun a => act N hU hθ (h a) (z a)) F (𝓝 0) := by
  refine tendsto_zero_iff.2 fun d => ?_
  obtain ⟨C, m, hC⟩ := GlobalTheory.T.moderateGrowthSobolevSize_rightTranslate_polyBound D θ hθ V d N
  have h1 : Tendsto (fun a => (C : ℝ≥0∞) * ENNReal.ofReal (height V (h a).1 ^ m)) F
      (𝓝 ((C : ℝ≥0∞) * ENNReal.ofReal (height V 1 ^ m))) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ((((continuous_height V).tendsto 1).comp hh).pow m))
      (Or.inr ENNReal.coe_ne_top)
  have hn : (C : ℝ≥0∞) * ENNReal.ofReal (height V 1 ^ m) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have := ENNReal.Tendsto.mul h1 (Or.inr ENNReal.zero_ne_top) (tendsto_zero_iff.1 hz d) (Or.inr hn)
  rw [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le) fun a =>
    hC _ (h a).2 _ (incl_sm _)

theorem tendsto_zero_of_comm (hθ : IsInfFam θ) {α : Type} {F : Filter α} (u : α → Sp θ N hU → Sp θ N hU)
    (h0 : ∀ x, Tendsto (fun a => growthSize V N (incl θ N hU (u a x))) F (𝓝 0))
    (hs : ∀ τ Z x, Tendsto (fun a => derL N hU hθ τ Z (u a x) - u a (derL N hU hθ τ Z x)) F (𝓝 0)) (x : Sp θ N hU) :
    Tendsto (fun a => u a x) F (𝓝 0) := by
  have key : ∀ l : List (D.what₂.Tau × Fin V.rank × Fin V.rank), ∀ x,
      Tendsto (fun a => growthSize V N (wordAct (glDer θ V) l (incl θ N hU (u a x)))) F (𝓝 0) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => exact h0
    | append_singleton l i ih =>
      intro x
      have := (tendsto_zero_iff.1 (hs i.1 (Matrix.single i.2.1 i.2.2 1) x) l.length).add
        (ih (derL N hU hθ i.1 (Matrix.single i.2.1 i.2.2 1) x))
      rw [add_zero] at this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le) fun a => ?_
      refine le_trans ?_ (add_le_add (le_wordSum (l := l) le_rfl _) le_rfl)
      refine le_of_eq_of_le (congrArg _ ?_) growthSize_add_le
      rw [← (linOnSm_glWord l).add _ (incl_sm _) _ (incl_sm _), ← map_add, sub_add_cancel, wordAct_append]
      rfl
  refine tendsto_zero_iff.2 fun d => ?_
  simpa only [Finset.sum_const_zero, growthSob, wordSum] using tendsto_finsetSum (Finset.range (d + 1)) fun k _ =>
    tendsto_finsetSum Finset.univ fun (a : Fin k → _) _ => key (List.ofFn a) x

variable (θ) in

def pt (τ : D.what₂.Tau) (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GinfC V := ⟨atTau θ V τ u, atTau_mem V τ u⟩

theorem tendsto_act_one (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : Sp θ N hU) :
    Tendsto (fun u => act N hU hθ (pt θ τ u) x - x) (𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1) (𝓝 0) := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have h1 : Tendsto (fun u => (pt θ τ u).1) (𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1) (𝓝 1) := by
    have := continuousOn_atTau hθ V τ 1 (one_mem_UH _)
    rwa [ContinuousWithinAt, atTau_one hθ] at this
  refine tendsto_zero_of_comm hθ (fun u x => act N hU hθ (pt θ τ u) x - x)
    (fun x => GlobalTheory.T.tendsto_moderateGrowthSize_translate_near_one D θ hθ V τ N _ (incl_sm x) (incl_fin x 1)) (fun τ' Z x => ?_) x
  have hm := GlobalTheory.Cusp.KinfCompact.continuous_realMat hθ V τ'
  have h2 : Continuous fun h : GA D V => derL N hU hθ τ' (adAt θ h τ' Z - Z) x :=
    (continuous_derL hθ τ' x).comp ((((hm.comp continuous_inv).matrix_mul continuous_const).matrix_mul hm).sub
      continuous_const)
  have h3 := (h2.tendsto' 1 0 (by simp [adAt, infMat_one])).comp h1
  refine (tendsto_act_zero hθ h1 h3).congr fun u => ?_
  simp only [Function.comp, map_sub, LinearMap.sub_apply, derL_act]
  abel

theorem act_mul (hθ : IsInfFam θ) (a b : GinfC V) (x : Sp θ N hU) :
    act N hU hθ (a * b) x = act N hU hθ a (act N hU hθ b x) :=
  incl_injective (funext fun g => congrArg (incl θ N hU x) (mul_assoc g a.1 b.1).symm)

theorem act_one (hθ : IsInfFam θ) (x : Sp θ N hU) : act N hU hθ 1 x = x :=
  incl_injective (funext fun g => congrArg (incl θ N hU x) (mul_one g))

theorem pt_mul (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    pt θ τ (g * g') = pt θ τ g * pt θ τ g' := Subtype.ext (atTau_mul hθ V τ hg hg')

theorem continuousOn_act (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : Sp θ N hU) :
    ContinuousOn (fun u => act N hU hθ (pt θ τ u) x) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  intro u hu
  have hv := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (atTau θ V τ u)⁻¹ τ
  have huv := infMat_mul_inv θ V τ (atTau θ V τ u)
  rw [(atTau_spec hθ V τ hu).2.1] at huv
  generalize infMat D.sp.cm.sig V.gram (θ τ) (atTau θ V τ u)⁻¹ = v at hv huv
  have h1 : Tendsto (fun w => v * w) (𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] u) (𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1) := by
    rw [← mul_eq_one_comm.1 huv]
    exact (continuous_const.matrix_mul continuous_id).continuousWithinAt.tendsto_nhdsWithin fun w hw => mul_mem_UH hv hw
  have h2 := ((act N hU hθ (pt θ τ u)).continuous.tendsto' 0 0 (map_zero _)).comp ((tendsto_act_one hθ τ x).comp h1)
  refine tendsto_sub_nhds_zero_iff.1 (h2.congr' (eventually_mem_nhdsWithin.mono fun w hw => ?_))
  simp only [Function.comp, map_sub]
  rw [← act_mul, ← pt_mul hθ τ hu (mul_mem_UH hv hw), ← Matrix.mul_assoc, huv, Matrix.one_mul]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem tendsto_ad_exp {n : ℕ} (X Z : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (NormedSpace.exp ((-t) • X) * Z * NormedSpace.exp (t • X) - Z)) (𝓝[≠] 0)
      (𝓝 (Z * X - X * Z)) := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have h2 := HasDerivAt.scomp (0 : ℝ) (h := fun t : ℝ => -t) (by rw [neg_zero]; exact h1) (hasDerivAt_neg (0 : ℝ))
  have h3 := ((h2.mul_const Z).mul h1).tendsto_slope_zero
  simp only [zero_add, Function.comp, neg_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, Pi.mul_apply,
    neg_smul, one_smul, neg_mul] at h3
  rw [neg_add_eq_sub] at h3
  refine h3.congr fun t => ?_
  rw [← Complex.ofReal_inv, Complex.coe_smul, neg_smul]
  rfl

theorem tendsto_quot (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (x : Sp θ N hU) : Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (act N hU hθ (pt θ τ (NormedSpace.exp (t • X))) x - x) -
      derL N hU hθ τ X x) (𝓝[≠] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (pt θ τ (NormedSpace.exp (t • X))).1) (𝓝[≠] 0) (𝓝 1) :=
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).tendsto' 0 1 (GlobalTheory.Mem.Lift.oneP_zero hθ)).mono_left nhdsWithin_le_nhds
  have h1' : Tendsto (fun t : ℝ => NormedSpace.exp (t • X)) (𝓝[≠] 0) (𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_matrix fun i j => continuous_iff_continuousAt.2 fun t =>
      (GlobalTheory.Mem.Lift.hasDerivAt_exp_entry X t i j).continuousAt).tendsto' 0 1 (by simp)).mono_left nhdsWithin_le_nhds,
      .of_forall (GlobalTheory.Mem.Lift.exp_mem hX)⟩
  have eX : ∀ y : Sp θ N hU, incl θ N hU (derL N hU hθ τ X y) = Rder θ V τ X (incl θ N hU y) := fun y =>
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX _
  refine tendsto_zero_of_comm hθ (fun (t : ℝ) x => ((t : ℂ)⁻¹) • (act N hU hθ (pt θ τ (NormedSpace.exp (t • X))) x - x) -
      derL N hU hθ τ X x) (fun x => ?_) (fun τ' Z x => ?_) x
  · simp only [map_sub, eX]
    exact GlobalTheory.T.tendsto_moderateGrowthSize_differenceQuotient D θ hθ V τ N X hX _ (incl_sm x) (incl_fin x 2)
  obtain ⟨B, hB, hb⟩ : ∃ B, Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (adAt θ (oneP θ V τ X t) τ' Z - Z)) (𝓝[≠] 0) (𝓝 B) ∧
      derL N hU hθ τ' Z (derL N hU hθ τ X x) = derL N hU hθ τ X (derL N hU hθ τ' Z x) + derL N hU hθ τ' B x := by
    have hi : ∀ t, (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := fun t => inv_eq_of_mul_eq_one_right (by
      rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ])
    have hs := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX
    have hbr := GlobalTheory.T.complexDerivative_rightDerivative_commutator D θ hθ V τ τ' Z X hX _ (incl_sm x)
    by_cases c : τ' = τ
    · subst c
      refine ⟨_, (tendsto_ad_exp X Z).congr fun t => ?_, incl_injective ?_⟩
      · rw [adAt, hi, (hs _).2.1, (hs _).2.1]
      · rw [map_add, eX, incl_derL, eX]
        exact hbr.1
    · refine ⟨0, tendsto_const_nhds.congr fun t => ?_, incl_injective ?_⟩
      · rw [adAt, hi, (hs _).2.2 _ c, (hs _).2.2 _ c, Matrix.one_mul, Matrix.mul_one, sub_self, smul_zero]
      · rw [map_zero, LinearMap.zero_apply, add_zero, eX, incl_derL, eX]
        exact hbr.2 c
  have h2 := ((continuous_derL hθ τ' x).tendsto' 0 0 (by simp)).comp (tendsto_sub_nhds_zero_iff.2 hB)
  have h3 := (tendsto_act_zero hθ h1 h2).add ((tendsto_act_one hθ τ (derL N hU hθ τ' B x)).comp h1')
  rw [add_zero] at h3
  refine h3.congr fun t => ?_
  simp only [Function.comp, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, derL_act, hb, smul_sub]
  change _ = _ • act N hU hθ _ (derL N hU hθ τ' (adAt θ (oneP θ V τ X t) τ' Z) x) - _ - _ - _
  abel

theorem fr_mul_inv (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) : A.fr τ * (A.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))

theorem conj_mem_UH (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hk : k ∈ Formalism.MainNotions.S.UJset (A.ε τ)) : (A.fr τ)⁻¹ * k * A.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have h1 := fr_mul_inv A τ
  have hk' : kᴴ * Formalism.REAL.Jm (A.ε τ) * k = Formalism.REAL.Jm (A.ε τ) := hk
  have h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← A.fr_gram τ]
  calc _ = (A.fr τ)ᴴ * (kᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * k) *
        A.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

theorem conj_mem_lieAt (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (A.ε τ)) : (A.fr τ)⁻¹ * X * A.fr τ ∈ lieAt V τ := by
  have h1 := fr_mul_inv A τ
  have hX' : Xᴴ * Formalism.REAL.Jm (A.ε τ) + Formalism.REAL.Jm (A.ε τ) * X = 0 := hX
  have h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ + _ * _ = _
  rw [← A.fr_gram τ]
  calc _ = (A.fr τ)ᴴ * (Xᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) +
        Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * X) * A.fr τ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem isSmoothModRep (hθ : IsInfFam θ) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) :
    GlobalTheory.SmoothGlob.IsSmoothModRep (A.ε τ) (sem θ N hU) (fun g => act N hU hθ (pt θ τ ((A.fr τ)⁻¹ * g * A.fr τ)))
      fun X => der N hU hθ τ ((A.fr τ)⁻¹ * X * A.fr τ) where
  withSeminorms := withSem
  map_one := ContinuousLinearMap.ext fun x => by
    rw [Matrix.mul_one, mul_eq_one_comm.1 (fr_mul_inv A τ), show pt θ τ 1 = 1 from Subtype.ext (atTau_one hθ V τ)]
    exact act_one hθ x
  map_mul a ha b hb := ContinuousLinearMap.ext fun x => by
    rw [ContinuousLinearMap.comp_apply, ← act_mul, ← pt_mul hθ τ (conj_mem_UH A τ ha) (conj_mem_UH A τ hb)]
    congr 3
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (A.fr τ), fr_mul_inv, Matrix.one_mul]
  continuousOn v := (continuousOn_act hθ τ v).comp
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn fun _ h => conj_mem_UH A τ h
  hasDRep X hX v := by
    refine tendsto_sub_nhds_zero_iff.1 ((tendsto_quot hθ (conj_mem_lieAt A τ hX) v).congr fun t => ?_)
    beta_reduce
    rw [← Matrix.exp_conj' _ _ (A.fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]
    rfl
  growth i := by
    obtain ⟨C, m, hC⟩ := GlobalTheory.T.moderateGrowthSobolevSize_rightTranslate_polyBound D θ hθ V i N
    obtain ⟨C', m', hC'⟩ := GlobalTheory.T.unitaryAdelicHeight_realFrameElement_le_hsPow D θ hθ V A τ
    refine ⟨(C * ‖C'‖₊ ^ m) • sem θ N hU i, m' * m, (withSem.continuous_seminorm i).const_smul (C * ‖C'‖₊ ^ m),
      fun g hg v => ?_⟩
    have h0 : 0 ≤ Formalism.REAL.hs g := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
      (incl_fin v i)) (hC (A.elt θ τ g) (atTau_mem V τ _) _ (incl_sm v))
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (pow_pos (height_pos V _) m).le] at h1
    have h2 := pow_le_pow_left₀ (height_pos V _).le ((hC' g hg).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))) m
    refine h1.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 C.coe_nonneg)
      ENNReal.toReal_nonneg).trans_eq ?_)
    change _ = _ * (((C * ‖C'‖₊ ^ m : ℝ≥0) : ℝ) * (growthSob θ V i N (incl θ N hU v)).toReal)
    rw [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, mul_pow, pow_mul]
    ring

theorem exists_frechet : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → ∃ (E : Type) (_ : AddCommGroup E) (_ : Module ℂ E) (_ : UniformSpace E) (_ : IsUniformAddGroup E) (_ : CompleteSpace E) (_ : T2Space E) (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)), Function.Injective ι ∧ (∀ φ, φ ∈ Set.range ι ↔ Continuous φ ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N φ ≠ ⊤) ∧ (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) ∧ ∀ τ, ∃ π dπ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E), GlobalTheory.SmoothGlob.IsSmoothModRep (A.ε τ) p π dπ ∧ (∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), ∀ x, ι (π g x) = rTr V (A.elt θ τ g) (ι x)) ∧ ∀ X ∈ GlobalTheory.SmoothGlob.lieSet (A.ε τ), ∀ x, ι (dπ X x) = Rder θ V τ ((A.fr τ)⁻¹ * X * A.fr τ) (ι x) := by
  intro D θ hθ V A U N hU
  refine ⟨Sp θ N hU, inferInstance, inferInstance, inferInstance, inferInstance, completeSpace hθ, inferInstance,
    sem θ N hU, incl θ N hU, incl_injective, fun φ => ⟨?_, fun h => ⟨⟨φ, h⟩, rfl⟩⟩, fun _ _ => rfl, fun τ =>
    ⟨_, _, isSmoothModRep hθ A τ, fun _ _ _ => rfl, fun X hX x =>
      GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (conj_mem_lieAt A τ hX) _⟩⟩
  rintro ⟨x, rfl⟩
  exact incl_mem x

end GlobalTheory.CuspFrechet

end
