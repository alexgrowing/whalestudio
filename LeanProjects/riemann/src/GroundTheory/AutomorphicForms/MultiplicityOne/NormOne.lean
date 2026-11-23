import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import GroundTheory.AutomorphicForms.CuspidalDiscreteness

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem mul_centralSection_inv_mem (g : AdelicGLn.AdelicGL K n) :
    g * (centralSection K n (detModule K n g))⁻¹ ∈ normOneGL K n := by
  rw [mem_normOneGL_iff_detModule, map_mul, map_inv]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.AdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim g 1, Subsingleton.elim (centralSection K 0 _) 1]
    simp
  · rw [detModule_centralSection hn, mul_inv_cancel]

def retract (g : AdelicGLn.AdelicGL K n) : normOneGL K n :=
  ⟨g * (centralSection K n (detModule K n g))⁻¹, mul_centralSection_inv_mem g⟩

theorem coe_retract (g : AdelicGLn.AdelicGL K n) :
    (retract g : AdelicGLn.AdelicGL K n) = g * (centralSection K n (detModule K n g))⁻¹ := rfl

theorem retract_coe (x : normOneGL K n) : retract (x : AdelicGLn.AdelicGL K n) = x := by
  ext1
  rw [coe_retract, (mem_normOneGL_iff_detModule).1 x.2, map_one, inv_one, mul_one]

theorem retract_mul_left (x : normOneGL K n) (g : AdelicGLn.AdelicGL K n) :
    retract ((x : AdelicGLn.AdelicGL K n) * g) = x * retract g := by
  ext1
  rw [coe_retract, Subgroup.coe_mul, coe_retract, map_mul, (mem_normOneGL_iff_detModule).1 x.2,
    one_mul, mul_assoc]

theorem continuous_retract : Continuous (retract (K := K) (n := n)) :=
  continuous_induced_rng.2 (continuous_id.mul
    ((continuous_centralSection.comp continuous_detModule).inv))

theorem retract_mul_finEmb (g : AdelicGLn.AdelicGL K n) {u : AdelicGLn.FiniteAdelicGL K n}
    (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    retract (g * finEmb K n u) = retract g * finOne K n ⟨u, hu⟩ := by
  have h1 : detModule K n (finEmb K n u) = 1 :=
    (mem_normOneGL_iff_detModule).1 (finOne K n ⟨u, hu⟩).2
  ext1
  rw [coe_retract, Subgroup.coe_mul, coe_retract, coe_finOne, map_mul, h1, mul_one, mul_assoc,
    ← centralSection_inv_mul_comm, ← mul_assoc]

def lift (ϕ : normOneGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ := ϕ (retract g)

theorem lift_coe (ϕ : normOneGL K n → ℂ) (x : normOneGL K n) :
    lift ϕ (x : AdelicGLn.AdelicGL K n) = ϕ x := by
  rw [lift, retract_coe]

theorem continuous_lift {ϕ : normOneGL K n → ℂ} (hϕ : Continuous ϕ) : Continuous (lift ϕ) :=
  hϕ.comp continuous_retract

theorem isLeftInvariant_lift {ϕ : normOneGL K n → ℂ}
    (hϕ : ∀ γ ∈ Γ₁, ∀ x, ϕ (γ * x) = ϕ x) : IsLeftInvariant (lift ϕ) := by
  intro γ g
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
  set γ₁ : normOneGL K n := ⟨AdelicGLn.diagonal K n γ, hγ1⟩
  have hγΓ : γ₁ ∈ Γ₁ := ⟨γ, rfl⟩
  show ϕ (retract ((γ₁ : AdelicGLn.AdelicGL K n) * g)) = ϕ (retract g)
  rw [retract_mul_left, hϕ γ₁ hγΓ]

theorem isCuspidal_lift {ϕ : normOneGL K n → ℂ}
    (hϕ : ∀ r : ℕ, 0 < r → r < n → ∀ x : normOneGL K n,
      ∫ X in unipFundamentalDomain K n r, ϕ (unipOne K n r X * x) ∂unipMeasure K n r = 0) :
    IsCuspidal (lift ϕ) := by
  intro r hr hrn g
  rw [← hϕ r hr hrn (retract g)]
  unfold constantTerm
  refine setIntegral_congr_fun (measurableSet_unipFundamentalDomain (K := K) (n := n) (r := r))
    fun X _ => ?_
  show ϕ (retract ((unipOne K n r X : AdelicGLn.AdelicGL K n) * g)) = _
  rw [retract_mul_left]

def openSubgroupOf (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    OpenSubgroup (AdelicGLn.FiniteAdelicGL K n) where
  toSubgroup := U.map (AdelicGLn.integralFiniteGL K n).subtype
  isOpen' := by
    change IsOpen ((U.map (AdelicGLn.integralFiniteGL K n).subtype : Subgroup _) :
      Set (AdelicGLn.FiniteAdelicGL K n))
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU

theorem lift_mul_finEmb {ϕ : normOneGL K n → ℂ} {U : Subgroup (AdelicGLn.integralFiniteGL K n)}
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (hϕ : ∀ u ∈ U, ∀ x, ϕ (x * finOne K n u) = ϕ x) (g : AdelicGLn.AdelicGL K n)
    (v : AdelicGLn.FiniteAdelicGL K n) (hv : v ∈ openSubgroupOf U hU) :
    lift ϕ (g * finEmb K n v) = lift ϕ g := by
  obtain ⟨u, hu, rfl⟩ := hv
  show ϕ (retract (g * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n))) = ϕ (retract g)
  rw [retract_mul_finEmb g u.2]
  exact hϕ u hu _

theorem uGL_mem_normOneGL (X : Pos n → 𝔸[K]) :
    (uGL X : AdelicGLn.AdelicGL K n) ∈ normOneGL K n := by
  have h1 : AdelicGLn.det K n (uGL X) = 1 :=
    Units.ext (by rw [AdelicGLn.coe_det, coe_uGL, det_uMat, Units.val_one])
  rw [mem_normOneGL, h1, map_one]
  rfl

def uOne (X : Pos n → 𝔸[K]) : normOneGL K n := ⟨uGL X, uGL_mem_normOneGL X⟩

@[simp] theorem coe_uOne (X : Pos n → 𝔸[K]) :
    (uOne X : AdelicGLn.AdelicGL K n) = uGL X := rfl

def whittakerOne (ϕ : normOneGL K n → ℂ) (x : normOneGL K n) : ℂ :=
  ∫ X in vecDomain K (Pos n), ϕ (uOne X * x) * (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ)
    ∂vecMeasure K (Pos n)

theorem whittaker_lift (ϕ : normOneGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    whittaker (lift ϕ) g = whittakerOne ϕ (retract g) := by
  unfold whittaker whittakerOne
  refine setIntegral_congr_fun measurableSet_vecDomain fun X _ => ?_
  show ϕ (retract ((uOne X : AdelicGLn.AdelicGL K n) * g)) * _ = _
  rw [retract_mul_left]

def IsSmoothTest (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) : Prop :=
  ∃ (ν : Measure (ArchUnits K n)) (_ : ν.IsHaarMeasure) (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (β : ArchMatrix K n → ℝ) (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ),
    f = archConv ν hβ.continuous hβc hβu (finAvg U hU g)

theorem IsSmoothTest.exists_finOne_mul {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    (hf : IsSmoothTest f) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (_ : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))),
      ∀ u ∈ U, ∀ x, f (finOne K n u * x) = f x := by
  obtain ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩ := hf
  refine ⟨U, hU, fun u hu x => ?_⟩
  rw [archConv_apply, archConv_apply]
  exact archConvFun_finOne_mul _ _ u (fun y => finAvgFun_finOne_mul U hU g ⟨u, hu⟩ y) x

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem rconv_mul_finOne {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    {u : AdelicGLn.integralFiniteGL K n} (hf : ∀ x, f (finOne K n u * x) = f x)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) :
    rconv Γ₁ μ f φ (x * finOne K n u) = rconv Γ₁ μ f φ x := by
  unfold rconv
  congr 1
  funext y
  rw [mul_inv_rev, mul_assoc, ← hf ((finOne K n u)⁻¹ * (x⁻¹ * y)), mul_inv_cancel_left]

theorem rconv_eq_zero_of_whittakerOne {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ)
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (hf : IsSmoothTest f)
    (h : ∀ x, whittakerOne (rconv Γ₁ μ f φ) x = 0) (x : normOneGL K n) :
    rconv Γ₁ μ f φ x = 0 := by
  obtain ⟨U, hU, hfU⟩ := hf.exists_finOne_mul
  have key := eq_zero_of_whittaker_eq_zero (ϕ := lift (rconv Γ₁ μ f φ))
    (continuous_lift (continuous_rconv Γ₁ μ f φ))
    (isLeftInvariant_lift fun γ hγ y => rconv_mul_left Γ₁ μ f φ hγ y)
    (isCuspidal_lift fun r hr hrn y => integral_rconv_unip_eq_zero μ f hφ hr hrn y)
    ⟨openSubgroupOf U hU, lift_mul_finEmb hU fun u hu y => rconv_mul_finOne μ (hfU u hu) φ y⟩
    (fun g => by rw [whittaker_lift]; exact h _)
  have := congrFun key (x : AdelicGLn.AdelicGL K n)
  rwa [lift_coe] at this

theorem integrated_eq_zero_of_rconv_eq_zero {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (h : ∀ x, rconv Γ₁ μ f φ x = 0) :
    (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ = 0 := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine (Lp.eq_zero_iff_ae_eq_zero).2 ?_
  filter_upwards [integrated_ae_eq_rconvQ Γ₁ μ f φ] with q hq
  rw [hq]
  obtain ⟨x, rfl⟩ := mk_surjective Γ₁ q
  rw [rconvQ_mk, h x]
  rfl

theorem exists_isSmoothTest_near (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ f : CompactlySupportedContinuousMap (normOneGL K n) ℂ,
      IsSmoothTest f ∧ ∫ x, ‖g x - f x‖ ∂μ ≤ ε := by
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ArchUnits K n), ν.IsHaarMeasure :=
    ⟨Measure.haar, inferInstance⟩
  obtain ⟨U, hU, β, hβ, hβc, hβu, -, hclose⟩ := exists_smooth_approx μ ν g hε
  exact ⟨_, ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩,
    le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)) hclose⟩

theorem _root_.GroundTheory.Automorphic.UnitaryRep.integrated_eq_zero_of_dense {G : Type*} [Group G]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (P : CompactlySupportedContinuousMap G ℂ → Prop)
    (hP : ∀ (g : CompactlySupportedContinuousMap G ℂ) (ε : ℝ), 0 < ε →
      ∃ f, P f ∧ ∫ x, ‖g x - f x‖ ∂ν ≤ ε)
    {v : H} (h : ∀ f, P f → π.integrated ν (UnitaryRep.ccToL1 ν f) v = 0)
    (g : CompactlySupportedContinuousMap G ℂ) : π.integrated ν (UnitaryRep.ccToL1 ν g) v = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  have hε' : 0 < ε / (‖v‖ + 1) := div_pos hε (by positivity)
  obtain ⟨f, hfs, hclose⟩ := hP g _ hε'
  have hf0 := h f hfs
  have hd := π.dist_integrated_ccToL1_le ν g f
  have hv1 : ‖v‖ / (‖v‖ + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [dist_eq_norm] at hd
  calc ‖π.integrated ν (UnitaryRep.ccToL1 ν g) v‖
      = ‖(π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)) v‖ := by
        rw [sub_apply, hf0, sub_zero]
    _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν g) - π.integrated ν (UnitaryRep.ccToL1 ν f)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ v
    _ ≤ (ε / (‖v‖ + 1)) * ‖v‖ := by gcongr; exact hd.trans hclose
    _ = ε * (‖v‖ / (‖v‖ + 1)) := by ring
    _ ≤ ε * 1 := by gcongr
    _ = 0 + ε := by ring

theorem eq_zero_of_forall_whittakerOne_rconv_eq_zero {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    (hφ : φ ∈ cuspidalL2 μ)
    (h : ∀ f, IsSmoothTest f → ∀ x, whittakerOne (rconv Γ₁ μ f φ) x = 0) : φ = 0 := by
  by_contra hne
  obtain ⟨g, hg⟩ := UnitaryRep.exists_integrated_ne_zero (rightRegularRep Γ₁ μ) μ hne
  exact hg (UnitaryRep.integrated_eq_zero_of_dense (rightRegularRep Γ₁ μ) μ IsSmoothTest
    (fun g ε hε => exists_isSmoothTest_near μ g hε) (fun f hf =>
      integrated_eq_zero_of_rconv_eq_zero μ (rconv_eq_zero_of_whittakerOne μ hφ hf (h f hf))) g)

end MultiplicityOne

end

end GroundTheory.Automorphic
