import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstantOneNotCuspidalOfIsotropic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp
open GlobalTheory.Mem.Th GlobalTheory.Cusp.Model GlobalTheory.CuspDecay.Model
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.AutMult.Model

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [SFinite μ]
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

omit [μ.IsMulLeftInvariant] in

theorem ae_const {φ : G → ℂ} (hφ : AEStronglyMeasurable φ μ) (h : ∀ g, (fun x => φ (x * g)) =ᵐ[μ] φ) :
    ∃ c, φ =ᵐ[μ] fun _ => c := by
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU => ?_
  refine eventuallyConst_set.1 (aeconst_of_forall_preimage_smul_ae_eq Gᵐᵒᵖ (s := φ ⁻¹' U)
    (hφ.aemeasurable.nullMeasurable hU) fun g => ((h g.unop).mono fun x hx => ?_).set_eq)
  exact iff_of_eq (congrArg (· ∈ U) hx)

theorem exists_ae_eq_char {χ : G →* Circle} (hχ : Continuous χ) {F : L2 Γ μ} (h : ∀ g, R Γ μ g F = (χ g : ℂ) • F) :
    ∃ c : ℂ, lift Γ F =ᵐ[μ] fun x => c * χ x := by
  have hm : AEStronglyMeasurable (lift Γ F) μ := aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have hc : Continuous fun x => ((χ x⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp (hχ.comp continuous_inv)
  obtain ⟨c, hc⟩ := ae_const (φ := fun x => lift Γ F x * ((χ x⁻¹ : Circle) : ℂ)) (hm.mul hc.aestronglyMeasurable)
    fun g => by
      have e : lift Γ (((χ g : ℂ) • F : L2 Γ μ)) =ᵐ[μ] (χ g : ℂ) • lift Γ F :=
        ae_quotMeasure_iff.1 (Lp.coeFn_smul (χ g : ℂ) F)
      filter_upwards [lift_R g F, e] with x h1 h2
      rw [← h1, h g, h2]
      simp only [Pi.smul_apply, smul_eq_mul, mul_inv_rev, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
      field_simp
  refine ⟨c, hc.mono fun x hx => ?_⟩
  rw [← show _ = c from hx]
  simp

omit [SFinite μ] [μ.IsMulRightInvariant] in

theorem lift_smul (c : ℂ) {F : L2 Γ μ} {φ : G → ℂ} (e : lift Γ F =ᵐ[μ] φ) : lift Γ (c • F : L2 Γ μ) =ᵐ[μ] c • φ :=
  EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)

theorem multIn_char [NeZero μ] {χ : G →* Circle} (hχ : Continuous χ) (h : MemL2Quotient Γ μ fun x => (χ x : ℂ))
    (U : Submodule ℂ (L2 Γ μ)) :
    (h.toL2 ∈ U → multIn (charRep χ) (R Γ μ) U = 1) ∧ (h.toL2 ∉ U → multIn (charRep χ) (R Γ μ) U = 0) := by
  have hl := h.lift_toL2_ae_eq
  generalize h.toL2 = F₀ at hl
  have h0 : F₀ ≠ 0 := fun e => by
    have h2 : lift Γ (0 : L2 Γ μ) =ᵐ[μ] 0 := ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)
    obtain ⟨x, hx⟩ := (hl.symm.trans (show lift Γ F₀ =ᵐ[μ] 0 from e ▸ h2)).exists
    exact Circle.coe_ne_zero _ hx
  have key : ∀ T ∈ homIn (charRep χ) (R Γ μ) U, ∃ c : ℂ, T = c • ContinuousLinearMap.toSpanSingleton ℂ F₀ := by
    intro T hT
    obtain ⟨c, hc⟩ := exists_ae_eq_char (Γ := Γ) (μ := μ) hχ (F := T 1) fun g => by
      rw [← map_smul]; exact (hT.2 g 1).symm
    refine ⟨c, ContinuousLinearMap.ext_ring ?_⟩
    simpa using l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hc.trans (lift_smul c hl).symm)
  refine ⟨fun hU => ?_, fun hU => multIn_eq_zero_iff.2 (eq_bot_iff.2 fun T hT => ?_)⟩
  · have h1 : ContinuousLinearMap.toSpanSingleton ℂ F₀ ∈ homIn (charRep χ) (R Γ μ) U := ⟨fun c => U.smul_mem c hU,
      fun g c => by
        have : R Γ μ g F₀ = (χ g : ℂ) • F₀ := l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((lift_R g _).trans (EventuallyEq.trans
          ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hl)
          (EventuallyEq.trans (.of_forall fun x => by simp [mul_comm]) (lift_smul (χ g : ℂ) hl).symm)))
        change ((χ g : ℂ) * c) • F₀ = R Γ μ g (c • F₀)
        rw [map_smul, this, smul_smul, mul_comm]⟩
    have h2 : homIn (charRep χ) (R Γ μ) U = ℂ ∙ ContinuousLinearMap.toSpanSingleton ℂ F₀ :=
      le_antisymm (fun T hT => Submodule.mem_span_singleton.2 ((key T hT).imp fun _ => Eq.symm))
        ((Submodule.span_singleton_le_iff_mem _ _).2 h1)
    have h3 : ContinuousLinearMap.toSpanSingleton ℂ F₀ ≠ 0 := fun e => h0 (by simpa using DFunLike.congr_fun e 1)
    rw [multIn, h2, ← Module.finrank_eq_rank, finrank_span_singleton h3, Nat.cast_one]
  · obtain ⟨c, rfl⟩ := key T hT
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using U.smul_mem c⁻¹ (hT.1 1)) hU

theorem multIn_char_eq_zero [NeZero μ] {χ : G →* Circle} (hχ : Continuous χ) {γ : G} (hγ : γ ∈ Γ) (h : χ γ ≠ 1)
    (U : Submodule ℂ (L2 Γ μ)) : multIn (charRep χ) (R Γ μ) U = 0 := by
  refine multIn_eq_zero_iff.2 (eq_bot_iff.2 fun T hT => ?_)
  obtain ⟨c, hc⟩ := exists_ae_eq_char (Γ := Γ) (μ := μ) hχ (F := T 1) fun g => by
    rw [← map_smul]; exact (hT.2 g 1).symm
  have h1 := (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae hc
  obtain ⟨x, hx, hx'⟩ := (hc.and h1).exists
  have h2 : c * χ x = c * χ (γ * x) := hx.symm.trans ((leftInv_lift _ γ hγ x).symm.trans hx')
  have h3 : c = 0 := by
    by_contra hc0
    exact h (mul_eq_right.1 ((map_mul χ γ x).symm.trans (Circle.ext (mul_left_cancel₀ hc0 h2)).symm))
  have h4 : lift Γ (0 : L2 Γ μ) =ᵐ[μ] 0 := ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)
  exact ContinuousLinearMap.ext_ring
    (l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hc.trans (EventuallyEq.trans (.of_forall fun x => by simp [h3]) h4.symm)))

end General

theorem multTensor_one {G G₁ G₂ K : Type} [Group G] [Group G₁] [Group G₂] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (j₁ : G₁ →* G) (j₂ : G₂ →* G) (hj : ∀ g, ∃ a b, j₂ a * j₁ b = g) (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) :
    multTensor j₁ j₂ (Representation.trivial ℂ G₁ ℂ) (charRep 1) ρ U = multIn (charRep 1) ρ U := by
  refine LinearEquiv.rank_eq
    { toFun := fun T => ⟨T.1 1, (mem_homTensor.1 T.2).1 1, fun g x => ?_⟩
      invFun := fun S => ⟨LinearMap.toSpanSingleton ℂ _ S.1, mem_homTensor.2 ⟨fun w y => U.smul_mem w (S.2.1 y),
        fun g w y => ?_, fun g w y => ?_⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun T => Subtype.ext (LinearMap.ext_ring (one_smul _ _))
      right_inv := fun S => Subtype.ext (one_smul _ _) }
  · obtain ⟨a, b, rfl⟩ := hj g
    rw [map_mul ρ, mul_apply_eq_comp]
    exact ((mem_homTensor.1 T.2).2.2 a 1 x).trans (congrArg _ ((mem_homTensor.1 T.2).2.1 b 1 x))
  · have := S.2.2 (j₁ g) y
    change w • S.1 y = ρ (j₁ g) (w • S.1 y)
    rw [map_smul, ← this]
    exact congrArg (w • S.1 ·) (one_mul y).symm
  · change w • S.1 (charRep 1 (j₂ g) y) = ρ (j₂ g) (w • S.1 y)
    rw [map_smul, ← S.2.2 (j₂ g) y]

theorem multTensorPi_one_ne_zero {ι G G₁ K : Type} {Γ : ι → Type} [Fintype ι] [DecidableEq ι] [Group G] [Group G₁]
    [∀ i, Group (Γ i)] [NormedAddCommGroup K] [InnerProductSpace ℂ K] (j : G₁ →* G) (e : ∀ i, Γ i →* G)
    {ρ : G →* (K →L[ℂ] K)} {U : Submodule ℂ K} {F : K} (hd : F ∈ U) (hR : ∀ g, ρ g F = F) (h0 : F ≠ 0) :
    multTensorPi (Hs := fun _ => ℂ) j e (Representation.trivial ℂ G₁ ℂ) (fun _ => charRep 1) ρ U ≠ 0 := by
  rw [multTensorPi, Ne, Submodule.rank_eq_zero, ← Ne, Submodule.ne_bot_iff]
  refine ⟨LinearMap.toSpanSingleton ℂ _ (ContinuousMultilinearMap.mkPiRing ℂ _ F), mem_homTensorPi.2
    ⟨fun w y => U.smul_mem w (U.smul_mem _ hd), fun g w y => ?_, fun i g w y => ?_⟩, fun e => h0 ?_⟩
  · simp [hR]
  · have : charRep (1 : Γ i →* Circle) g (y i) = y i := one_mul _
    simp [hR, this]
  · simpa using DFunLike.congr_fun (DFunLike.congr_fun e 1) fun _ => 1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {χ : GA D V →* Circle}

omit [μ.IsMulRightInvariant] in

theorem memL2_automorphic_character (hχ : Continuous χ) (h : ∀ γ ∈ GQ V, χ γ = 1) : MemL2Quotient (GQ V) μ fun x => (χ x : ℂ) :=
  memL2_of_bounded_continuous_invariant (C := 1) (fun γ hγ g => by simp [h γ hγ]) (continuous_subtype_val.comp hχ) fun g => (Circle.norm_coe _).le

theorem mDisc_char_eq_one (hχ : Continuous χ) (h : ∀ γ ∈ GQ V, χ γ = 1) : mDisc V μ (charRep χ) = 1 :=
  (mDisc_eq_top (isIrrUnitary_charRep hχ)).trans ((multIn_char hχ (memL2_automorphic_character μ hχ h) ⊤).1 trivial)

theorem mDisc_char_eq_zero (hχ : Continuous χ) {γ : GA D V} (hγ : γ ∈ GQ V) (h : χ γ ≠ 1) :
    mDisc V μ (charRep χ) = 0 := multIn_char_eq_zero hχ hγ h _

theorem mDisc_one : mDisc V μ (charRep 1) = 1 := mDisc_char_eq_one μ continuous_const fun _ _ => rfl

theorem mCusp_one_of_aniso (h : wittIndex V = 0) : mCusp V μ (charRep 1) = 1 :=
  (multIn_char (χ := 1) continuous_const (memL2_const 1) _).1 ((constant_one_cuspidal_iff_anisotropic μ).2 h)

theorem mCusp_one_of_iso (h : 0 < wittIndex V) : mCusp V μ (charRep 1) = 0 :=
  (multIn_char (χ := 1) continuous_const (memL2_const 1) _).2 (constant_one_not_cuspidal_of_isotropic μ h)

theorem plane_disc_not_cusp (μ : Measure (GA D (plane D))) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    IsDiscreteRep (plane D) μ (charRep 1) ∧ ¬ IsCuspidalRep (plane D) μ (charRep 1) :=
  ⟨isDiscreteRep_one _ μ, fun h => h.2 (mCusp_one_of_iso μ (by rw [wittIndex_plane]; exact one_pos))⟩

theorem right_regular_constant_one (g : GA D V) : RG V μ g (constantOneDividedPowerChartLift V μ) = constantOneDividedPowerChartLift V μ := right_translate_toL2 (memL2_const 1) g

theorem mDiscT_one : mDiscT V μ (Representation.trivial ℂ (GfC V) ℂ) (charRep 1) = 1 :=
  (multTensor_one (GfC V).subtype (GinfC V).subtype (fun g => ⟨toInf V g, toFin V g, toInf_mul_toFin g⟩) _ _).trans (mDisc_one μ)

theorem mCuspT_one_of_aniso (h : wittIndex V = 0) : mCuspT V μ (Representation.trivial ℂ (GfC V) ℂ) (charRep 1) = 1 :=
  (multTensor_one (GfC V).subtype (GinfC V).subtype (fun g => ⟨toInf V g, toFin V g, toInf_mul_toFin g⟩) _ _).trans (mCusp_one_of_aniso μ h)

theorem mCuspT_one_of_iso (h : 0 < wittIndex V) : mCuspT V μ (Representation.trivial ℂ (GfC V) ℂ) (charRep 1) = 0 :=
  (multTensor_one (GfC V).subtype (GinfC V).subtype (fun g => ⟨toInf V g, toFin V g, toInf_mul_toFin g⟩) _ _).trans (mCusp_one_of_iso μ h)

theorem mDiscPi_one_ne_zero :
    mDiscPi V μ (Hs := fun _ => ℂ) (Representation.trivial ℂ (GfC V) ℂ) (fun _ => charRep 1) ≠ 0 := by
  classical
  exact multTensorPi_one_ne_zero _ _ (isIrredSubrep_const.le_disc (Submodule.mem_span_singleton_self _))
    (right_regular_constant_one μ) (constant_one_L2_ne_zero μ)

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

theorem finVec_one (θ : InfF D) (A : CptF V) : finVec V θ A (charRep 1) = ⊤ :=
  eq_top_iff.2 fun x _ => ⟨⟨⊤, inferInstance, fun _ _ => trivial⟩, by
    change IsOpen {g : GfC V | _ = x}
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun g => one_mul x⟩

def constEmb (θ : InfF D) (A : CptF V) : finVec V θ A (charRep 1) →ₗ[ℂ] (GA D V → ℂ) :=
  LinearMap.pi fun _ => (finVec V θ A (charRep 1)).subtype

theorem constEmb_mem (θ : InfF D) (A : CptF V) (h : wittIndex V = 0) : constEmb θ A ∈ formHom V θ A μ (charRep 1) := by
  refine ⟨fun x => ⟨⟨isAutFunSm_const θ V _, .of_invariant fun _ _ _ => rfl⟩, continuous_const, fun _ _ _ => rfl,
    fun r C hC => absurd hC (wittIndex_eq_zero_iff_isAniso.1 h r C)⟩,
    ContinuousLinearMap.toSpanSingleton ℂ (constantOneDividedPowerChartLift V μ), ⟨fun c => Submodule.smul_mem _ c ((constant_one_cuspidal_iff_anisotropic μ).2 h),
      fun g c => ?_⟩, fun x => ?_⟩
  · change ((1 : ℂ) * c) • constantOneDividedPowerChartLift V μ = RG V μ g (c • constantOneDividedPowerChartLift V μ)
    rw [map_smul, one_mul, right_regular_constant_one]
  · exact (lift_smul_ae (x : ℂ) (memL2_const 1).lift_toL2_ae_eq).trans (.of_forall fun _ => mul_one _)

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

theorem constEmb_ne_zero (θ : InfF D) (A : CptF V) : constEmb θ A ≠ 0 := fun e =>
  one_ne_zero (congrFun (DFunLike.congr_fun e ⟨1, finVec_one θ A ▸ Submodule.mem_top⟩) 1)

theorem beF_constEmb (θ : InfF D) (A : CptF V) (h : wittIndex V = 0) :
    beF μ (constEmb θ A) (constEmb θ A) = (autMeasure V μ).real Set.univ ∧
      beF μ (Complex.I • constEmb θ A) (constEmb θ A) = Complex.I * (autMeasure V μ).real Set.univ := by
  have h1 := petersson_eq_beF (isIrrUnitary_charRep continuous_const) (constEmb_mem μ θ A h) (constEmb_mem μ θ A h)
    ⟨1, finVec_one θ A ▸ Submodule.mem_top⟩ ⟨1, finVec_one θ A ▸ Submodule.mem_top⟩
  have h2 : beF μ (constEmb θ A) (constEmb θ A) = (autMeasure V μ).real Set.univ := by
    rw [Submodule.coe_inner] at h1
    have h3 : petersson V μ (fun _ => 1) (fun _ => 1) = (autMeasure V μ).real Set.univ := by
      simp [petersson, pet, AutomorphicL2Unitary.descend]
    simpa using h1.symm.trans h3
  exact ⟨h2, by rw [beF_smul_left, h2]⟩

theorem line_mCusp (μ : Measure (GA D (line D))) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    mCusp (line D) μ (charRep 1) = 1 := mCusp_one_of_aniso μ (wittIndex_line D)

theorem not_hasLocComp_one {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)} {ψ : Gv V v →* Circle}
    (h : ψ ≠ 1) : ¬ HasLocComp V v (charRep ψ) (charRep 1) := fun hc => by
  obtain ⟨T, hT, h0⟩ := (Submodule.ne_bot_iff _).1 (IsIsotypic.homIn_ne_bot hc)
  refine h (MonoidHom.ext fun g => Circle.ext ?_)
  have h1 : T ((ψ g : ℂ) • (1 : ℂ)) = 1 * T 1 := hT.2 g 1
  rw [map_smul] at h1
  exact mul_right_cancel₀ (fun e => h0 (ContinuousLinearMap.ext_ring e)) h1

theorem multIn_one_euclidean {G : Type} [Group G] (n : ℕ) :
    multIn (charRep 1) (1 : G →* (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) ⊤ = n := by
  have h : homIn (charRep 1) (1 : G →* (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) ⊤ = ⊤ :=
    eq_top_iff.2 fun T _ => mem_homIn_top.2 fun g x => congrArg T (one_mul x)
  rw [multIn, h, rank_top, ← LinearMap.toContinuousLinearMap.rank_eq, (LinearMap.ringLmapEquivSelf ℂ ℂ _).rank_eq,
    ← Module.finrank_eq_rank]
  simp

theorem not_isIrrUnitary_two {G : Type} [Group G] [TopologicalSpace G] :
    ¬ IsIrrUnitary (1 : G →* (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) := fun h => by
  have h1 := (uEquiv_of_multIn_ne_zero (isIrrUnitary_charRep (χ := 1) continuous_const) h
    (by rw [multIn_one_euclidean]; simp)).multIn_eq (ρ := (1 : G →* (EuclideanSpace ℂ (Fin 2) →L[ℂ] _))) (U := ⊤)
  rw [multIn_one_euclidean, multIn_self h] at h1
  exact absurd (show (2 : ℕ) = 1 by exact_mod_cast h1) (by decide)

end GlobalTheory.AutMult.Model

end
