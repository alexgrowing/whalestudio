import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspCompact

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

def cuspQuot {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ) :
    RightCosetSpace Γ₁ → ℂ :=
  Quotient.lift (fun y : Reduction.normOneGL K n => φ y) fun a b hab => by
    obtain ⟨γ, rfl⟩ := hab
    obtain ⟨γ', hγ'⟩ := Subgroup.mem_subgroupOf.1 γ.2
    change φ (((γ : Reduction.normOneGL K n) : AdelicGLn.AdelicGL K n) * b) = φ b
    rw [← hγ']
    exact hφ γ' b

@[simp] theorem cuspQuot_mk {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (y : Reduction.normOneGL K n) : cuspQuot hφ (mk Γ₁ y) = φ y := rfl

theorem continuous_cuspQuot {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (hc : Continuous φ) : Continuous (cuspQuot hφ) :=
  (isOpenQuotientMap_mk Γ₁).isQuotientMap.continuous_iff.2 (hc.comp continuous_subtype_val)

theorem cuspQuot_surj_eq {φ ψ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (hψ : IsLeftInvariant ψ) (h : ∀ y : Reduction.normOneGL K n, φ y = ψ y) :
    cuspQuot hφ = cuspQuot hψ := by
  funext q
  obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
  exact h y

variable (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]

theorem memLp_cuspQuot {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : φ ∈ cuspForms K n) :
    MemLp (cuspQuot hφ.1.isLeftInvariant) 2 (quotientMeasure Γ₁ μ) := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms hφ
  refine MemLp.of_bound (continuous_cuspQuot _ hφ.1.continuous).aestronglyMeasurable C
    (Eventually.of_forall fun q => ?_)
  obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
  exact hC y y.2

theorem toLp_mem_cuspidalL2 {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : φ ∈ cuspForms K n) :
    (memLp_cuspQuot μ hφ).toLp _ ∈ cuspidalL2 μ := by
  intro r hr hrn
  filter_upwards [ae_ctFun_congr μ r (MemLp.coeFn_toLp (memLp_cuspQuot μ hφ))] with y hy
  rw [constantTermL2, hy]
  exact hφ.2 r hr hrn y

def cuspToL2 : cuspForms K n →ₗ[ℂ] cuspidalL2 μ where
  toFun φ := ⟨(memLp_cuspQuot μ φ.2).toLp _, toLp_mem_cuspidalL2 μ φ.2⟩
  map_add' φ ψ := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_add]
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun q => by
      obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
      rfl)
  map_smul' c φ := by
    refine Subtype.ext ?_
    simp only [SetLike.val_smul, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun q => by
      obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
      rfl)

theorem coeFn_cuspToL2 (φ : cuspForms K n) :
    ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) =ᵐ[quotientMeasure Γ₁ μ]
      cuspQuot φ.2.1.isLeftInvariant :=
  MemLp.coeFn_toLp (memLp_cuspQuot μ φ.2)

theorem cuspToL2_eq_zero_iff (φ : cuspForms K n) :
    cuspToL2 μ φ = 0 ↔ ∀ x ∈ Reduction.normOneGL K n, (φ : AdelicGLn.AdelicGL K n → ℂ) x = 0 := by
  constructor
  · intro h x hx
    have h1 : cuspQuot φ.2.1.isLeftInvariant =ᵐ[quotientMeasure Γ₁ μ] 0 := by
      refine (coeFn_cuspToL2 μ φ).symm.trans ?_
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have h2 : (fun y : Reduction.normOneGL K n => (φ : AdelicGLn.AdelicGL K n → ℂ) y) =ᵐ[μ] 0 :=
      (quasiMeasurePreserving_mk Γ₁ μ).ae_eq h1
    have h3 := (Continuous.ae_eq_iff_eq μ (φ.2.1.continuous.comp continuous_subtype_val)
      continuous_const).1 h2
    exact congrFun h3 ⟨x, hx⟩
  · intro h
    refine Subtype.ext ?_
    rw [Submodule.coe_zero]
    refine Lp.ext ((coeFn_cuspToL2 μ φ).trans (EventuallyEq.trans ?_ (Lp.coeFn_zero _ _ _).symm))
    refine Eventually.of_forall fun q => ?_
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
    exact h y y.2

theorem exists_centralSection_mul_mem_normOneGL (x : AdelicGLn.AdelicGL K n) :
    ∃ (s : {r : ℝ // 0 < r}) (y : AdelicGLn.AdelicGL K n), y ∈ Reduction.normOneGL K n ∧
      x = Reduction.centralSection K n s * y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, x, ?_, by rw [map_one, one_mul]⟩
    rw [Reduction.mem_normOneGL_iff_detModule]
    have : AdelicGLn.det K 0 x = 1 := Units.ext (by rw [AdelicGLn.coe_det, Matrix.det_isEmpty]; rfl)
    rw [Reduction.detModule, MonoidHom.comp_apply, this, map_one]
  · set s := Reduction.detModule K n x
    refine ⟨s, (Reduction.centralSection K n s)⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
    rw [Reduction.mem_normOneGL_iff_detModule, map_mul, map_inv,
      Reduction.detModule_centralSection hn, inv_mul_cancel]

theorem injOn_cuspToL2 :
    Set.InjOn (cuspToL2 μ) {φ : cuspForms K n | ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x) =
        (φ : AdelicGLn.AdelicGL K n → ℂ) x} := by
  intro φ hφ ψ hψ h
  have h0 : cuspToL2 μ (φ - ψ) = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 h
  rw [cuspToL2_eq_zero_iff] at h0
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL x
  rw [hφ s y, hψ s y, ← sub_eq_zero]
  exact h0 y hy

theorem coe_cuspRep_apply (g : Reduction.normOneGL K n) (v : cuspidalL2 μ) :
    ((cuspRep μ g v : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) =
      RightCosetSpace.rightTranslate Γ₁ μ g (v : Lp ℂ 2 (quotientMeasure Γ₁ μ)) := rfl

theorem cuspToL2_rightTranslate (g : Reduction.normOneGL K n) (φ ψ : cuspForms K n)
    (hψ : (ψ : AdelicGLn.AdelicGL K n → ℂ) =
      Automorphic.rightTranslate (g : AdelicGLn.AdelicGL K n) (φ : AdelicGLn.AdelicGL K n → ℂ)) :
    cuspToL2 μ ψ = cuspRep μ g (cuspToL2 μ φ) := by
  refine Subtype.ext ?_
  rw [coe_cuspRep_apply]
  have h1 := (measurePreserving_rightMul μ g).quasiMeasurePreserving.ae_eq (coeFn_cuspToL2 μ φ)
  have h2 : cuspQuot ψ.2.1.isLeftInvariant =
      fun q => cuspQuot φ.2.1.isLeftInvariant (rightMul Γ₁ g q) := by
    funext q
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
    rw [rightMul_mk, cuspQuot_mk, cuspQuot_mk, hψ]
    rfl
  refine Lp.ext ((coeFn_cuspToL2 μ ψ).trans ?_)
  rw [h2]
  exact h1.symm.trans (coeFn_rightTranslate Γ₁ μ g _).symm

theorem finiteDimensional_span_cuspRep_maxCompact (φ : cuspForms K n) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRep μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ (cuspToL2 μ φ))) := by
  have hmem : ∀ k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
      Automorphic.rightTranslate (k : AdelicGLn.AdelicGL K n) (φ : AdelicGLn.AdelicGL K n → ℂ) ∈
        cuspForms K n :=
    fun k => ⟨φ.2.1.rightTranslate_of_mem_maxCompact k.2, φ.2.2.translate _⟩
  have hmap : (Submodule.span ℂ (Set.range fun k => (⟨_, hmem k⟩ : cuspForms K n))).map
      (cuspForms K n).subtype =
      Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        Automorphic.rightTranslate (k : AdelicGLn.AdelicGL K n) (φ : AdelicGLn.AdelicGL K n → ℂ)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
  have hfd : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k =>
      (⟨_, hmem k⟩ : cuspForms K n))).map (cuspForms K n).subtype) := by
    rw [hmap]
    exact φ.2.1.isKFinite
  have hW : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k =>
      (⟨_, hmem k⟩ : cuspForms K n))) :=
    LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ (cuspForms K n).injective_subtype _).symm
  have hle : Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRep μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ (cuspToL2 μ φ)) ≤
      (Submodule.span ℂ (Set.range fun k => (⟨_, hmem k⟩ : cuspForms K n))).map (cuspToL2 μ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨_, hmem k⟩, Submodule.subset_span ⟨k, rfl⟩,
      cuspToL2_rightTranslate μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ φ ⟨_, hmem k⟩ rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end CuspidalSpectrum

end

end GroundTheory.Automorphic
