import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

section Abs

variable {G : Type} [Group G] [TopologicalSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def eigU (π : UnitaryRep G H) (J : Subgroup G) (χ : G → ℂ) : Submodule ℂ H :=
  ⨅ x ∈ J, LinearMap.eqLocus (π x : H →ₗ[ℂ] H) (χ x • LinearMap.id)

private lemma mem_eigU {π : UnitaryRep G H} {J : Subgroup G} {χ : G → ℂ} {v : H} :
    v ∈ eigU π J χ ↔ ∀ x ∈ J, π x v = χ x • v := by
  simp [eigU, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private lemma isClosed_eigU (π : UnitaryRep G H) (J : Subgroup G) (χ : G → ℂ) :
    IsClosed (eigU π J χ : Set H) := by
  have h : (eigU π J χ : Set H) = ⋂ x ∈ J, {v | π x v = χ x • v} := by
    ext v
    simp [mem_eigU]
  rw [h]
  exact isClosed_biInter fun x _ => isClosed_eq (π x).continuous (continuous_const_smul _)

private lemma conj_mul_chr {J : Subgroup G} {χ : G → ℂ} (hχ : IsChr J χ) {x : G} (hx : x ∈ J) :
    conj (χ x) * χ x = 1 := by
  rw [Complex.conj_mul', hχ.2.1 x hx]
  simp

variable [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

private def avg (π : UnitaryRep G H) (J : Subgroup G) (χ : G → ℂ) (m : Measure G) (v : H) : H :=
  ∫ g in (J : Set G), conj (χ g) • π g v ∂m

private lemma integrableOn_avg (π : UnitaryRep G H) {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (hχ : IsChr J χ)
    (m : Measure G) [m.IsHaarMeasure] (v : H) :
    IntegrableOn (fun g => conj (χ g) • π g v) (J : Set G) m := by
  have hc : Continuous fun g => conj (χ g) • π g v :=
    ((Complex.continuous_conj.comp hχ.1.continuous).smul (π.continuous_orbit v))
  exact hc.continuousOn.integrableOn_compact hJ.1

private lemma avg_mem (π : UnitaryRep G H) {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (hχ : IsChr J χ)
    (m : Measure G) [m.IsHaarMeasure] (v : H) : avg π J χ m v ∈ eigU π J χ := by
  rw [mem_eigU]
  intro y hy
  set f : G → H := fun g => conj (χ g) • π g v with hf
  have hint : IntegrableOn f (J : Set G) m := integrableOn_avg π hJ hχ m v
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  have h1 : ∫ g, (J : Set G).indicator f (y * g) ∂m = ∫ g, (J : Set G).indicator f g ∂m :=
    integral_mul_left_eq_self _ y
  have h2 : (fun g => (J : Set G).indicator f (y * g)) =
      (J : Set G).indicator fun g => (conj (χ y) • (π y)) (f g) := by
    funext g
    by_cases hg : g ∈ J
    · have hyg : y * g ∈ J := J.mul_mem hy hg
      rw [Set.indicator_of_mem (show y * g ∈ (J : Set G) from hyg),
        Set.indicator_of_mem (show g ∈ (J : Set G) from hg)]
      simp only [hf, hχ.2.2 y hy g hg, map_mul, UnitaryRep.map_mul_apply,
        ContinuousLinearMap.smul_apply, map_smul, smul_smul]
      rw [mul_comm]
    · have hyg : y * g ∉ J := fun h => hg (by simpa using J.mul_mem (J.inv_mem hy) h)
      rw [Set.indicator_of_notMem (show y * g ∉ (J : Set G) from hyg),
        Set.indicator_of_notMem (show g ∉ (J : Set G) from hg)]
  have h3 : avg π J χ m v = conj (χ y) • π y (avg π J χ m v) := by
    have e1 : avg π J χ m v = ∫ g, (J : Set G).indicator f g ∂m := (integral_indicator hmeas).symm
    have e2 : ∫ g, (J : Set G).indicator (fun g => (conj (χ y) • (π y)) (f g)) g ∂m =
        (conj (χ y) • (π y)) (avg π J χ m v) := by
      rw [integral_indicator hmeas]
      exact (conj (χ y) • (π y)).integral_comp_comm hint
    calc avg π J χ m v = ∫ g, (J : Set G).indicator f g ∂m := e1
      _ = ∫ g, (J : Set G).indicator f (y * g) ∂m := h1.symm
      _ = ∫ g, (J : Set G).indicator (fun g => (conj (χ y) • (π y)) (f g)) g ∂m :=
        congrArg (fun F : G → H => ∫ g, F g ∂m) h2
      _ = (conj (χ y) • (π y)) (avg π J χ m v) := e2
      _ = conj (χ y) • π y (avg π J χ m v) := rfl
  calc π y (avg π J χ m v) = (conj (χ y) * χ y) • π y (avg π J χ m v) := by
        rw [conj_mul_chr hχ hy, one_smul]
    _ = χ y • (conj (χ y) • π y (avg π J χ m v)) := by
        rw [smul_smul, mul_comm]
    _ = χ y • avg π J χ m v := by rw [← h3]

private lemma inner_avg (π : UnitaryRep G H) {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (hχ : IsChr J χ)
    (m : Measure G) [m.IsHaarMeasure] (hm : m J = 1) (v e : H) (he : e ∈ eigU π J χ) :
    ⟪e, avg π J χ m v⟫_ℂ = ⟪e, v⟫_ℂ := by
  have hint := integrableOn_avg π hJ hχ m v
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  rw [avg, ← integral_inner hint e]
  have : ∀ g ∈ (J : Set G), ⟪e, conj (χ g) • π g v⟫_ℂ = ⟪e, v⟫_ℂ := by
    intro g hg
    rw [← UnitaryRep.inner_map_map π g e v, mem_eigU.1 he g hg, inner_smul_left, inner_smul_right]
  rw [setIntegral_congr_fun hmeas this, setIntegral_const]
  simp [Measure.real, hm]

private lemma prj_eq_avg (π : UnitaryRep G H) {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (hχ : IsChr J χ)
    (m : Measure G) [m.IsHaarMeasure] (hm : m J = 1) (v : H) :
    prj (eigU π J χ) v = avg π J χ m v := by
  have hcl := (isClosed_eigU π J χ).submodule_topologicalClosure_eq
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [hcl]
    exact avg_mem π hJ hχ m v
  · intro e he
    rw [hcl] at he
    rw [← inner_conj_symm, inner_sub_right, inner_avg π hJ hχ m hm v e he, sub_self, map_zero]

private lemma commute_prj (π : UnitaryRep G H) {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (hχ : IsChr J χ)
    (m : Measure G) [m.IsHaarMeasure] (hm : m J = 1) (B : H →L[ℂ] H) (hB : ∀ x ∈ J, Commute B (π x)) :
    Commute B (prj (eigU π J χ)) := by
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  refine ContinuousLinearMap.ext fun v => ?_
  show B (prj (eigU π J χ) v) = prj (eigU π J χ) (B v)
  rw [prj_eq_avg π hJ hχ m hm, prj_eq_avg π hJ hχ m hm, avg, avg,
    ← B.integral_comp_comm (integrableOn_avg π hJ hχ m v)]
  refine setIntegral_congr_fun hmeas fun g hg => ?_
  have := congrArg (fun T : H →L[ℂ] H => T v) (hB g hg).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  simp [this]

private lemma oloc_abs (π : UnitaryRep G H) {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (hχ : IsChr J χ)
    (m : Measure G) [m.IsHaarMeasure] (hm : m J = 1) (u v : H) :
    ⟪u, prj (eigU π J χ) v⟫_ℂ = ∫ g, (J : Set G).indicator (fun x => conj (χ x)) g * ⟪u, π g v⟫_ℂ ∂m := by
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  have e : (fun g => (J : Set G).indicator (fun x => conj (χ x)) g * ⟪u, π g v⟫_ℂ) =
      (J : Set G).indicator fun g => ⟪u, conj (χ g) • π g v⟫_ℂ := by
    funext g
    by_cases hg : g ∈ (J : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [prj_eq_avg π hJ hχ m hm, avg, ← integral_inner (integrableOn_avg π hJ hχ m v) u, e,
    integral_indicator hmeas]

end Abs

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.eigBasic :
    UpperTheory.ConvolutionTheory.L1.EigBasic := by
  intro K _ _ n μ _ w J χ hJ hχ
  let φ : Gw n w →* normOneGL K n := (MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w)
  have hφ : Continuous φ := MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne K n) μ).compHom φ hφ
  have hπ : ∀ x, π x = rhoL μ w x := fun _ => rfl
  have hE : ∀ ψ : Gw n w → ℂ, eigL μ w J ψ = eigU π J ψ := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE]
    exact isClosed_eigU π J χ
  · ext v
    rw [hE, mem_eigU]
    simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]
    constructor
    · rintro h _ ⟨x, hx, rfl⟩
      simpa [hπ, rhoL] using h x hx
    · intro h x hx
      simpa [hπ, rhoL] using h _ ⟨x, hx, rfl⟩
  · intro _ _ m _ hm u v
    exact oloc_abs π hJ hχ m hm u v
  · intro B hB
    letI : MeasurableSpace (Gw n w) := borel _
    haveI : BorelSpace (Gw n w) := ⟨rfl⟩
    let K₀ : TopologicalSpace.PositiveCompacts (Gw n w) :=
      ⟨⟨J, hJ.1⟩, ⟨1, mem_interior_iff_mem_nhds.2 (hJ.2.mem_nhds J.one_mem)⟩⟩
    rw [hE]
    exact commute_prj π hJ hχ (Measure.haarMeasure K₀) (Measure.haarMeasure_self) B hB
