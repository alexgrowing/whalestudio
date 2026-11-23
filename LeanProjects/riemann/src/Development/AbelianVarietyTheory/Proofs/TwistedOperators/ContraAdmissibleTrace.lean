import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

namespace GlobalTheory.SmGL.ContraTrace

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]

def res (π : Representation ℂ G V) (K : Subgroup G) :
    fixed (contra π) K →ₗ[ℂ] Module.Dual ℂ (fixed π K) :=
  (fixed π K).subtype.dualMap ∘ₗ (smoothPart π.dual).subtype ∘ₗ (fixed (contra π) K).subtype

theorem res_apply (π : Representation ℂ G V) (K : Subgroup G) (l : fixed (contra π) K)
    (v : fixed π K) : res π K l v = (l.1 : Module.Dual ℂ V) v.1 := rfl

theorem invariant_of_fixed {π : Representation ℂ G V} {K : Subgroup G} (l : fixed (contra π) K)
    (h : G) (hh : h ∈ K) (w : V) : (l.1 : Module.Dual ℂ V) (π h w) = (l.1 : Module.Dual ℂ V) w := by
  have h1 := mem_fixed.1 l.2 h⁻¹ (inv_mem hh)
  conv_rhs => rw [← h1]
  rw [contra_apply, inv_inv]

theorem res_bijective [T2Space G] {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) : Function.Bijective (res π K) := by
  constructor
  · intro l l' h
    refine Subtype.ext (Subtype.ext ?_)
    exact IndDual.dual_ext hπ hK (invariant_of_fixed l) (invariant_of_fixed l')
      fun w hw => LinearMap.congr_fun h ⟨w, hw⟩
  · intro m
    obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend m
    obtain ⟨l, h1, h2⟩ := DualAverage.exists_invariant_form G V π hπ K hK l₀
    have h3 : ∀ g ∈ K, π.dual g l = l := fun g hg => LinearMap.ext fun w => h1 g⁻¹ (inv_mem hg) w
    refine ⟨⟨⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset (ho.mem_nhds (one_mem K)) h3)⟩,
      mem_fixed.2 fun g hg => Subtype.ext (h3 g hg)⟩, LinearMap.ext fun w => ?_⟩
    exact (h2 _ (mem_fixed.1 w.2)).trans (LinearMap.congr_fun hl₀ w)

theorem isAdmissible_contra [T2Space G] {π : Representation ℂ G V} (hπ : IsAdmissible π) :
    IsAdmissible (contra π) :=
  ⟨isSmooth_contra π, fun K ho hK =>
    haveI := hπ.2 K ho hK
    FiniteDimensional.of_injective (res π K) (res_bijective hπ.1 ho hK).1⟩

theorem smoothOp_contra [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] {π : Representation ℂ G V} (hπ : IsSmooth π)
    {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (l : smoothPart π.dual) (v : V) :
    (smoothOp (contra π) μ f l : Module.Dual ℂ V) v =
      (l : Module.Dual ℂ V) (smoothOp π μ (fun g => f g⁻¹) v) := by
  have h1 := (isSmooth_contra π).map_smoothOp (μ := μ) hf hc
    (Module.Dual.eval ℂ V v ∘ₗ (smoothPart π.dual).subtype) l
  have h2 := hπ.map_smoothOp (μ := μ) (f := fun g => f g⁻¹) (hf.comp_continuous continuous_inv)
    (hc.comp_homeomorph (Homeomorph.inv G)) (l : Module.Dual ℂ V) v
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [← integral_inv_eq_self]
  refine integral_congr_ae (.of_forall fun g => ?_)
  show f g⁻¹ • (l : Module.Dual ℂ V) (π g⁻¹⁻¹ v) = f g⁻¹ • (l : Module.Dual ℂ V) (π g v)
  rw [inv_inv]

theorem contra_admissible_trace : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ π hπ
  refine ⟨isAdmissible_contra hπ, fun f hf hc => ?_⟩
  have hf' : IsLocallyConstant fun g => f g⁻¹ := hf.comp_continuous continuous_inv
  have hc' : HasCompactSupport fun g => f g⁻¹ := hc.comp_homeomorph (Homeomorph.inv G)
  obtain ⟨K, ho, hK, hle⟩ := hG _ (Filter.inter_mem
    ((isOpen_leftStabilizer hf hc).mem_nhds (one_mem _))
    ((isOpen_leftStabilizer hf' hc').mem_nhds (one_mem _)))
  have := hπ.2 K ho hK
  have := (isAdmissible_contra hπ).2 K ho hK
  have m1 := (isSmooth_contra π).smoothOp_mem_fixed (μ := μ) hf hc (K := K) fun k hk => (hle hk).1
  have m2 := hπ.1.smoothOp_mem_fixed (μ := μ) hf' hc' (K := K) fun k hk => (hle hk).2
  let e := LinearEquiv.ofBijective _ (res_bijective hπ.1 ho hK)
  rw [smoothTrace, smoothTrace, finRankTrace_eq _ _ m1, finRankTrace_eq _ _ m2,
    ← LinearMap.trace_transpose' (M := fixed π K), ← LinearMap.trace_conj' _ e.symm]
  congr 1
  refine LinearMap.ext fun l => e.injective ?_
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
  exact LinearMap.ext fun v => smoothOp_contra μ hπ.1 hf hc l.1 v.1

end GlobalTheory.SmGL.ContraTrace
