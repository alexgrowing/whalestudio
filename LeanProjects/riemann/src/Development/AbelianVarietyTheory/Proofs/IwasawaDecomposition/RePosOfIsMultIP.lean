import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurConst

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem left_cont_of_mem (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : T ∈ Mult θ M J χ) (v : M.Vec) :
    Continuous (T v) ∧ ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨(IsMultMap.aut hx v).cont, (IsMultMap.aut hx v).left⟩
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    refine ⟨hx.1.add hy.1, fun γ hγ g => ?_⟩
    show x v (γ * g) + y v (γ * g) = x v g + y v g
    rw [hx.2 γ hγ, hy.2 γ hγ]
  | smul a x _ hx =>
    refine ⟨hx.1.const_smul a, fun γ hγ g => ?_⟩
    show a • x v (γ * g) = a • x v g
    rw [hx.2 γ hγ]

theorem eq_zero_of_ae (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (φ : GA D V → ℂ) (hc : Continuous φ)
    (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (h2 : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0) : φ = 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ
  let t : Set (GA D V) := {g | φ g ≠ 0}
  have ht : IsOpen t := hc.isOpen_preimage _ isOpen_ne
  have htm : MeasurableSet t := ht.measurableSet
  have h3 : μ (t ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h2
  have hinv : ∀ γ : GQ V, γ • t = t := by
    intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0 ↔ φ g ≠ 0
    rw [hL _ (γ⁻¹).2]
  have h4 : μ t = 0 := hF.measure_zero_of_invariant t hinv h3
  have h5 : t = ∅ := (ht.measure_eq_zero_iff μ).1 h4
  funext g
  by_contra hg
  have : g ∈ t := hg
  rw [h5] at this
  exact this

theorem exists_vec (M : DSModel V S) (h : ∀ τ, M.sm τ ≠ ⊥) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  choose w hw hw0 using fun τ => (Submodule.ne_bot_iff _).1 (h τ)
  refine ⟨fun τ => ⟨w τ, hw τ⟩, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
  exact fun e => hw0 τ (inner_self_eq_zero.1 e)

theorem isMultiplicityInner_add_smul_right (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' T'' : MMap M)
    {a b : ℂ} (c : ℂ) (h : IsMultIP M μ 𝓕 T T' a) (h' : IsMultIP M μ 𝓕 T T'' b) :
    IsMultIP M μ 𝓕 T (T' + c • T'') (a + c * b) := by
  intro v v'
  have e : (fun g => star (T v g) * (T' + c • T'') v' g) =
      fun g => star (T v g) * T' v' g + c * (star (T v g) * T'' v' g) := by
    funext g
    show star (T v g) * (T' v' g + c * T'' v' g) = _
    ring
  have i2 : IntegrableOn (fun g => c * (star (T v g) * T'' v' g)) 𝓕 μ := (h' v v').1.const_mul c
  rw [e]
  refine ⟨(h v v').1.add i2, ?_⟩
  rw [integral_add (h v v').1 i2, integral_const_mul, (h v v').2, (h' v v').2]
  ring

theorem isMultiplicityInner_symm (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a : ℂ} (h : IsMultIP M μ 𝓕 T T' a) : IsMultIP M μ 𝓕 T' T (star a) := by
  intro v v'
  have e : (fun g => star (T' v g) * T v' g) = fun g => (starRingEnd ℂ) (star (T v' g) * T' v g) := by
    funext g
    rw [starRingEnd_apply, star_mul, star_star]
  rw [e]
  refine ⟨?_, ?_⟩
  · exact (Complex.conjCLE.toContinuousLinearMap.integrable_comp (h v' v).1 :)
  · rw [integral_conj, (h v' v).2, map_mul, map_prod]
    simp only [inner_conj_symm]
    rfl

theorem re_pos_of_isMultIP (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (T : MMap M) {a : ℂ} (h : IsMultIP M μ 𝓕 T T a) (v : M.Vec)
    (hc : Continuous (T v)) (hL : ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) (h0 : T v ≠ 0) : 0 < a.re := by
  obtain ⟨hi, he⟩ := h v v
  have e : (fun g => star (T v g) * T v g) = fun g => ((‖T v g‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [e] at hi he
  have hi' : IntegrableOn (fun g => ‖T v g‖ ^ 2) 𝓕 μ := by
    have := hi.re
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at this
    exact this
  rw [integral_complex_ofReal] at he
  have e2 : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = ((∏ τ, ‖(v τ : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [e2] at he
  have he' := congrArg Complex.re he
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at he'
  have hp : 0 ≤ ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := Finset.prod_nonneg fun τ _ => by positivity
  have hnn : 0 ≤ ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
  have hne : ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ ≠ 0 := by
    intro hz
    have := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi').1 hz
    refine h0 (eq_zero_of_ae μ 𝓕 hμ hF _ hc hL ?_)
    filter_upwards [this] with g hg
    simpa using hg
  have hpos : 0 < a.re * ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := he' ▸ lt_of_le_of_ne hnn hne.symm
  by_contra hn
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hp))

theorem ipM_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → (∀ τ, M.sm τ ≠ ⊥) → (∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ T'' ∈ Mult θ M J χ, ∀ c : ℂ, ipM M μ 𝓕 T (T' + c • T'') = ipM M μ 𝓕 T T' + c * ipM M μ 𝓕 T T'' ∧ ipM M μ 𝓕 T' T = star (ipM M μ 𝓕 T T')) ∧ ∀ T ∈ Mult θ M J χ, T ≠ 0 → 0 < (ipM M μ 𝓕 T T).re := by
  intro D θ V S M J χ μ 𝓕 hθ hμ hF hS hsm
  obtain ⟨v0, hv0⟩ := exists_vec M hsm
  have hs : ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, IsMultIP M μ 𝓕 T T' (ipM M μ 𝓕 T T') :=
    fun T hT T' hT' => ipM_spec M μ 𝓕 T T' (hS hθ hμ hF T hT T' hT')
  refine ⟨fun T hT T' hT' T'' hT'' c => ⟨?_, ?_⟩, fun T hT h0 => ?_⟩
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0
      (hs T hT _ (Submodule.add_mem _ hT' (Submodule.smul_mem _ c hT'')))
      (isMultiplicityInner_add_smul_right M μ 𝓕 T T' T'' c (hs T hT T' hT') (hs T hT T'' hT''))
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0 (hs T' hT' T hT) (isMultiplicityInner_symm M μ 𝓕 T T' (hs T hT T' hT'))
  · obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h0 (MultilinearMap.ext hn)
    have := left_cont_of_mem θ M J χ T hT v
    exact re_pos_of_isMultIP M μ 𝓕 hμ hF T (hs T hT T hT) v this.1 this.2 hv

end GlobalTheory.SchurConst
