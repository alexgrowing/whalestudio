import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.InfType

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def diagInf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : E →+* Cinf E :=
  (pInf E).comp (algebraMap E (Ad E))

theorem infDiag_eq (k : Eˣ) : infDiag k = infId E (Units.map (diagInf E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - infEq E 1 + infEq E ((infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

theorem denseRange_diagInf : DenseRange (diagInf E) := by
  have hc : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact (infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

theorem denseRange_units : DenseRange (Units.map (diagInf E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagInf.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

omit [NumberField E] [IsTotallyComplex E] in

theorem continuous_coord (τ : E →+* ℂ) : Continuous (coord τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

omit [NumberField E] [IsTotallyComplex E] in

theorem coord_expU (τ : E →+* ℂ) (x : Cinf E) : coord τ (expU x : (Cinf E)ˣ) = Complex.exp (coord τ x) := by
  unfold coord
  split_ifs
  · rfl
  · exact (Complex.exp_conj _).symm

omit [NumberField E] in

theorem conj_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))

omit [NumberField E] in
open Classical in

theorem coord_atEmb' (σ τ : E →+* ℂ) (z : ℂ) : coord σ (atEmb τ z) =
    (if σ = τ then z else 0) + (if σ = ComplexEmbedding.conjugate τ then starRingEnd ℂ z else 0) := by
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (conj_ne σ).symm, add_zero, coord_atEmb]
  by_cases h2 : σ = ComplexEmbedding.conjugate τ
  · subst h2
    rw [if_neg h1, if_pos rfl, zero_add]
    have := atEmb_conj τ (starRingEnd ℂ z)
    rw [Complex.conj_conj] at this
    rw [← this, coord_atEmb]
  · have h : InfinitePlace.mk σ ≠ InfinitePlace.mk τ := fun h => by
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · exact h2 (by rw [← h]; ext; simp)
    rw [if_neg h1, if_neg h2, add_zero]
    unfold coord atEmb
    by_cases h3 : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h3]; simp [h]
    · rw [if_neg h3]; simp [h]

theorem chiInf_eq (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ i, f i (coord (φ i) u) := by
  refine congrFun (denseRange_units.equalizer (g := fun u => ((chiInf χ u : ℂˣ) : ℂ))
    (h := fun u : (Cinf E)ˣ => ∏ i, f i (coord (φ i) u)) (Units.continuous_val.comp (continuous_chiInf χ))
    (continuous_finsetProd _ fun i _ => continuous_iff_continuousAt.2 fun v => ?_) (funext fun k => ?_)) u
  · exact ContinuousAt.comp (g := f i) (f := fun u : (Cinf E)ˣ => coord (φ i) u)
      (hf i _ (v.isUnit.map (coord (φ i))).ne_zero)
      ((continuous_coord (φ i)).comp Units.continuous_val).continuousAt
  · have e := h k
    simp only [← coord_algebraMap (φ _) (k : E)] at e
    rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq] at e
    exact e

open Classical in

theorem expo_eq_sum (χ : HChar E) {I : Type} [Fintype I] (φ : I → E →+* ℂ) (f : I → ℂ → ℂ) (a b : I → ℂ)
    (hf : ∀ i z, z ≠ 0 → ContinuousAt (f i) z)
    (he : ∀ i z, f i (Complex.exp z) = Complex.exp (a i * z + b i * starRingEnd ℂ z))
    (h : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, f i (φ i k)) (τ : E →+* ℂ) :
    expo χ τ = ∑ i, ((if φ i = τ then a i else 0) + (if φ i = ComplexEmbedding.conjugate τ then b i else 0)) := by
  refine expo_eq_of_exp χ τ _
    (∑ i, ((if φ i = τ then b i else 0) + (if φ i = ComplexEmbedding.conjugate τ then a i else 0))) fun z => ?_
  rw [chiInf_eq χ φ f hf h]
  simp only [coord_expU, he, coord_atEmb']
  rw [← Complex.exp_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  split_ifs <;> simp <;> ring

theorem expo_of_infType : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  intro E _ _ _ χ
  classical
  refine ⟨fun n h τ => ?_, fun s h τ => ?_, fun I _ φ n hφ h i => ?_⟩
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => z ^ n σ) (fun σ => n σ) (fun _ => 0)
      (fun σ z hz => continuousAt_zpow₀ z _ (Or.inl hz)) (fun σ z => by simp [Complex.exp_int_mul]) h τ]
    simp
  · rw [expo_eq_sum χ (fun σ => σ) (fun σ z => ((‖z‖ : ℝ) : ℂ) ^ (s : ℂ)) (fun _ => s / 2) (fun _ => s / 2)
      (fun σ z hz => ?_) (fun σ z => ?_) h.2.2 τ]
    · simp [Finset.sum_add_distrib]
    · refine ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_norm).continuousAt continuousAt_const ?_
      exact Complex.ofReal_mem_slitPlane.2 (norm_pos_iff.2 hz)
    · rw [← Complex.ofReal_cpow (norm_nonneg _), Complex.norm_exp, ← Real.exp_mul, Complex.ofReal_exp]
      congr 1
      rw [← mul_add, Complex.add_conj]
      push_cast
      ring
  · have key := expo_eq_sum χ φ (fun i z => (z / ((‖z‖ : ℝ) : ℂ)) ^ n i) (fun i => n i / 2) (fun i => -(n i : ℂ) / 2)
      (fun i z hz => ?_) (fun i z => ?_) h
    · have h1 : ∀ j, φ j = φ i ↔ j = i := fun j =>
        ⟨fun e => hφ (congrArg InfinitePlace.mk e), fun e => by rw [e]⟩
      have h2 : ∀ j, φ j ≠ ComplexEmbedding.conjugate (φ i) := fun j e => by
        have : j = i := hφ ((congrArg InfinitePlace.mk e).trans (InfinitePlace.mk_conjugate_eq _))
        subst this
        exact conj_ne _ e.symm
      have h3 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ i)) = φ i := by ext; simp
      rw [key, key]
      simp [h1, h2, h3]
    · have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
      exact (continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt hn).zpow₀ _
        (Or.inl (div_ne_zero hz hn))
    · rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub, ← Complex.exp_int_mul]
      congr 1
      have := Complex.add_conj z
      push_cast at this
      linear_combination ((n i : ℂ) / 2) * this

end GlobalTheory.CuspRep.InfType
