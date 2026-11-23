import Mathlib
import Formalism.PeriodIntegrals.StdCharTR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInterAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IsOpenIntSub

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes InfinitePlace.Completion

namespace PI.StdCharTRWork

variable (F : Type) [Field F] [NumberField F]

def Lre : Ainf F →+ ℝ where
  toFun a := ∑ w : InfinitePlace F, (extensionEmbedding w (a w)).re
  map_zero' := by
    show ∑ w : InfinitePlace F, (extensionEmbedding w ((0 : ∀ v : InfinitePlace F, v.Completion) w)).re = 0
    simp
  map_add' a b :=
    (Finset.sum_congr rfl fun w _ => (congrArg Complex.re (map_add (extensionEmbedding w) (a w) (b w))).trans
      (Complex.add_re _ _)).trans Finset.sum_add_distrib

theorem continuous_Lre : Continuous (Lre F) := by
  show Continuous (fun a : Ainf F => ∑ w : InfinitePlace F, (extensionEmbedding w (a w)).re)
  exact continuous_finset_sum _ fun w _ =>
    Complex.continuous_re.comp ((isometry_extensionEmbedding w).continuous.comp (continuous_apply w))

theorem sum_embedding_eq_trace [IsTotallyReal F] (y : F) :
    ∑ v : InfinitePlace F, v.embedding y = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by
  have hreal : ∀ φ : F →+* ℂ, NumberField.ComplexEmbedding.IsReal φ := fun φ =>
    InfinitePlace.isReal_mk_iff.1 (NumberField.IsTotallyReal.isReal _)
  have e1 : ∀ φ : F →+* ℂ, (InfinitePlace.mk φ).embedding = φ := fun φ =>
    InfinitePlace.embedding_mk_eq_of_isReal (hreal φ)
  let eqv : (F →ₐ[ℚ] ℂ) ≃ InfinitePlace F :=
    { toFun := fun σ => InfinitePlace.mk σ.toRingHom
      invFun := fun w => w.embedding.toRatAlgHom
      left_inv := fun σ => by
        apply AlgHom.ext
        intro x
        simp [e1]
      right_inv := fun w => by simp [InfinitePlace.mk_embedding] }
  rw [trace_eq_sum_embeddings ℂ]
  exact (Fintype.sum_equiv eqv _ _ fun σ => by simp [eqv, e1]).symm

theorem Lre_algebraMap (b : F) :
    Lre F (algebraMap F (Ainf F) b) = (∑ v : InfinitePlace F, v.embedding b).re := by
  show ∑ w : InfinitePlace F, (extensionEmbedding w (algebraMap F (Ainf F) b w)).re = _
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  first
    | exact extensionEmbedding_coe w b
    | simp [InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe]

theorem Lre_int [IsTotallyReal F] (b : 𝓞 F) : ∃ n : ℤ, Lre F (algebraMap F (Ainf F) (b : F)) = n := by
  rw [Lre_algebraMap, sum_embedding_eq_trace]
  have hint : IsIntegral ℤ (Algebra.trace ℚ F (b : F)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe b)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, ?_⟩
  rw [← hn]
  simp

theorem exists_Lre_half [IsTotallyReal F] : ∃ t : Ainf F, Lre F t = 1 / 2 := by
  have hn : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  refine ⟨algebraMap F (Ainf F) ((1 : F) / (2 * (Fintype.card (InfinitePlace F) : F))), ?_⟩
  rw [Lre_algebraMap]
  simp only [map_div₀, map_one, map_mul, map_ofNat, map_natCast]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn' : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show ((Fintype.card (InfinitePlace F) : ℂ) * (1 / (2 * (Fintype.card (InfinitePlace F) : ℂ)))) = 1 / 2 by
    field_simp]
  norm_num

theorem stdCharTR_main : PI.StdCharTR.Target := by
  intro F _ _ hTR
  let mk1 : ℝ →+ AddCircle (1 : ℝ) := QuotientAddGroup.mk' _
  let g : AF F →+ AddCircle (1 : ℝ) := mk1.comp ((Lre F).comp (AddMonoidHom.fst (Ainf F) (Af F)))
  have hg : Continuous g :=
    (continuous_quotient_mk').comp ((continuous_Lre F).comp continuous_fst)
  let K : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range
  have hU : IsOpen (PI.GaugeCharW.intSub F : Set (AF F)) :=
    PI.GaugeCharW.isOpen_intSub F PI.GaugeCharW.openInt
  have hKU : ∀ x ∈ K, x ∈ PI.GaugeCharW.intSub F → g x = 0 := by
    rintro _ ⟨a, rfl⟩ hx
    have hx' : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
        sndA F (algebraMap F (AF F) a) v ∈ v.adicCompletionIntegers F := hx
    obtain ⟨b, hb⟩ := PI.GaugeCharW.intInter F a (fun v => hx' v)
    obtain ⟨n, hn⟩ := Lre_int F b
    show ((Lre F (algebraMap F (Ainf F) a) : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [← hb, hn]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples_iff.2 ⟨n, by simp⟩)
  obtain ⟨h, hcont, hK, hUeq⟩ := PI.GaugeCharW.extChar (AF F) K _ hU g hg hKU
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun x => ((AddCircle.toCircle (h x) : Circle) : ℂ)
      map_zero_eq_one' := by simp [AddCircle.toCircle_zero]
      map_add_eq_mul' := fun a b => by simp [map_add, AddCircle.toCircle_add] }
  have hψ : ∀ x, ψ x = ((AddCircle.toCircle (h x) : Circle) : ℂ) := fun _ => rfl
  have hpair : ∀ x : Ainf F, pairA F x 0 ∈ PI.GaugeCharW.intSub F := by
    intro x
    show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), sndA F (pairA F x 0) v ∈ v.adicCompletionIntegers F
    intro v
    have e : sndA F (pairA F x 0) = 0 := rfl
    rw [e]
    exact zero_mem _
  have hval : ∀ x : Ainf F, ψ (pairA F x 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Lre F x : ℝ) : ℂ)) := by
    intro x
    rw [hψ, hUeq _ (hpair x)]
    show ((AddCircle.toCircle ((Lre F x : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = _
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 1
    push_cast
    ring
  refine ⟨ψ, ⟨?_, ?_, ?_, ?_⟩, fun x => hval x⟩
  · exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hcont)
  · intro x
    rw [hψ]
    first
      | exact Circle.norm_coe _
      | exact Circle.abs_coe _
      | simp [Circle.norm_coe]
  · intro a
    have e : h (algebraMap F (AF F) a) = 0 := hK _ ⟨a, rfl⟩
    rw [hψ, e, AddCircle.toCircle_zero]
    rfl
  · obtain ⟨t, ht⟩ := exists_Lre_half F
    refine ⟨pairA F t 0, ?_⟩
    rw [hval, ht]
    have e : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring]
      exact Complex.exp_pi_mul_I
    rw [e]
    norm_num

end PI.StdCharTRWork
