import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdScale

theorem finite_mulSupport_sub {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (p : ι → Prop) : (Function.mulSupport fun v : {v // p v} => (r v.1 : ℝ)).Finite := by
  refine (hr.preimage (f := (Subtype.val : {v // p v} → ι)) Subtype.val_injective.injOn).subset ?_
  intro v hv h
  exact hv (by simp [h])

theorem summable_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) : Summable fun v => |r v * f v - 1| := by
  refine hf.congr_cofinite ?_
  filter_upwards [hr.compl_mem_cofinite] with v hv
  have : r v = 1 := by simpa using hv
  simp [this]

theorem finprod_eq {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ((∏ᶠ v, r v : ℝ≥0) : ℝ) = (∏ v ∈ S, (r v : ℝ)) * ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : (Function.mulSupport fun v => (r v : ℝ)).Finite :=
    hr.subset fun v hv h => hv (by simp [h])
  have h1 : ((∏ᶠ v, r v : ℝ≥0) : ℝ) = ∏ᶠ v, (r v : ℝ) :=
    NNReal.toRealHom.toMonoidHom.map_finprod hr
  rw [h1, ← tprod_eq_finprod (L := SummationFilter.unconditional ι) h0, ← Finset.tprod_subtype' S (fun v => (r v : ℝ))]
  exact (Multipliable.tprod_mul_tprod_compl (f := fun v => (r v : ℝ)) (s := (S : Set ι))
    (multipliable_of_finite_mulSupport (finite_mulSupport_sub r hr _))
    (multipliable_of_finite_mulSupport (finite_mulSupport_sub r hr _))).symm

theorem tprod_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ∏' v : {v // v ∉ S}, ((r v.1 : ℝ) * f v.1) =
      (∏' v : {v // v ∉ S}, (r v.1 : ℝ)) * ∏' v : {v // v ∉ S}, f v.1 := by
  refine Multipliable.tprod_mul
    (multipliable_of_finite_mulSupport (finite_mulSupport_sub r hr _)) ?_
  have h := multipliable_one_add_of_summable (f := fun v : {v // v ∉ S} => f v.1 - 1)
    (hf.subtype {v | v ∉ S})
  simpa using h

theorem finprod_ennreal {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (S : Finset ι) :
    ∃ c : ℝ≥0, (∏ᶠ v, r v) = (∏ v ∈ S, r v) * c ∧ (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
    rw [tprod_eq_finprod (finite_mulSupport_sub r hr _)]
    exact finprod_nonneg fun v => (r v.1).2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := ⟨⟨_, h0⟩, rfl⟩
  refine ⟨c, ?_, hc⟩
  apply NNReal.coe_injective
  rw [finprod_eq r hr S, ← hc]
  simp

theorem isProd_smul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0)
    (r : HeightOneSpectrum (𝓞 F) → ℝ≥0) (h : IsProd b ν mi mv)
    (hr : (Function.mulSupport r).Finite) :
    IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  obtain ⟨⟨hi, hv, hs⟩, hf⟩ := h
  have key : ∀ v, ((r v • mv v) (latV b v)).toReal = r v * (mv v (latV b v)).toReal := by
    intro v
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  refine ⟨⟨inferInstance, fun v => inferInstance, ?_⟩, ?_⟩
  · simp only [key]
    exact summable_scale _ r hs hr
  · intro S fi fv hfi hfv
    obtain ⟨c, hc, hc'⟩ := finprod_ennreal r hr S
    have ht : tailProd b (fun v => r v • mv v) S = c * tailProd b mv S := by
      unfold tailProd
      simp only [key]
      rw [tprod_scale (fun v => (mv v (latV b v)).toReal) r hs hr S, ← hc',
        ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [Measure.restrict_smul, lintegral_smul_measure, hf S fi fv hfi hfv, ht, hc]
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
    push_cast
    ring

end GlobalTheory.GaugeEx.ProdScale
