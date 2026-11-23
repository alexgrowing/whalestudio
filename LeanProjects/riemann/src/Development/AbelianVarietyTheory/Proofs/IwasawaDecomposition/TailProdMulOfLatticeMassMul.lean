import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem summable_abs_mul_sub_one {ι : Type} {a a' : ι → ℝ} (ha : Summable fun v => |a v - 1|)
    (ha' : Summable fun v => |a' v - 1|) : Summable fun v => |a v * a' v - 1| := by
  have h1 : Summable fun v => |a v - 1| * |a' v - 1| := by
    refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_)
      (ha.mul_right (∑' w, |a' w - 1|))
    exact mul_le_mul_of_nonneg_left (ha'.le_tsum v fun w _ => abs_nonneg _) (abs_nonneg _)
  refine Summable.of_nonneg_of_le (fun v => abs_nonneg _) (fun v => ?_) ((h1.add ha).add ha')
  have : a v * a' v - 1 = (a v - 1) * (a' v - 1) + (a v - 1) + (a' v - 1) := by ring
  rw [this, ← abs_mul]
  exact abs_add_three _ _ _

theorem multipliable_subtype_of_summable_abs {ι : Type} {a : ι → ℝ}
    (ha : Summable fun v => |a v - 1|) (p : ι → Prop) :
    Multipliable fun v : {v // p v} => a v.1 := by
  have h : Summable fun v : {v // p v} => (a v.1 - 1) :=
    (Summable.of_abs ha).comp_injective Subtype.val_injective
  have := Real.multipliable_one_add_of_summable h
  simpa using this

theorem tprod_nonneg_of_multipliable {ι : Type} {a : ι → ℝ} (ha : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v :=
  ge_of_tendsto' ha.hasProd fun _ => Finset.prod_nonneg fun v _ => h0 v

theorem tailProd_mul_of_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  intro F E _ _ _ _ _ d b n₁ M₁ n₂ M₂ n₃ M₃ mi mv mi' mv' Nv S₀ h h' hN
  refine ⟨?_, fun S hS => ?_⟩
  · refine (summable_abs_mul_sub_one h.2.2 h'.2.2).congr_cofinite ?_
    filter_upwards [S₀.eventually_cofinite_notMem] with v hv
    rw [hN v hv, ENNReal.toReal_mul]
  · have m := multipliable_subtype_of_summable_abs h.2.2 (fun v => v ∉ S)
    have m' := multipliable_subtype_of_summable_abs h'.2.2 (fun v => v ∉ S)
    unfold tailProd
    rw [← ENNReal.ofReal_mul (tprod_nonneg_of_multipliable m fun _ => ENNReal.toReal_nonneg),
      ← m.tprod_mul m']
    congr 1
    refine tprod_congr fun v => ?_
    rw [hN v.1 (fun hv => v.2 (hS hv)), ENNReal.toReal_mul]

end GlobalTheory.GaugeEx
