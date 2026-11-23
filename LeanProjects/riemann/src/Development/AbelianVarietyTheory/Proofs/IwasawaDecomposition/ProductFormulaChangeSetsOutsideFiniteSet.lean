import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeSetChange

theorem abstract_change {ι X Z : Type} [Countable ι] {Y : ι → Type} [MeasurableSpace X]
    [MeasurableSpace Z] [∀ v, MeasurableSpace (Y v)] (ν : Measure X) (mi : Measure Z)
    (mv : ∀ v, Measure (Y v)) (p : X → Z) (q : ∀ v, X → Y v) (hq : ∀ v, Measurable (q v))
    (S T S' : Finset ι) (A L : ∀ v, Set (Y v)) (c : ℝ≥0∞)
    (hS' : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) (hA : ∀ v, MeasurableSet (A v))
    (hL : ∀ v ∉ S', A v = L v)
    (H : ∀ (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x in {x | ∀ v ∉ S', q v x ∈ L v}, fi (p x) * ∏ v ∈ S', fv v (q v x) ∂ν =
        (∫⁻ y, fi y ∂mi) * (∏ v ∈ S', ∫⁻ y, fv v y ∂(mv v)) * c)
    (fi : Z → ℝ≥0∞) (fv : ∀ v, Y v → ℝ≥0∞) (hfi : Measurable fi) (hfv : ∀ v, Measurable (fv v)) :
    ∫⁻ x in {x | ∀ v ∉ S, q v x ∈ A v}, fi (p x) * ∏ v ∈ S, fv v (q v x) ∂ν =
      (∫⁻ y, fi y ∂mi) * (∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * c) := by
  classical
  have hSeq : S' = S ∪ T := by
    ext v; rw [hS', Finset.mem_union]
  subst hSeq
  have hmeas : ∀ U : Finset ι, MeasurableSet {x | ∀ v ∉ U, q v x ∈ A v} := by
    intro U
    have : {x | ∀ v ∉ U, q v x ∈ A v} = ⋂ v, ⋂ (_ : v ∉ U), q v ⁻¹' A v := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hq v (hA v)
  let gv : ∀ v, Y v → ℝ≥0∞ := fun v => if v ∈ S then fv v else (A v).indicator 1
  have hgS : ∀ v ∈ S, gv v = fv v := fun v hv => if_pos hv
  have hgT : ∀ v ∈ T, gv v = (A v).indicator 1 := fun v hv =>
    if_neg (fun h => Finset.disjoint_left.mp hd h hv)
  have hgm : ∀ v, Measurable (gv v) := by
    intro v
    by_cases hv : v ∈ S
    · rw [hgS v hv]; exact hfv v
    · have : gv v = (A v).indicator 1 := if_neg hv
      rw [this]; exact measurable_one.indicator (hA v)
  have h1 := H fi gv hfi hgm
  have hset : {x | ∀ v ∉ S ∪ T, q v x ∈ L v} = {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := by
    ext x
    refine forall_congr' fun v => forall_congr' fun hv => ?_
    rw [hL v hv]
  rw [hset, Finset.prod_union hd, ← lintegral_indicator (hmeas _)] at h1
  have e1 : ∏ v ∈ S, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ S, ∫⁻ y, fv v y ∂(mv v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  have e2 : ∏ v ∈ T, ∫⁻ y, gv v y ∂(mv v) = ∏ v ∈ T, mv v (A v) :=
    Finset.prod_congr rfl fun v hv => by rw [hgT v hv]; exact lintegral_indicator_one (hA v)
  rw [e1, e2] at h1
  rw [← lintegral_indicator (hmeas _), ← mul_assoc, mul_assoc (∫⁻ y, fi y ∂mi), ← h1]
  refine lintegral_congr fun x => ?_
  have e3 : ∏ v ∈ S, gv v (q v x) = ∏ v ∈ S, fv v (q v x) :=
    Finset.prod_congr rfl fun v hv => by rw [hgS v hv]
  by_cases hx : x ∈ {x | ∀ v ∉ S, q v x ∈ A v}
  · have hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v} := fun v hv =>
      hx v fun h => hv (Finset.mem_union_left _ h)
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Finset.prod_union hd, e3]
    have : ∏ v ∈ T, gv v (q v x) = 1 := Finset.prod_eq_one fun v hv => by
      rw [hgT v hv, Set.indicator_of_mem (hx v fun h => Finset.disjoint_left.mp hd h hv)]
      rfl
    rw [this, mul_one]
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x ∈ {x | ∀ v ∉ S ∪ T, q v x ∈ A v}
    · rw [Set.indicator_of_mem hx', Finset.prod_union hd]
      simp only [Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, hvA⟩ := hx
      have hvT : v ∈ T := by
        by_contra h
        exact hvA (hx' v (by simp [hvS, h]))
      have : ∏ v ∈ T, gv v (q v x) = 0 := Finset.prod_eq_zero hvT (by
        rw [hgT v hvT, Set.indicator_of_notMem hvA])
      rw [this, mul_zero, mul_zero]
    · rw [Set.indicator_of_notMem hx']

theorem product_formula_change_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → (∀ v, MeasurableSet (A v)) → (∀ v ∉ S', A v = latV b v) → (∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S', projV v (projFin X) ∈ latV b v}, fi (projInf X) * ∏ v ∈ S', fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S', ∫⁻ Y, fv v Y ∂(mv v)) * tailProd b mv S') → ∀ (fi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (fv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable fi → (∀ v, Measurable (fv v)) → ∫⁻ X in {X | ∀ v ∉ S, projV v (projFin X) ∈ A v}, fi (projInf X) * ∏ v ∈ S, fv v (projV v (projFin X)) ∂ν = (∫⁻ Y, fi Y ∂mi) * (∏ v ∈ S, ∫⁻ Y, fv v Y ∂(mv v)) * ((∏ v ∈ T, mv v (A v)) * tailProd b mv S') := by
  intro F E _ _ _ _ _ d b n M ν mi mv S T S' A hS' hd hA hL H fi fv hfi hfv
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2.2
  exact abstract_change ν mi mv projInf (fun v X => projV v (projFin X))
    (fun v => (hc v).measurable) S T S' A (fun v => latV b v) _ hS' hd hA hL H fi fv hfi hfv

end GlobalTheory.GaugeSetChange
