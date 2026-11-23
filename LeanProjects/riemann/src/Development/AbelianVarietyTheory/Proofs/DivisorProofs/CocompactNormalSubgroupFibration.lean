import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdHomeoSymmApplySnd

open MeasureTheory

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem isHaarMeasure_map_prodHomeo : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  intro G _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ _ _ s π hs hsc hπc hπmul hπs hker hsmul μ hμ
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he_def
  set P : Measure (N' × V) := (Measure.haar : Measure N').prod μ with hP
  set ν : Measure N := P.map e with hν
  haveI := hc'.isMulRightInvariant (Measure.haar : Measure N')
  have hem : Measurable e := e.continuous.measurable
  haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map P e
  haveI : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective

  haveI hR : ν.IsMulRightInvariant := ⟨fun n₀ => by
    set z₀ := e.symm n₀
    have hz₀ : ((n₀ : N) : G) = (z₀.1 : G) * s z₀.2 := by
      rw [← prodHomeo_apply hle hs hsc hπc hπmul hπs hker z₀]; simp [z₀, e]
    let c : V → N' := fun v => ⟨s v * z₀.1 * (s v)⁻¹, hn _ (hs v) _ z₀.1.2⟩
    have hcc : Continuous c := by fun_prop
    let T' : V × N' → V × N' := fun p => (p.1 + z₀.2, p.2 * c p.1)
    have hT' : MeasurePreserving T' (μ.prod (Measure.haar : Measure N')) (μ.prod (Measure.haar : Measure N')) :=
      (measurePreserving_add_right μ z₀.2).skew_product (g := fun v m => m * c v)
        (by apply Continuous.measurable; fun_prop)
        (.of_forall fun v => map_mul_right_eq_self _ _)
    have hT : MeasurePreserving (Prod.swap ∘ T' ∘ Prod.swap) P P :=
      Measure.measurePreserving_swap.comp (hT'.comp Measure.measurePreserving_swap)
    have hcomm : (fun n => n * n₀) ∘ e = e ∘ (Prod.swap ∘ T' ∘ Prod.swap) := by
      funext ⟨m, v⟩
      apply Subtype.ext
      change ((m : G) * s v) * (n₀ : G) = ((m * c v : N') : G) * s (v + z₀.2)
      rw [hz₀, hsmul, Subgroup.coe_mul]
      change _ = (m : G) * (s v * (z₀.1 : G) * (s v)⁻¹) * (s v * s z₀.2)
      group
    rw [hν, Measure.map_map (measurable_mul_const n₀) hem, hcomm, ← Measure.map_map hem hT.measurable, hT.map_eq]⟩
  haveI : IsFiniteMeasureOnCompacts ν.inv := Measure.IsFiniteMeasureOnCompacts.map ν (Homeomorph.inv N)
  haveI : ν.inv.IsOpenPosMeasure := (Homeomorph.inv N).continuous.isOpenPosMeasure_map (Homeomorph.inv N).surjective
  haveI : ν.inv.IsHaarMeasure := {}
  haveI := hc.isMulRightInvariant ν.inv
  have hL : ν.IsMulLeftInvariant := by rw [← Measure.inv_inv ν]; infer_instance
  exact {}

end GlobalTheory.Cusp.Shear

end
