import Mathlib
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory

theorem mulEquivHaarChar_heisenberg_chart (N A B : Type) [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
    (Ψ : A × B ≃ₜ N) (ω : A → A → B) (hω : Continuous (fun p : A × A => ω p.1 p.2))
    (hlaw : ∀ a b a' b', Ψ (a, b) * Ψ (a', b') = Ψ (a + a', b + b' + ω a a'))
    (φ : N ≃ₜ* N) (L₁ : A ≃ₜ+ A) (L₂ : B ≃ₜ+ B) (hφ : ∀ a b, φ (Ψ (a, b)) = Ψ (L₁ a, L₂ b)) :
    mulEquivHaarChar φ = addEquivAddHaarChar L₁ * addEquivAddHaarChar L₂ := by
  set μA : Measure A := Measure.addHaar
  set μB : Measure B := Measure.addHaar
  set ρ : Measure (A × B) := μA.prod μB
  have hΨm : Measurable Ψ := Ψ.continuous.measurable

  have hT : ∀ (a' : A) (b' : B),
      MeasurePreserving (fun p : A × B => (a' + p.1, b' + p.2 + ω a' p.1)) ρ ρ := by
    intro a' b'
    have h1 : Continuous (fun a : A => ω a' a) :=
      hω.comp (Continuous.prodMk continuous_const continuous_id)
    have hg : Measurable (Function.uncurry fun (a : A) (b : B) => b' + b + ω a' a) := by
      have : Continuous (fun p : A × B => b' + p.2 + ω a' p.1) :=
        (continuous_const.add continuous_snd).add (h1.comp continuous_fst)
      exact this.measurable
    refine (measurePreserving_add_left μA a').skew_product hg
      (Filter.Eventually.of_forall fun a => ?_)
    have : (fun b : B => b' + b + ω a' a) = fun b => (b' + ω a' a) + b := by
      funext b; abel
    rw [this]
    exact (measurePreserving_add_left μB _).map_eq
  set μ : Measure N := ρ.map Ψ
  have hinv : μ.IsMulLeftInvariant := by
    constructor
    intro g
    obtain ⟨⟨a', b'⟩, rfl⟩ := Ψ.surjective g
    have hcomp : (fun x => Ψ (a', b') * x) ∘ Ψ =
        Ψ ∘ (fun p : A × B => (a' + p.1, b' + p.2 + ω a' p.1)) := by
      funext p
      rcases p with ⟨a, b⟩
      exact hlaw a' b' a b
    change Measure.map (fun x => Ψ (a', b') * x) (ρ.map Ψ) = ρ.map Ψ
    rw [Measure.map_map (continuous_mul_left _).measurable hΨm, hcomp,
      ← Measure.map_map hΨm (hT a' b').measurable, (hT a' b').map_eq]
  haveI : IsFiniteMeasureOnCompacts μ := Measure.IsFiniteMeasureOnCompacts.map _ Ψ
  haveI : μ.IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
  haveI : μ.IsHaarMeasure := ⟨⟩
  haveI : μ.Regular := Measure.Regular.map Ψ

  have hchart : μ.map φ = ((μA.map L₁).prod (μB.map L₂)).map Ψ := by
    have hcomp : (φ : N → N) ∘ Ψ = Ψ ∘ Prod.map L₁ L₂ := by
      funext p
      rcases p with ⟨a, b⟩
      exact hφ a b
    change Measure.map φ (ρ.map Ψ) = _
    have hL₁ : Measurable (L₁ : A → A) := (map_continuous L₁).measurable
    have hL₂ : Measurable (L₂ : B → B) := (map_continuous L₂).measurable
    rw [Measure.map_map (map_continuous φ).measurable hΨm, hcomp,
      ← Measure.map_map hΨm (hL₁.prodMap hL₂), Measure.map_prod_map μA μB hL₁ hL₂]
  have h1 := addEquivAddHaarChar_smul_map μA L₁
  have h2 := addEquivAddHaarChar_smul_map μB L₂
  have h := mulEquivHaarChar_smul_map μ φ
  have hc : (addEquivAddHaarChar L₁ * addEquivAddHaarChar L₂) • μ.map φ = μ := by
    rw [hchart, ← Measure.map_smul, mul_smul, ← Measure.prod_smul_right,
      ← Measure.prod_smul_left, h1, h2]
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (1 : N)
  have hpos : (μ.map φ) K ≠ 0 := by
    haveI : (μ.map φ).IsHaarMeasure := φ.isHaarMeasure_map μ
    exact (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hfin : (μ.map φ) K ≠ ∞ := by
    haveI : (μ.map φ).IsHaarMeasure := φ.isHaarMeasure_map μ
    exact hK.measure_lt_top.ne
  have key := congrArg (fun m : Measure N => m K) (h.trans hc.symm)
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at key
  have := (ENNReal.mul_left_inj hpos hfin).1 key
  exact_mod_cast this

end GlobalTheory
