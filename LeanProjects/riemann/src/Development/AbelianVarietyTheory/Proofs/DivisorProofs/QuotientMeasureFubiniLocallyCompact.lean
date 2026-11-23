import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MulEquivHaarCharEqOfChart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr

open MeasureTheory

namespace GlobalTheory.HeisChart

theorem mulEquivHaarChar_eq_mul_of_heisenberg_chart : ∀ (N V L : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N]
    [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [T2Space V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L] [LocallyCompactSpace L] [T2Space L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (χ : N ≃ₜ V × L) (ω : V → V → L), Continuous (fun p : V × V => ω p.1 p.2) →
    (∀ n₁ n₂ : N, χ (n₁ * n₂) = ((χ n₁).1 + (χ n₂).1, (χ n₁).2 + (χ n₂).2 + ω (χ n₁).1 (χ n₂).1)) →
    ∀ (φ : N ≃ₜ* N) (A : V ≃ₜ+ V) (Bl : L ≃ₜ+ L), (∀ n, χ (φ n) = (A (χ n).1, Bl (χ n).2)) →
      mulEquivHaarChar φ = addEquivAddHaarChar A * addEquivAddHaarChar Bl := by
  intro N V L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ χ ω hω hmul φ A Bl hφ
  set ν : Measure (V × L) := (Measure.addHaar : Measure V).prod (Measure.addHaar : Measure L) with hνdef
  have hνH : ν.IsAddHaarMeasure := by infer_instance
  have hνR : ν.Regular := by infer_instance
  set μ : Measure N := ν.map χ.symm with hμdef
  have hχm : Measurable χ := χ.continuous.measurable
  have hχsm : Measurable χ.symm := χ.symm.continuous.measurable
  have hinv : ∀ g : N, μ.map (g * ·) = μ := by
    intro g
    have hgm : Measurable (g * · : N → N) := (continuous_mul_left g).measurable
    set τ : V × L → V × L := fun p => ((χ g).1 + p.1, (χ g).2 + p.2 + ω (χ g).1 p.1) with hτ
    have hcomp : (g * · : N → N) ∘ χ.symm = χ.symm ∘ τ := by
      funext p
      apply χ.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply, hmul, hτ]
    have hfm : Measurable (fun v : V => ω (χ g).1 v) :=
      (hω.comp (Continuous.prodMk continuous_const continuous_id)).measurable
    have hshm : Measurable (fun p : V × L => (p.1, p.2 + ω (χ g).1 p.1)) :=
      measurable_fst.prodMk (measurable_snd.add (hfm.comp measurable_fst))
    have hsh : ν.map (fun p : V × L => (p.1, p.2 + ω (χ g).1 p.1)) = ν :=
      PI.IwaMeasEx.MG.shear_map _ _ (fun v => ω (χ g).1 v) hfm
    have htr : ν.map (fun p : V × L => χ g + p) = ν := map_add_left_eq_self ν (χ g)
    have hτeq : τ = (fun p : V × L => χ g + p) ∘ (fun p : V × L => (p.1, p.2 + ω (χ g).1 p.1)) := by
      funext p
      simp only [hτ, Function.comp_apply, Prod.mk_add_mk]
      congr 1
      abel
    have hτν : ν.map τ = ν := by
      rw [hτeq, ← Measure.map_map (measurable_const_add _) hshm, hsh, htr]
    have hτm : Measurable τ := by
      rw [hτeq]
      exact (measurable_const_add _).comp hshm
    rw [hμdef, Measure.map_map hgm hχsm, hcomp, ← Measure.map_map hχsm hτm, hτν]
  have hμH : μ.IsHaarMeasure := by
    have h1 : IsFiniteMeasureOnCompacts μ := by
      rw [hμdef]; exact Measure.IsFiniteMeasureOnCompacts.map ν χ.symm
    have h2 : μ.IsOpenPosMeasure := by
      rw [hμdef]
      exact χ.symm.continuous.isOpenPosMeasure_map χ.symm.surjective
    have h3 : μ.IsMulLeftInvariant := ⟨hinv⟩
    exact { }
  have hμR : μ.Regular := by infer_instance
  have hμχ : μ.map χ = ν := by
    rw [hμdef, Measure.map_map hχm hχsm]
    simp
  have key := PI.IwaMeasEx.MG.mulEquivHaarChar_eq_of_chart μ ν χ hχm hμχ φ (GlobalTheory.ModuLR.prodCE A Bl)
    (fun n => by rw [GlobalTheory.ModuLR.prodCE_apply]; exact hφ n)
  rw [key, GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE]

end GlobalTheory.HeisChart
