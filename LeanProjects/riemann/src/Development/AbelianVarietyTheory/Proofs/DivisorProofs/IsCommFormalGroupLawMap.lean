import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {d : ℕ} {τ : Type}

theorem map_powerSeriesEvalTwoGroups (c : MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    MvPowerSeries.map σ (at2 c u v) =
      at2 (MvPowerSeries.map σ c) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hu, hv])
  unfold at2
  rw [map_subst hs]
  congr 1
  funext s
  cases s <;> rfl

theorem constantCoeff_powerSeriesEvalTwoGroups_zero_of {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : constantCoeff c = 0) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    constantCoeff (at2 c u v) = 0 := by
  have h0 : ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hc

theorem map_op_of_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => MvPowerSeries.map σ (op μ u v i)) =
      op (fun i => MvPowerSeries.map σ (μ i)) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  funext i
  exact map_powerSeriesEvalTwoGroups σ (μ i) hu hv

theorem isLaw_map (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : IsLaw μ) :
    IsLaw (fun i => MvPowerSeries.map σ (μ i)) := by
  have hX : ∀ {κ : Type} (f : Fin d → κ), (fun i => MvPowerSeries.map σ
      (X (f i) : MvPowerSeries κ R)) = fun i => (X (f i) : MvPowerSeries κ S) := by
    intro κ f; funext i; exact map_X σ (f i)
  have hcX : ∀ {κ : Type} (f : Fin d → κ) (i : Fin d),
      constantCoeff (X (f i) : MvPowerSeries κ R) = 0 := fun f i => constantCoeff_X _
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d) R =>
      fun i => MvPowerSeries.map σ (w i)) h.unit
    rw [map_op_of_const σ μ (u := fun i => (X i : MvPowerSeries (Fin d) R)) (fun i => constantCoeff_X i)
      (fun _ => map_zero _)] at h1
    simpa only [map_X, map_zero] using h1
  · have h1 := congrArg (MvPowerSeries.map σ) (h.comm i)
    unfold swap at h1 ⊢
    rw [map_powerSeriesEvalTwoGroups σ (μ i) (hcX Sum.inr) (hcX Sum.inl)] at h1
    simpa only [map_X] using h1
  · have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have c12 : ∀ i, constantCoeff (op μ x1 x2 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx1 hx2
    have c23 : ∀ i, constantCoeff (op μ x2 x3 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx2 hx3
    have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
      fun i => MvPowerSeries.map σ (w i)) h.assoc
    rw [map_op_of_const σ μ c12 hx3, map_op_of_const σ μ hx1 c23,
      map_op_of_const σ μ hx1 hx2, map_op_of_const σ μ hx2 hx3] at h1
    have e1 : (fun i => MvPowerSeries.map σ (x1 (R := R) (d := d) i)) = x1 := hX _
    have e2 : (fun i => MvPowerSeries.map σ (x2 (R := R) (d := d) i)) = x2 := hX _
    have e3 : (fun i => MvPowerSeries.map σ (x3 (R := R) (d := d) i)) = x3 := hX _
    rwa [e1, e2, e3] at h1

end GlobalTheory.Katz
