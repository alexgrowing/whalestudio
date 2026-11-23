import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.MapLaw

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem hasSubst_elim {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun i => by cases i with
    | inl i => exact hu i
    | inr i => exact hv i

theorem constantCoeff_powerSeriesEvalTwoGroups_eq_zero {c : MvPowerSeries (Fin d ⊕ Fin d) R} (hc : constantCoeff c = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : constantCoeff (at2 c u v) = 0 := by
  unfold at2
  exact constantCoeff_subst_eq_zero (hasSubst_elim hu hv)
    (fun i => by cases i with
      | inl i => exact hu i
      | inr i => exact hv i) hc

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_elim hu hv)]
  congr 1
  funext i
  cases i <;> rfl

theorem map_op (r : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map r (op μ u v i) = op (fun j => map r (μ j)) (fun j => map r (u j)) (fun j => map r (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups r (μ i) hu hv

theorem constantCoeff_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 :=
  constantCoeff_powerSeriesEvalTwoGroups_eq_zero (hμ i) hu hv

end GlobalTheory.MapLaw

open GlobalTheory.MapLaw in
theorem GlobalTheory.isLaw_map_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {σ : Type} (i : σ), constantCoeff (X i : MvPowerSeries σ R) = 0 :=
    fun i => constantCoeff_X i
  have h0 : ∀ i : Fin d, constantCoeff (0 : MvPowerSeries (Fin d) R) = 0 := fun _ => map_zero _
  refine ⟨⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, ?_⟩
  · rw [constantCoeff_map, hμ.const i, map_zero]
  · funext i
    have := congrArg (map r) (congrFun hμ.unit i)
    rw [map_op r μ (fun j => hX j) h0] at this
    simpa [map_X] using this
  · have := congrArg (map r) (hμ.comm i)
    unfold swap at this ⊢
    rw [mvPowerSeriesMap_evalTwoGroups r (μ i) (fun j => hX _) (fun j => hX _)] at this
    simpa [map_X] using this
  · have hx1 : ∀ j, constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx2 : ∀ j, constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx3 : ∀ j, constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have m1 : (fun j => map r (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x1 := by
      funext j; simp [x1, map_X]
    have m2 : (fun j => map r (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x2 := by
      funext j; simp [x2, map_X]
    have m3 : (fun j => map r (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x3 := by
      funext j; simp [x3, map_X]
    funext i
    have := congrArg (map r) (congrFun hμ.assoc i)
    rw [map_op r μ (constantCoeff_op hμ.const hx1 hx2) hx3,
      map_op r μ hx1 (constantCoeff_op hμ.const hx2 hx3)] at this
    have e12 : (fun j => map r (op μ x1 x2 j)) = op (fun j => map r (μ j)) x1 x2 := by
      funext j; rw [map_op r μ hx1 hx2, m1, m2]
    have e23 : (fun j => map r (op μ x2 x3 j)) = op (fun j => map r (μ j)) x2 x3 := by
      funext j; rw [map_op r μ hx2 hx3, m2, m3]
    rw [e12, e23, m1, m3] at this
    exact this
  · intro n
    induction n with
    | zero => intro i; simp [nmul]
    | succ n ih =>
      intro i
      have hc : ∀ j, constantCoeff (nmul μ n j) = 0 := fun j => (ih j).1
      have e : ∀ (m : ℕ) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S), nmul ν (m + 1) =
          op ν (nmul ν m) (fun j => X j) := by
        intro m ν
        unfold nmul
        rw [Function.iterate_succ_apply']
      have e' : nmul μ (n + 1) = op μ (nmul μ n) (fun j => X j) := by
        unfold nmul
        rw [Function.iterate_succ_apply']
      rw [e', e]
      refine ⟨constantCoeff_op hμ.const hc (fun j => hX j) i, ?_⟩
      rw [map_op r μ hc (fun j => hX j)]
      have hn : (fun j => map r (nmul μ n j)) = nmul (fun i => map r (μ i)) n := funext fun j => (ih j).2
      rw [hn]
      simp only [map_X]
