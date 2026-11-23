import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

namespace Katz

namespace CoefChange

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun j => by
    cases j with
    | inl i => exact hu i
    | inr i => exact hv i))]
  congr 1
  funext j
  cases j <;> rfl

theorem map_subst' (r : R →+* S) {σ : Type} [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    map r (subst a f) = subst (fun i => map r (a i)) (map r f) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero ha)]

theorem map_inL (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inL f) = inL (map r f) := by
  unfold inL
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem map_inR (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inR f) = inR (map r f) := by
  unfold inR
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem inL_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inL f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

theorem inR_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inR f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

end CoefChange

open CoefChange in

theorem map_cob_swap_pull : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {τ : Type} (i : τ), constantCoeff (X i : MvPowerSeries τ R) = 0 :=
    fun i => constantCoeff_X i
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    unfold op at2
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i)) (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i) (hμ i)
  have mapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (fun i => map r (op μ u v i)) =
        op (fun i => map r (μ i)) (fun i => map r (u i)) (fun i => map r (v i)) := by
    intro u v hu hv
    funext i
    exact mvPowerSeriesMap_evalTwoGroups r (μ i) u v hu hv
  have mx1 : (fun i => map r ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x1 := by
    funext i; exact map_X r _
  have mx2 : (fun i => map r ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x2 := by
    funext i; exact map_X r _
  have mx3 : (fun i => map r ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x3 := by
    funext i; exact map_X r _
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold cob1
    rw [map_sub, map_sub, map_subst' r μ hμ, map_inL, map_inR]
  · intro c
    unfold cob2
    rw [map_sub, map_add, map_sub, mvPowerSeriesMap_evalTwoGroups r c _ _ h2 h3, mvPowerSeriesMap_evalTwoGroups r c _ _ (hop _ _ h1 h2) h3,
      mvPowerSeriesMap_evalTwoGroups r c _ _ h1 (hop _ _ h2 h3), mvPowerSeriesMap_evalTwoGroups r c _ _ h1 h2, mapop _ _ h1 h2,
      mapop _ _ h2 h3, mx1, mx2, mx3]
  · intro c
    unfold Katz.swap
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun _ => hX _) (fun _ => hX _)]
    congr 1 <;> funext i <;> exact map_X r _
  · intro f
    funext i
    unfold lin
    rw [coeff_map]
  · intro φ hφ
    refine ⟨?_, fun f => map_subst' r φ hφ f⟩
    intro c
    unfold pull2
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i))]
    congr 1 <;> funext i
    · exact map_inL r (φ i)
    · exact map_inR r (φ i)

end Katz

end GlobalTheory
