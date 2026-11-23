import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubInStatement

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace CobSymCoc

open GlobalTheory.Katz.CobCob

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (elim_has hu hv)]
  congr 1
  funext k
  cases k <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map φ (op μ u v i) = op (fun j => map φ (μ j)) (fun j => map φ (u j)) (fun j => map φ (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem map_threeGroupsFirstVariables (φ : R →+* S) : (fun j => map φ (x1 (R := R) (d := d) j)) = x1 := by
  funext j; exact map_X φ _
theorem map_threeGroupsSecondVariables (φ : R →+* S) : (fun j => map φ (x2 (R := R) (d := d) j)) = x2 := by
  funext j; exact map_X φ _
theorem map_threeGroupsThirdVariables (φ : R →+* S) : (fun j => map φ (x3 (R := R) (d := d) j)) = x3 := by
  funext j; exact map_X φ _

theorem map_assocL (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ x1 (op μ x2 x3) i)) =
      op (fun j => map φ (μ j)) x1 (op (fun j => map φ (μ j)) x2 x3) := by
  funext i
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables (op_const h constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables), map_threeGroupsFirstVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem map_assocR (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ (op μ x1 x2) x3 i)) =
      op (fun j => map φ (μ j)) (op (fun j => map φ (μ j)) x1 x2) x3 := by
  funext i
  rw [map_op φ μ (op_const h constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables, map_threeGroupsThirdVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables]

end CobSymCoc

open CobSymCoc CobCob in

theorem cob_symCoc_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL N f hf
  have hM : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, constantCoeff_map, hL.const i, map_zero]
  obtain ⟨A, Bs, -⟩ := formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hM f
  refine ⟨?_, ?_⟩
  · rw [A]
    have eL : op (up Q μ) x1 (op (up Q μ) x2 x3) = up Q (op μ x1 (op μ x2 x3)) :=
      (map_assocL (algebraMap B Q) μ hL.const).symm
    have eR : op (up Q μ) (op (up Q μ) x1 x2) x3 = up Q (op μ (op μ x1 x2) x3) :=
      (map_assocR (algebraMap B Q) μ hL.const).symm
    rw [eL, eR]
    refine GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p B O Q θ hF (RingHom.ker θ) ?_ (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) N f _ _ hf
      (op_const hL.const constantCoeff_threeGroupsFirstVariables (op_const hL.const constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables))
      (op_const hL.const (op_const hL.const constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables) ?_
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
      exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
    · intro i α
      rw [RingHom.mem_ker, ← coeff_map, map_sub]
      have h1 := congrFun (map_assocL θ μ hL.const) i
      have h2 := congrFun (map_assocR θ μ hL.const) i
      rw [h1, h2, hL.law.assoc, sub_self, map_zero]
  · have hs : (fun i => swap (up Q μ i)) = up Q μ := by
      funext i
      have e : map (algebraMap B Q) (swap (μ i)) = swap (map (algebraMap B Q) (μ i)) := by
        unfold swap
        rw [mvPowerSeriesMap_evalTwoGroups (algebraMap B Q) (μ i) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
        simp only [map_X]
      show swap (map (algebraMap B Q) (μ i)) = map (algebraMap B Q) (μ i)
      rw [← e, hL.comm i]
    rw [hs, sub_self] at Bs
    exact sub_eq_zero.1 Bs

end GlobalTheory
