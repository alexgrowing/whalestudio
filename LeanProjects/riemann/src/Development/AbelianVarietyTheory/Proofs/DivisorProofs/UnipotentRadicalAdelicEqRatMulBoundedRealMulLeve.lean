import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFiniteStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapCover

theorem unip_eq_rat_mul_inf_mul_fin : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (s : ℕ)
    (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E,
    ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧
    unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  intro E _ _ _ a s L hL
  have h0 : (unip (0 : BlockIx a s → Af E)) = 1 := by
    have h := unip_add (0 : BlockIx a s → Af E) 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hpre : (fun y : BlockIx a s → Af E => unip y) ⁻¹' L ∈ nhds (0 : BlockIx a s → Af E) := by
    apply JointCont.continuous_unip.continuousAt.preimage_mem_nhds
    rw [h0]; exact hL
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  have hU : (⋂ p, t p) ∈ nhds (0 : Af E) := Filter.iInter_mem.2 fun p => by simpa using ht p
  obtain ⟨R, hR, hx⟩ := GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite E (⋂ p, t p) hU
  refine ⟨R, hR, fun x => ?_⟩
  choose ξ hξ1 hξ2 using fun p => hx (x p)
  refine ⟨ξ, fun p => pInf E (x p - algebraMap E (Ad E) (ξ p)),
    unip (fun p => pFin E (x p - algebraMap E (Ad E) (ξ p))), ?_, ?_, ?_⟩
  · apply hsub
    intro p _
    exact Set.mem_iInter.1 (hξ2 p) p
  · exact (pi_norm_le_iff_of_nonneg hR).2 hξ1
  · have hsplit : x = (fun p => algebraMap E (Ad E) (ξ p)) + (fun p => x p - algebraMap E (Ad E) (ξ p)) := by
      funext p; simp
    conv_lhs => rw [hsplit, unip_add, unip_algebraMap,
      ← infGL_mul_finGL (unip (fun p => x p - algebraMap E (Ad E) (ξ p))), JointCont.map_unip, JointCont.map_unip]
    rw [mul_assoc]

end GlobalTheory.RapCover
