import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtRel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

open ProjFrameFibrePt in

theorem ProjFrameGenPtRel.proof : ProjFrameGenPtRel.Statement := by
  intro D Ω _ _ κ _ x e _ hF G
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have h1 : (C (n : ℤ) : MRing (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1))))) ∈ graphP x e := by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_C, eq_intCast, Int.cast_natCast]
      exact hn
    rw [graphP, graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (C : (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* MvPolynomial Unit _), C_eq_zero,
      ← map_natCast (Ideal.Quotient.mk (coordIdeal ℤ x)), Ideal.Quotient.eq_zero_iff_mem, coordIdeal,
      RingHom.mem_ker, map_natCast, ← map_natCast (Polynomial.C : Ω →+* Polynomial Ω), Polynomial.C_eq_zero] at h1
    exact_mod_cast h1
  ·
    have hker : ∀ h : MRing (GlobalTheory κ),
        aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) h = 0 ↔ h ∈ coordIdeal ℤ x := by
      intro h
      constructor
      · intro h0
        have h2 : rename (fun p : Ix κ => aV D p.2) h ∈ graphP x e := by
          rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker, aeval_rename]
          exact h0
        rwa [graphP, graphIdeal, RingHom.mem_ker, graphMap_rename_inl, C_eq_zero,
          Ideal.Quotient.eq_zero_iff_mem] at h2
      · intro hh
        exact aeval_inl_eq_zero G hh
    ext f
    have hu : f ∈ coordIdeal ℤ (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) ↔
        ∀ d, homogeneousComponent d f ∈ coordIdeal ℤ x := by
      rw [coordIdeal, RingHom.mem_ker, Polynomial.ext_iff]
      simp only [coeff_coneMap, Polynomial.coeff_zero, hker]
    rw [hu]
    constructor
    · intro h
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => h d
    · intro h d
      exact coordIdeal_isHomogIdeal ℤ x f h d
  ·
    intro k
    have h := x'_frame_mul G (e := e) k
    change G.x' (bV κ k) * G.x' (aV D (e 0).2) = G.x' (bV κ 0) * G.x' (aV D (e k).2)
    linear_combination -h
  ·
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_fieldRange] at hy
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨f, g, _, rfl⟩ := G.gen c
      have key : ∀ h : MRing (GlobalTheory (Fin (D + 1))), algebraMap G.Φ G.Φ' (aeval G.x h) ∈
          Subfield.closure (Set.range fun k : Fin (D + 1) => G.x' ⟨Sum.inr (), k⟩) := by
        intro h
        induction h using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, eq_intCast, map_intCast]
          exact intCast_mem _ a
        | add p q hp hq =>
          rw [map_add, map_add]
          exact add_mem hp hq
        | mul_X p i hp =>
          rw [map_mul, map_mul, aeval_X]
          exact mul_mem hp (Subfield.subset_closure ⟨i.2, G.compat i⟩)
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨G.x ⟨(), k⟩, (G.compat ⟨(), k⟩).symm⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
