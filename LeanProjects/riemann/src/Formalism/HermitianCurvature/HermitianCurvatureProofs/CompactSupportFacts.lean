import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt

noncomputable section

theorem compact_support_facts : TL.CptFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs F hF
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  refine ⟨⟨ε, hε, ?_⟩, fun Dop hDop => ?_⟩
  · set R' : ℝ := |R| + 1 with hR'
    have hR0 : 0 < R' := by positivity
    obtain ⟨h1, h2⟩ := JCx2.pd_cut_nice (E := Wq →L[ℂ] Wp) hR0 hFs
    have hN : JC.NiceCoef Bs ε (fun g => JCx2.pdPhi (R'⁻¹ • g) • F g) :=
      ⟨h1, fun A m => h2 A m, fun g hg hne => by
        refine hεF g hg ?_
        intro h0; apply hne; simp [h0]⟩
    refine JCx2.mn_nice_congr (fun g hg => ?_) hN
    by_cases h0 : F g = 0
    · simp [h0]
    · have hgR : gN g ≤ R := hR g hg h0
      have hg0 : 0 ≤ gN g := Real.sqrt_nonneg _
      have hsq : JCx2.pdSq (R'⁻¹ • g) ≤ 1 := by
        rw [JCx2.pd_sq_smul, JCx2.pd_sq_eq, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
        have : gN g ≤ R' := by rw [hR']; linarith [le_abs_self R]
        nlinarith
      simp [JCx2.pdPhi, JCx2.pd_chi_one hsq]
  · have hGc : Continuous (Gf k r Bs.z Bs.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _
    have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | Gf k r Bs.z Bs.z' g < ε}, g ∈ GV k r →
        Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
        (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | R < gN g}, g ∈ GV k r → Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
        (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hcl : IsClosed {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} :=
      Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
    have hsub : {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} ⊆ C6.domL Bs ∅ :=
      fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
    have hsF : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
    have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      intro T hT
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg
      refine ⟨hg.1, ?_⟩
      by_contra hlt
      exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
    refine ⟨⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg hgn => ?_⟩
    · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hDop T hT).1) hsT
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
    · refine PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g ?_ hg
      show Gf k r Bs.z Bs.z' g < ε
      by_contra hge
      exact hgn ⟨hg, lt_of_lt_of_le hε (not_lt.1 hge), by simp⟩

end

end Formalism.FourierDecayAlt.P
