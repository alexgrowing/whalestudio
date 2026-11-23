import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtEpart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion

namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section rw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_vanish_GV {O : Set (Mat k r)} (hO : IsOpen O) {f : Mat k r → E}
    (h : ∀ g ∈ O, g ∈ GV k r → f g = 0) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ O, g ∈ GV k r → Rw w f g = 0
  | [], _ => h
  | X :: w, hw => by
    intro g hg hgG
    have ih := rw_vanish_GV hO h w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    have hX : inLie k r X := hw X List.mem_cons_self
    show RdV X (Rw w f) g = 0
    unfold RdV
    have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
    have h0 : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ O := by
      simp only; rw [Formalism.FourierDecayAlt.P.B5.curve_zero]; exact hg
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have e : (fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hev] with t ht
      exact ih _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    rw [e.deriv_eq]; simp

end rw

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_eq_zero (Θ : DiffOp k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (h : ∀ T ∈ Θ, Rw T.word F g = 0) : opApply Θ F g = 0 := by
  unfold opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [h T hT, map_zero]

theorem ckOn_opApply_list (UU : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hs : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ UU) :
    ∀ Θ : DiffOp k r Wp Wq, (∀ T ∈ Θ, CkOn ⊤ UU T.coef) →
      (∀ T ∈ Θ, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ UU) → CkOn ⊤ (GV k r) (opApply Θ F)
  | [], _, _ => by
    have e : opApply ([] : DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, hc, hsu => by
    have e : opApply (T :: Θ) F = fun g => T.coef g (Rw T.word F g) + opApply Θ F g := by
      funext g; simp [opApply]
    rw [e]
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add ?_ (ckOn_opApply_list UU F hF hs Θ (fun T' hT' => hc T' (List.mem_cons_of_mem _ hT'))
      (fun T' hT' => hsu T' (List.mem_cons_of_mem _ hT')))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_coef (hc T List.mem_cons_self)
      (Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hF T.word_lie) (hsu T List.mem_cons_self)

end op

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem theta_compact_support : Formalism.FourierDecayAlt.KB.ThetaCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F w e Cb hDD hF hw
  obtain ⟨nf, fib, o, κ, Dop, _, hIn, _, _, hΘeq⟩ := hDD w hw e
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  have hGc : Continuous (Gf P.k P.r p.T.base.z p.T.base.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _

  have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | Gf P.k P.r p.T.base.z p.T.base.z' g < ε}, g ∈ GV P.k P.r →
      Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
      (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | R < gN g}, g ∈ GV P.k P.r → Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
      (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hcl : IsClosed {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} :=
    Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
  have hsub : {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} ⊆
      C6.domL p.T.base ∅ := fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
  have hsF : closure {g | g ∈ GV P.k P.r ∧ F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
  have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV P.k P.r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    intro T hT
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg
    refine ⟨hg.1, ?_⟩
    by_contra hlt
    exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
  refine ⟨opApply Dop F, ⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg => hΘeq F g hg, ?_⟩
  · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hIn.1 T hT).1) hsT
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
  · intro a
    show D.vecV p.T.base p.ν' p.m₀ _ a = D.vecV p.T.base p.ν' p.m₀ _ a
    unfold D.vecV
    split_ifs with h1 h2
    · have hγ := h2.choose_spec
      have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h2.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec _ _ _ _ a _ h1.1 hγ.2.1]; exact h1.2
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h2.choose _ (p.Θ.Θ w e F) (opApply Dop F) 1 ?_, one_smul]
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
      rw [one_smul]
      simp only [D.orbIntegrand, rho]
      rw [hΘeq F _ ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem p.T.base hq hγ.1,
        by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hG, by simp⟩]
    · rfl
    · rfl

end Formalism.FourierDecayAlt.P
