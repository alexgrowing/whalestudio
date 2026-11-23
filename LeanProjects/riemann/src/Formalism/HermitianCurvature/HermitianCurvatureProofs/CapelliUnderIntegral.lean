import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CapelliUnderIntegral

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem glev0 {k r : ℕ} (g : Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ GV k r := by
  simp only [Q.Glev, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, fun a ha => by simp at ha⟩

theorem integrable_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    Integrable (fun x => (L.map (fun i => φ i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))

theorem integral_map_sum {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (L : List ι) (φ : ι → α → E) (h : ∀ i ∈ L, Integrable (φ i) μ) :
    ∫ x, (L.map (fun i => φ i x)).sum ∂μ = (L.map (fun i => ∫ x, φ i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    have hi := h i (by simp)
    have hL : ∀ j ∈ L, Integrable (φ j) μ := fun j hj => h j (by simp [hj])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add hi (integrable_map_sum L φ hL), ih hL]

end Formalism.FourierDecayAlt.P.CapelliUnderIntegral

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem CapelliUnderIntegral.cvUnderInt_of_jWords : Formalism.FourierDecayAlt.JF.JWords → Formalism.FourierDecayAlt.JF.RwRho → Formalism.FourierDecayAlt.JF.CVUnderInt := by
  intro hJW hRR k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hThr hF g hg
  obtain ⟨L, hLw, hL⟩ := CapelliWordSumExpansion.cvWordSumG k r Y
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hJ := hJW k r Wp Wq D A m F hThr hF
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Om k r D.z D.z') (JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ.1 g₀ ⟨(CapelliUnderIntegral.glev0 g₀).2 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm),
      fun g' hg'U hg'G => he g' hg'U ((CapelliUnderIntegral.glev0 g').2 hg'G)⟩
  have hw : ∀ cw ∈ L, (∀ X ∈ cw.2, unitLie k r X) ∧ cw.2.length ≤ m :=
    fun cw h => ⟨(hLw cw h).1, (hLw cw h).2.trans hnm⟩
  have hword : ∀ cw ∈ L, Integrable (fun p => xiP D p • Rw cw.2 (rho D p F) g) D.μSS ∧
      Rw cw.2 (JF D F) g = ∫ p, xiP D p • Rw cw.2 (rho D p F) g ∂D.μSS := by
    intro cw hcw
    obtain ⟨hint, heq⟩ := hJ.2 [] cw.2 (by simp) (hw cw hcw).1 (by simpa using (hw cw hcw).2) g hg
    have hae : (fun p => xiP D p • rho D p (dLR ([].map (AdL p)) (cw.2.map (AdR p)) F) g) =ᵐ[D.μSS]
        (fun p => xiP D p • Rw cw.2 (rho D p F) g) := by
      filter_upwards [B5.ae_inSS D] with p hp
      have e := hRR k r Wp Wq D m F p hp hCk [] cw.2 (by simp)
        (fun X hX => ((hw cw hcw).1 X hX).1) (by simpa using (hw cw hcw).2) g hg.1
      simp only [List.map_nil] at e ⊢
      rw [← e]
      rfl
    exact ⟨hint.congr hae, (show Rw cw.2 (JF D F) g = dLR [] cw.2 (JF D F) g from rfl).trans
      (heq.trans (integral_congr_ae hae))⟩
  rw [hL _ _ (JF D F) hJck g hg hg.1]
  have hae2 : (fun p => xiP D p • Q.CV k r Y (rho D p F) g) =ᵐ[D.μSS]
      (fun p => (L.map (fun cw => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g))).sum) := by
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hL _ _ (rho D p F) (B5.ckOn_rho D hp hCkn) g hg.1 hg.1, List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left (fun cw _ => ?_)
    simp only [Function.comp_apply]
    exact smul_comm _ _ _
  rw [integral_congr_ae hae2, CapelliUnderIntegral.integral_map_sum L
    (fun cw p => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g))
    (fun cw hcw => (hword cw hcw).1.smul cw.1)]
  congr 1
  refine List.map_congr_left (fun cw hcw => ?_)
  rw [integral_smul, (hword cw hcw).2]

end Formalism.FourierDecayAlt.P
