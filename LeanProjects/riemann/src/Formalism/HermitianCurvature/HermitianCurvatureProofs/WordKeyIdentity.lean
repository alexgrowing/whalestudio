import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordKeyIdentity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem int_list_smul' {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => a i • φ i p).sum) μ ∧
      ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hadd := integral_add (hi.smul (a i)) hl1
    simp only [Pi.smul_apply] at hadd
    simp only [List.map_cons, List.sum_cons]
    refine ⟨(hi.smul (a i)).add hl1, ?_⟩
    rw [hadd, integral_smul, hl2]

theorem int_list_smul {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum :=
  (int_list_smul' μ l a φ h).2

theorem smul_list_smul {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (a : ι → ℂ)
    (x : ι → E) : c • (l.map fun i => a i • x i).sum = (l.map fun i => a i • (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [smul_add, ih, smul_comm c (a i)]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

theorem word_key (hW : JWords) (hR : RwRho) (D : RealPlaceData k r Wp Wq) {A : ℝ} {m : ℕ}
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : InCC A m F) {g : Mat k r} (hg : g ∈ Om k r D.z D.z')
    (w : List (Mat k r)) (hw : ∀ X ∈ w, unitLie k r X) (hl : w.length ≤ m) :
    Integrable (fun p => xiP D p • Rw w (rho D p F) g) D.μSS ∧
      Rw w (JF D F) g = ∫ p, xiP D p • Rw w (rho D p F) g ∂D.μSS := by
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] w (by simp) hw (by simpa using hl) g hg
  simp only [List.map_nil] at hI hE
  have hae : (fun p => xiP D p • rho D p (dLR [] (w.map (AdR p)) F) g) =ᵐ[D.μSS]
      fun p => xiP D p • Rw w (rho D p F) g := by
    filter_upwards [B5.ae_inSS D] with p hp
    have := hR k r Wp Wq D m F p hp hCk [] w (by simp) (fun X hX => (hw X hX).1) (by simpa using hl) g hg.1
    simp only [List.map_nil] at this
    rw [← this]
    rfl
  exact ⟨hI.congr hae, by rw [← integral_congr_ae hae]; exact hE⟩

end Formalism.FourierDecayAlt.P.WordKeyIdentity

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem capelli_under_integral_of_parts : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by
  intro hW hWS hR k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hT hF g hg
  obtain ⟨L, hLw, hLeq⟩ := hWS k r Y
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Om k r D.z D.z') (JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ ⟨WordKeyIdentity.glev0 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun x hx hxG => he x hx (WordKeyIdentity.glev0 hxG)⟩
  rw [hLeq _ _ _ hJck g hg hg.1]
  have key : ∀ cw ∈ L, Integrable (fun p => xiP D p • Rw cw.2 (rho D p F) g) D.μSS ∧
      Rw cw.2 (JF D F) g = ∫ p, xiP D p • Rw cw.2 (rho D p F) g ∂D.μSS := fun cw hcw =>
    WordKeyIdentity.word_key hW hR D hT hF hg cw.2 (hLw cw hcw).1 ((hLw cw hcw).2.trans hnm)
  have hRHS : (∫ p, xiP D p • Q.CV k r Y (rho D p F) g ∂D.μSS) =
      ∫ p, (L.map fun cw => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g)).sum ∂D.μSS := by
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hLeq _ _ _ (B5.ckOn_rho D hp hCkn) g hg.1 hg.1, WordKeyIdentity.smul_list_smul]
  rw [hRHS, WordKeyIdentity.int_list_smul D.μSS L (fun cw => cw.1) (fun cw p => xiP D p • Rw cw.2 (rho D p F) g)
    fun cw hcw => (key cw hcw).1]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [(key cw hcw).2]

end Formalism.FourierDecayAlt.P
