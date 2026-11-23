import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInfOrb

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_rdWord_functional : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (σ : Mat k r → (H →L[ℂ] H))
    (Λ : H →L[ℂ] B), IsURepOn (GG k r) σ → ∀ v : H, IsSmoothVec (k := k) (r := r) σ v →
    SmoothOnH (Hpk k r) (fun g : Mat k r => Λ (σ g v)) ∧
    ∀ ws : List (Mat k r), (∀ X ∈ ws, InLieHpk k r X) → ∀ x ∈ GG k r,
      rdWord ws (fun g : Mat k r => Λ (σ g v)) x = Λ (σ x (dsigW σ ws v)) := by
  intro k r H _ _ _ B _ _ σ Λ hσ v hv
  refine ⟨?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hg, hF, hE⟩ := hv g₀ hg₀
    refine ⟨U, fun g => Λ (F g), hU, hg, (Λ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hgH
    exact congrArg Λ (hE g hgU hgH)
  · intro ws
    induction ws with
    | nil => intro _ x _; rfl
    | cons X w ih =>
      intro hws x hx
      have hX : InLieHpk k r X := hws X List.mem_cons_self
      have hw : ∀ Y ∈ w, InLieHpk k r Y := fun Y hY => hws Y (List.mem_cons_of_mem _ hY)
      have hd := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv w hw hX
      have h2 := ((Λ.comp (σ x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      have e : (fun t : ℝ => rdWord w (fun g : Mat k r => Λ (σ g v)) (x * NormedSpace.exp ((t : ℂ) • X))) =
          (⇑((Λ.comp (σ x)).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW σ w v)) := by
        funext t
        have ht := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hX t
        rw [ih hw _ (GlobalTheory.SgInfDD.gg_mul hx ht)]
        simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply]
        rw [hσ.1.2 x hx _ ht]
        rfl
      show deriv _ 0 = _
      rw [e, h2.deriv]
      rfl

end GlobalTheory.SgInfOrb
