import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RowBij
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem unfold_strip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  intro L ρ Ψ W hρ hΨ hΨm hW
  classical
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) := inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  haveI : Countable (Gamma0 L) := Subtype.countable
  have memΓ : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L ↔ (L : ℤ) ∣ γ 1 0 := by
    intro γ
    rw [Gamma0_mem]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hs : MeasurableSet strip := by
    have : strip = (fun τ : ℍ => τ.re) ⁻¹' Set.Ico 0 1 := by
      ext τ; simp [strip]
    rw [this]
    exact UpperHalfPlane.continuous_re.measurable measurableSet_Ico
  set f : ℍ → ℂ := strip.indicator Ψ with hf_def
  have hfi : Integrable f := (integrable_indicator_iff hs).2 hΨ
  have hfm : AEStronglyMeasurable f := hfi.aestronglyMeasurable
  have mp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun τ : ℍ => γ • τ) volume volume := fun γ =>
    measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have me : ∀ γ : SL(2, ℤ), MeasurableEmbedding (fun τ : ℍ => γ • τ) := fun γ =>
    (MeasurableEquiv.smul ((γ : GL (Fin 2) ℝ))).measurableEmbedding
  have rowEq : ∀ (γ : SL(2, ℤ)) (a b : ℤ), γ 1 0 = a → γ 1 1 = b → UpperTheory.V.Af.Rs.row γ = ![a, b] := by
    intro γ a b ha hb
    funext i
    fin_cases i
    · simpa [UpperTheory.V.Af.Rs.row] using ha
    · simpa [UpperTheory.V.Af.Rs.row] using hb
  have step1 : ∀ τ : ℍ, ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ =
      ∑' γ : Gamma0 L, f ((γ : SL(2, ℤ)) • τ) := by
    intro τ
    have key : ∀ x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, ∃ γ : Gamma0 L,
        ((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1) = x.1 ∧ (γ : SL(2, ℤ)) • τ ∈ strip := by
      intro x
      obtain ⟨γ, ⟨hr, hst⟩, -⟩ := UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩
      have h0 : γ 1 0 = x.1.1 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 0
      have h1 : γ 1 1 = x.1.2 := by simpa [UpperTheory.V.Af.Rs.row] using congrFun hr 1
      refine ⟨⟨γ, (memΓ γ).2 (h0 ▸ x.2.2)⟩, ?_, hst⟩
      simp [h0, h1]
    choose g hg using key
    have ginj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      rw [← (hg x).1, ← (hg y).1, hxy]
    have hsupp : Function.support (fun γ : Gamma0 L => f ((γ : SL(2, ℤ)) • τ)) ⊆ Set.range g := by
      intro γ hγ
      have hin : (γ : SL(2, ℤ)) • τ ∈ strip := by
        by_contra h
        exact hγ (Set.indicator_of_notMem h _)
      have hL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := (memΓ γ).1 γ.2
      have hcop : IsCoprime ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := UpperTheory.V.Af.Rs.rowBij.1 γ
      refine ⟨⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩, ?_⟩
      set x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1} := ⟨((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1), hcop, hL⟩
      have hx := hg x
      apply Subtype.ext
      exact (UpperTheory.V.Af.Rs.rowBij.2 τ ⟨![x.1.1, x.1.2], by simpa using x.2.1⟩).unique
        ⟨rowEq _ _ _ (congrArg Prod.fst hx.1) (congrArg Prod.snd hx.1), hx.2⟩ ⟨rowEq _ _ _ rfl rfl, hin⟩
    rw [← ginj.tsum_eq hsupp]
    refine tsum_congr fun x => ?_
    have hx := hg x
    have hL : (L : ℤ) ∣ (g x : SL(2, ℤ)) 1 0 := (memΓ _).1 (g x).2
    rw [hf_def, Set.indicator_of_mem hx.2, hW _ hL τ, hx.1]
  have hsum : ∀ τ, HasSum (fun γ : Gamma0 L => ρ ((γ : SL(2, ℤ))⁻¹ • τ)) 1 := fun τ => by
    have := (Equiv.inv (Gamma0 L)).hasSum_iff.mpr (hρ.sum τ)
    simpa [Function.comp_def] using this
  set F : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ τ : ℂ) * f ((γ : SL(2, ℤ)) • τ) with hF
  set G : Gamma0 L → ℍ → ℂ := fun γ τ => (ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℂ) * f τ with hG
  have hFG : ∀ γ, F γ = fun τ => G γ ((γ : SL(2, ℤ)) • τ) := by
    intro γ; funext τ; simp [hF, hG]
  have Gm : ∀ γ, AEStronglyMeasurable (G γ) := fun γ =>
    ((Complex.measurable_ofReal.comp (hρ.meas.comp (me ((γ : SL(2, ℤ))⁻¹)).measurable)).aestronglyMeasurable).mul hfm
  have Fm : ∀ γ, AEStronglyMeasurable (F γ) := fun γ => by
    rw [hFG γ]
    exact (Gm γ).comp_measurePreserving (mp γ)
  have tot : ∀ τ, ∑' γ : Gamma0 L, ‖G γ τ‖ₑ = ‖f τ‖ₑ := by
    intro τ
    simp only [hG, enorm_mul]
    rw [ENNReal.tsum_mul_right]
    have : ∑' γ : Gamma0 L, ‖((ρ ((γ : SL(2, ℤ))⁻¹ • τ) : ℝ) : ℂ)‖ₑ = 1 := by
      simp_rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (hρ.nonneg _)]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => hρ.nonneg _) (hsum τ).summable, (hsum τ).tsum_eq,
        ENNReal.ofReal_one]
    rw [this, one_mul]
  have finG : ∑' γ, ∫⁻ τ, ‖G γ τ‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum (fun γ => (Gm γ).enorm)]
    simp_rw [tot]
    exact hfi.hasFiniteIntegral.ne
  have finF : ∑' γ, ∫⁻ τ, ‖F γ τ‖ₑ ≠ ⊤ := by
    have : ∀ γ, ∫⁻ τ, ‖F γ τ‖ₑ = ∫⁻ τ, ‖G γ τ‖ₑ := fun γ => by
      rw [hFG γ]
      exact (mp γ).lintegral_comp_emb (me γ) (fun τ => ‖G γ τ‖ₑ)
    simp_rw [this]
    exact finG
  calc ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ
        = ∫ τ, ∑' γ, F γ τ := by
          congr 1; funext τ; rw [step1 τ, ← tsum_mul_left]
    _ = ∑' γ, ∫ τ, F γ τ := integral_tsum Fm finF
    _ = ∑' γ, ∫ τ, G γ τ := by
          refine tsum_congr fun γ => ?_
          rw [hFG γ]
          exact (mp γ).integral_comp (me γ) (G γ)
    _ = ∫ τ, ∑' γ, G γ τ := (integral_tsum Gm finG).symm
    _ = ∫ τ, f τ := by
          congr 1; funext τ
          simp only [hG]
          rw [tsum_mul_right, ← Complex.ofReal_tsum, (hsum τ).tsum_eq]
          simp
    _ = ∫ τ in strip, Ψ τ := integral_indicator hs

end GlobalTheory.EisM

end
