import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Assemble
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlumb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.ok_of_conj (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {y y' : GR d.n} {x₁ x₂ : d.G} {A₁ A₂ A' : d.LF → d.LF} {B₁ B₂ : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w (R.ι w y') A' id)
    (hy : R.ι w y = x₁ * R.ι w y' * x₂) (h1 : x₁ * x₂ = 1) : R.OkY w y := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  intro f hf
  by_cases hf0 : ∀ u, f u = 0
  · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
    have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hf0])
    subst this
    rw [map_zero, d.T_zero]
    funext X
    simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
  · push Not at hf0
    obtain ⟨u₀, hu₀⟩ := hf0
    by_cases hex : ∃ κ : ℂ, κ ≠ 0 ∧ A₁ (A₂ f) = κ • f
    · obtain ⟨κ, hκ, hA⟩ := hex
      refine ⟨κ⁻¹ • A₁ (A' (A₂ f)), ?_, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      · obtain ⟨φ, hφ⟩ := hc.1 f hf
        refine ⟨κ⁻¹ • φ, ?_⟩
        funext u
        have := congrFun hφ u
        simp only [Function.comp_apply] at this
        simp [this]
      · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have hB : ∀ X, B₁ (B₂ Ψ) X = κ⁻¹ * Ψ X := by
          intro X
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
          have h2 := congrFun e0 (X + Z)
          have h3 := hΨ X Z hZ1 hZ2
          have h4 := hBaway X Z hZ1 hZ2
          simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, hZ3, hA, Pi.smul_apply, smul_eq_mul] at h2 h4
          rw [h3, h4] at h2
          rw [eq_inv_mul_iff_mul_eq₀ hκ]
          apply mul_left_cancel₀ hu₀
          linear_combination -h2
        rw [hy, e]
        funext X
        simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hB]
        ring
    · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      have hΨ0 : ∀ X, Ψ X = 0 := by
        by_contra hne
        push Not at hne
        obtain ⟨X₀, hX₀⟩ := hne
        have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
        rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
        have hBaway := (h0.2 Ψ hΨ).1
        have key : ∀ u, f u * Ψ X₀ = A₁ (A₂ f) u * B₁ (B₂ Ψ) X₀ := by
          intro u
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
          have h2 := congrFun e0 (X₀ + Z)
          have h3 := hΨ X₀ Z hZ1 hZ2
          have h4 := hBaway X₀ Z hZ1 hZ2
          simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, hZ3] at h2 h4
          rw [h3, h4] at h2
          exact h2
        have hB0 : B₁ (B₂ Ψ) X₀ ≠ 0 := by
          intro h0'
          have := key u₀
          rw [h0', mul_zero] at this
          exact mul_ne_zero hu₀ hX₀ this
        apply hex
        refine ⟨Ψ X₀ / B₁ (B₂ Ψ) X₀, div_ne_zero hX₀ hB0, ?_⟩
        funext u
        have := key u
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [div_mul_eq_mul_div, eq_div_iff hB0]
        linear_combination -this
      have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨ0])
      subst this
      rw [map_zero, d.T_zero]
      funext X
      simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨ0]
end RD
theorem locOpEx_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k := by
  intro F E _ _ _ _ _ σ d R w
  refine ⟨_, R.isLocOp_of_ok w fun y => ?_⟩
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨C, s, B, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have okN : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b → R.OkY w y :=
    fun y b hb hy => R.ok_of_step w (R.stepN w hT y b hb hy)
  have okM : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = Glob.mM a → R.OkY w y := by
    intro y a ha hy
    obtain ⟨c, -, hc⟩ := R.stepM w hT y a ha hy
    exact R.ok_of_step w hc
  have okB : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = Glob.nbar c → R.OkY w y := by
    intro y c hc hy
    obtain ⟨y', x, hx, hy', hrel⟩ := R.nbar_conj' w hw₀ y c hc hy
    have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
    exact R.ok_of_conj w hT hW3 hW (R.stepN w hT y' x hx hy') hrel (_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀)
  obtain ⟨y1, y2, y3, y4, hy, ⟨t, ht⟩, ⟨c, hc, hc2⟩, ⟨a, ha, ha2⟩, ⟨b, hb, hb2⟩⟩ := PositivityTheory.Rg.Sw.Glob.decomp d.n y
  rw [hy]
  exact R.ok_mul w hsch (R.ok_mul w hsch (R.ok_mul w hsch (okN y1 _ (herm_smul_one' t) ht) (okB y2 c hc hc2))
    (okM y3 a ha ha2)) (okN y4 b hb hb2)
end PositivityTheory.SiegelWeilFormula
end
end
