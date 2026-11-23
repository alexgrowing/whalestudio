import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.TenSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.InfOrthWW
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ExPhi
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.JmMeasurable
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem sb_mul_w {F : Type} [Field F] [NumberField F] {v : P F} {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) :
    (fun m : M2 v => a (m * !![0, 1; -1, 0])) ∈ SB (M2 v) := by
  have h1 : (!![0, -1; 1, 0] : M2 v) * !![0, 1; -1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h2 : (!![0, 1; -1, 0] : M2 v) * !![0, -1; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => m * !![0, 1; -1, 0]
      invFun := fun m => m * !![0, -1; 1, 0]
      left_inv := fun m => by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
      right_inv := fun m => by simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  obtain ⟨hl, hc⟩ := ha
  exact ⟨hl.comp_continuous e.continuous, hc.comp_homeomorph e⟩

private theorem infOrth_wW_inv (F : Type) [Field F] [NumberField F] : InfOrth (wW F)⁻¹ := by
  intro i j
  have h : ((wW F)⁻¹).1 * ((wW F)⁻¹).1ᵀ = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [wW, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [h]

theorem UpperTheory.ConvolutionTheory.R2.I.modSpan :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) D.δ → θ ≠ 0 →
      Fock D.δ ≤ Submodule.span ℂ {φ : S4 F | ∃ u a, Mod v θ W u ∧ a ∈ SB (M2 v) ∧ φ.1 = ten v θ u (Pt a)} := by
  intro F E _ _ _ _ _ _ _ D W v θ hθ hne φ hφ
  obtain ⟨U, hU, -, hk⟩ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).om φ hφ {(wW F)⁻¹} isCompact_singleton
    (by rintro k rfl; exact infOrth_wW_inv F)
  have hs := UpperTheory.ConvolutionTheory.R2.I.tenSpan F v D.δ θ D.neg hne (hU (hk _ rfl))
  have hmap : ∀ x ∈ Submodule.span ℂ {φ : S4 F | ∃ u b, GoodU v D.δ θ u ∧ b ∈ SB (M2 v) ∧ φ.1 = ten v θ u b},
      W.Om (wW F) x ∈ Submodule.span ℂ {φ : S4 F | ∃ u a, Mod v θ W u ∧ a ∈ SB (M2 v) ∧ φ.1 = ten v θ u (Pt a)} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, b, hu, hb, hx⟩ := hx
      obtain ⟨a, ha, rfl⟩ := (UpperTheory.ConvolutionTheory.R2.I.ptInv F v b hb).2
      obtain ⟨u', hu', key⟩ := (UpperTheory.ConvolutionTheory.R2.I.omW F E D W v θ hθ hne).2 u hu
      have hm := UpperTheory.ConvolutionTheory.R2.I.omSL F E D W v θ hθ hne u u' hu hu' key
      exact Submodule.subset_span ⟨u', _, hm, sb_mul_w ha, key a ha x hx⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h := hmap _ hs
  have e : W.Om (wW F) (W.Om (wW F)⁻¹ φ) = φ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rwa [e] at h
