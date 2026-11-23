import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MatLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Cols
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.ContinuousQuaternaryFormLeft
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IntegrableCols
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.JmMeasurable
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem sb_mul_w {F : Type} [Field F] [NumberField F] {v : P F} {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) :
    (fun m : M2 v => a (m * !![0, -1; 1, 0])) ∈ SB (M2 v) := by
  have h1 : (!![0, -1; 1, 0] : M2 v) * !![0, 1; -1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have h2 : (!![0, 1; -1, 0] : M2 v) * !![0, -1; 1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  let e : M2 v ≃ₜ M2 v :=
    { toFun := fun m => m * !![0, -1; 1, 0]
      invFun := fun m => m * !![0, 1; -1, 0]
      left_inv := fun m => by simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      right_inv := fun m => by simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  obtain ⟨hl, hc⟩ := ha
  exact ⟨hl.comp_continuous e.continuous, hc.comp_homeomorph e⟩

private theorem infOrth_wW (F : Type) [Field F] [NumberField F] : InfOrth (wW F) := by
  intro i j
  have h : (wW F).1 * (wW F).1ᵀ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [wW, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [h]

theorem UpperTheory.ConvolutionTheory.R2.I.omW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) D.δ → θ ≠ 0 →
      (∀ u (a : M2 v → ℂ) (b : Kv v) (φ : S4 F), φ.1 = ten v θ u (Pt a) →
        (W.Om (nU (sg v b)) φ).1 = ten v θ u (Pt fun m => a (m * !![1, b; 0, 1]))) ∧
      ∀ u, GoodU v D.δ θ u → ∃ u', GoodU v D.δ θ u' ∧ ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
        (W.Om (wW F) φ).1 = ten v θ u' (Pt fun m => a (m * !![0, 1; -1, 0])) := by
  intro F E _ _ _ _ _ _ _ D W v θ hθ hne
  obtain ⟨-, -, hq, -⟩ := UpperTheory.ConvolutionTheory.R2.I.matLaws F v D.δ θ hθ hne
  obtain ⟨-, hψ, -⟩ := UpperTheory.ConvolutionTheory.R2.I.psiLaws F v
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hPt : ∀ a ∈ SB (M2 v), Pt a ∈ SB (M2 v) := fun a ha => by
    have := (T ⟨a, ha⟩).2
    rwa [hT] at this
  refine ⟨?_, ?_⟩
  · intro u a b φ hφ
    funext X
    rw [W.Om_n, hφ, hq, hψ]
    simp only [ten]
    rw [← ((UpperTheory.ConvolutionTheory.R2.I.ptN F v a (mat v θ X)).1 b)]
    ring
  · intro u hu
    obtain ⟨u', hu'⟩ := UpperTheory.ConvolutionTheory.R2.I.tenFt F v D.δ θ hθ hne u hu
    have key : ∀ a ∈ SB (M2 v), ∀ φ : S4 F, φ.1 = ten v θ u (Pt a) →
        (W.Om (wW F) φ).1 = ten v θ u' (Pt fun m => a (m * !![0, 1; -1, 0])) := by
      intro a ha φ hφ
      funext X
      rw [W.Om_w, hφ, hu' _ (hPt a ha)]
      simp only [ten]
      rw [UpperTheory.ConvolutionTheory.R2.I.ptW F v a ha]
    refine ⟨u', ?_, key⟩
    intro b hb
    obtain ⟨a1, ha1, rfl⟩ := ((UpperTheory.ConvolutionTheory.R2.I.ptInv F v b hb).2)
    have ha := sb_mul_w ha1
    obtain ⟨φ, hφF, hφ⟩ := hu _ (hPt _ ha)
    obtain ⟨U, hU, -, hk⟩ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).om φ hφF {wW F} isCompact_singleton
      (by rintro k rfl; exact infOrth_wW F)
    refine ⟨W.Om (wW F) φ, hU (hk _ rfl), ?_⟩
    rw [key _ ha φ hφ]
    congr 2
    funext m
    have h2 : (!![0, 1; -1, 0] : M2 v) * !![0, -1; 1, 0] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
