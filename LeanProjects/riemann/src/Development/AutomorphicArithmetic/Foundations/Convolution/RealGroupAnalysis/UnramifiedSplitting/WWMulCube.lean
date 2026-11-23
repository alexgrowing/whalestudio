import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem nU_mul_neg {F : Type} [Field F] [NumberField F] (b : A F) : nU b * nU (-b) = 1 := by
  apply Subtype.ext
  show (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A F)) * !![1, -b; 0, 1] = 1
  simp [Matrix.mul_fin_two, Matrix.one_fin_two]

private theorem wW_mul_cube (F : Type) [Field F] [NumberField F] : wW F * (wW F * (wW F * wW F)) = 1 := by
  apply Subtype.ext
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A F)) * (!![0, 1; -1, 0] * (!![0, 1; -1, 0] * !![0, 1; -1, 0])) = 1
  simp [Matrix.mul_fin_two, Matrix.one_fin_two]

theorem UpperTheory.ConvolutionTheory.R2.H.slKer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (φ : S4 F), Sl0 φ.1 → ∀ g, ThRow 0 0 (W.Om g φ).1 = 0 := by
  intro F E _ _ _ _ _ _ _ D W φ hφ g
  have hH : St.Hat W := hatSt F E D W
  let P : G1 F → Prop := fun g => ∀ χ : S4 F, Sl0 χ.1 → Sl0 (W.Om g χ).1
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb χ h
    have e : W.Om (a * b) χ = W.Om a (W.Om b χ) := by
      rw [map_mul]; rfl
    rw [e]
    exact ha _ (hb _ h)
  have hone : P 1 := by
    intro χ h
    rw [map_one]
    exact h
  have hn : ∀ b, P (nU b) := by
    intro b χ h u t
    rw [hH.n]
    have e : Function.update (![0, 0, u, t] : V4 F) 1
        ((![0, 0, u, t] : V4 F) 1 + b * (![0, 0, u, t] : V4 F) 0) = ![0, 0, u, t] := by
      apply Function.update_eq_self_iff.mpr
      simp
    rw [e, h u t, mul_zero]
  have hw : P (wW F) := by
    intro χ h u t
    rw [hH.w]
    have e : ∀ z : Fin 2 → A F, hat χ.1 ![-(![0, 0, u, t] : V4 F) 1, (![0, 0, u, t] : V4 F) 0, z 0, z 1] = 0 := by
      intro z
      have := h (z 0) (z 1)
      simpa using this
    simp only [e, zero_mul, MeasureTheory.integral_zero]
  have hw3 : P (wW F)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right (wW_mul_cube F)]
    exact hmul _ _ hw (hmul _ _ hw hw)
  have hall : ∀ g : G1 F, P g ∧ P g⁻¹ := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
      rw [(gen F).1]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | hx
      · refine ⟨hn b, ?_⟩
        rw [inv_eq_of_mul_eq_one_right (nU_mul_neg b)]
        exact hn _
      · rw [Set.mem_singleton_iff.mp hx]
        exact ⟨hw, hw3⟩
    | one => simpa using hone
    | mul x y _ _ hx hy =>
      refine ⟨hmul _ _ hx.1 hy.1, ?_⟩
      rw [_root_.mul_inv_rev]
      exact hmul _ _ hy.2 hx.2
    | inv x _ hx =>
      rw [inv_inv]
      exact ⟨hx.2, hx.1⟩
  have hs : Sl0 (W.Om g φ).1 := (hall g).1 φ hφ
  unfold ThRow
  simp only [hs _ _, tsum_zero]
