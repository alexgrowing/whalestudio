import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.SetIntegralMulRight
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StableOfOrth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FW
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem lift_neg_form {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (M : Meas F) (u : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) :
    lift W M (fun x => -u x) φ h = -lift W M u φ h := by
  unfold lift
  simp only [neg_mul]
  exact integral_neg _

private theorem lift_neg_data {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (M : Meas F) (u : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) :
    lift W M u (-φ) h = -lift W M u φ h := by
  unfold lift
  have e : ∀ χ : S4 F, Th (-χ).1 = -Th χ.1 := fun χ => by
    unfold Th
    exact tsum_neg
  simp only [map_neg, e, mul_neg]
  exact integral_neg _

theorem UpperTheory.ConvolutionTheory.R2.Fo.moveF :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (O : Ops F), MoveE O W M π →
    ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ w h, lift W M f.1 (O.f D.δ w φ) h = -lift W M (TR.Eop w 1 0 f).1 φ h := by
  intro F E _ _ _ _ _ _ _ D W M π O hE f hf φ hφ v h
  obtain ⟨hV, hAd, hO⟩ := UpperTheory.ConvolutionTheory.R2.Fo.adW F
  have left : ∀ u ∈ π.V, ∀ γ g, u.1 (ratGL F 2 γ * g) = u.1 g := fun u hu => (π.cusp u hu).1.left
  set f' := TR.rt F 2 (gl (wW F)⁻¹) f with hf'def
  have hf' : f' ∈ π.V := (hV π f hf).2
  set φ' := W.Om (wW F)⁻¹ φ with hφ'def
  have hφ' : φ' ∈ Fock D.δ := by
    obtain ⟨U, hU, -, hk⟩ := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).om φ hφ {(wW F)⁻¹} isCompact_singleton
      (by rintro k rfl; exact hO)
    exact hU (hk _ rfl)
  set f'' := TR.Eop v 0 1 f' with hf''def
  have hf'' : f'' ∈ π.V := π.stable (.lie _) f' hf'
  have e1 : φ = W.Om (wW F) φ' := by
    rw [hφ'def, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have e2 : O.f D.δ v φ = -W.Om (wW F) (O.e D.δ v φ') := by
    have := congrArg (fun T : Module.End ℂ (S4 F) => T φ') (UpperTheory.ConvolutionTheory.R2.Fo.fW F E D W O v)
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at this
    rw [← e1] at this
    exact this
  have e3 : lift W M f.1 (W.Om (wW F) (O.e D.δ v φ')) = lift W M f'.1 (O.e D.δ v φ') :=
    UpperTheory.ConvolutionTheory.R2.Fo.moveG F E D W M f.1 (left f hf) _ _
  have e4 : lift W M f''.1 φ' = lift W M (TR.rt F 2 (gl (wW F)) f'').1 φ := by
    have := UpperTheory.ConvolutionTheory.R2.Fo.moveG F E D W M f''.1 (left f'' hf'') φ (wW F)⁻¹
    rw [inv_inv] at this
    exact this
  have e5 : TR.rt F 2 (gl (wW F)) f'' = -TR.Eop v 1 0 f := by
    have a := congrArg (fun T : Module.End ℂ (TR.Sm F 2) => T f') (hAd v)
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at a
    have b : TR.rt F 2 (gl (wW F)) f' = f := by
      rw [hf'def, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Module.End.one_apply]
    rw [b] at a
    exact a
  have e6 : (TR.rt F 2 (gl (wW F)) f'').1 = fun x => -(TR.Eop v 1 0 f).1 x := by
    rw [e5]; rfl
  rw [e2, lift_neg_data, e3, hE f' hf' φ' hφ' v h, neg_neg, e4, e6, lift_neg_form]
