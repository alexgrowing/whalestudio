import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkStab
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FinPartMulVec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwSum
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoeffB
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.QuaternaryFormEqOfFinitePart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OmFinite
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Entries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OmX
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ProdEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.fockSt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), St.FockSt W := by
  intro F E _ _ _ _ _ _ _ D W
  obtain ⟨O⟩ := opsEx F
  have one : ∀ (T : Module.End ℂ (S4 F)), (∀ φ ∈ Vac D.δ, T φ ∈ Vac D.δ) →
      (∀ w i φ, T (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)}) → ∀ φ ∈ Fock D.δ, T φ ∈ Fock D.δ := by
    intro T h1 h2 φ hφ
    obtain ⟨Λ, m, hm⟩ := fockEx F E D O {φ} (Set.finite_singleton φ) (by simpa using hφ)
    exact (fkLe F D.δ O).2 _ le_rfl m (fkStab F D.δ O T (Vac D.δ ⊓ Fix D.δ Λ) _ le_rfl (fun χ hχ => h1 χ hχ.1) h2 m φ (hm φ rfl))
  refine ⟨fun k => one _ (vacL F E D W _ ?_) (lX F E D W O _), fun φ hφ => ?_, fun φ hφ C hC hO => ?_⟩
  · rw [pInf_finGL]; exact one_mem _
  · obtain ⟨Λ, m, hm⟩ := fockEx F E D O {φ} (Set.finite_singleton φ) (by simpa using hφ)
    refine ⟨_, (fkLe F D.δ O).2 _ inf_le_left m, (fkBasic F O).2.2 _ (vacFd F E D Λ) m, fun k => ?_⟩
    refine fkStab F D.δ O _ (Vac D.δ ⊓ Fix D.δ Λ) (Vac D.δ ⊓ Fix D.δ Λ) inf_le_left (fun χ hχ => ⟨vacL F E D W _ ?_ χ hχ.1, lFix F E D W _ Λ χ hχ.2⟩)
      (lX F E D W O _) m φ (hm φ rfl)
    rw [pInf_infGL]; exact k.2
  · obtain ⟨s, hs, h1, h2⟩ := omFinite F E D W φ C hC
    have orth : ∀ g : G1 F, InfOne g → InfOrth g := by
      intro g hg i j
      have e : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
      have hg' : ∀ i j, (g.1 i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 := hg
      rw [Matrix.mul_apply, Fin.sum_univ_two, e, Matrix.transpose_apply, Matrix.transpose_apply, hg', hg', hg', hg', ← e]
      refine congrArg (fun x : A F => x.1) ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    obtain ⟨Λ, m, hm⟩ := fockEx F E D O ((fun g => W.Om g φ) '' s) (hs.image _) (by
      rintro _ ⟨g, hg, rfl⟩
      exact one _ (vacOm F E D W g (orth g (h1 g hg))) (omX F E D W O g) φ hφ)
    refine ⟨_, (fkLe F D.δ O).2 _ inf_le_left m, (fkBasic F O).2.2 _ (vacFd F E D Λ) m, fun k hk => ?_⟩
    obtain ⟨g, hg, k', a1, a2, a3⟩ := h2 k hk
    rw [a3]
    exact fkStab F D.δ O _ (Vac D.δ ⊓ Fix D.δ Λ) (Vac D.δ ⊓ Fix D.δ Λ) inf_le_left (fun χ hχ => ⟨vacOm F E D W k' (a2 (hO k hk)) χ hχ.1, omFix F E D W k' a1 Λ χ hχ.2⟩)
      (omX F E D W O k') m _ (hm _ ⟨g, hg, rfl⟩)
