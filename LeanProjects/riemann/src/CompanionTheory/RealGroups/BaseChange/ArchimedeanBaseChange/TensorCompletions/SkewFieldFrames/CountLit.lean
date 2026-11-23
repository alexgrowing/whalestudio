import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PParamL
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PSkewEx
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PStruct
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PFactorField
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PQuadField
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PLocDict
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PClsNorm
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PClsOnto
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PClsEq
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PBaseFrame
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PInertBase
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PSplitSq
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PTensorCompl
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PLocGood
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.Count1Pf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3

theorem param_lit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → ∃ (ι : Type) (_ : Fintype ι) (K L : ι → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Field (L i)) (_ : ∀ i, NumberField (L i)) (_ : ∀ i, Algebra (K i) (L i)) (_ : ∀ i, Algebra.IsQuadraticExtension (K i) (L i)) (x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i)), Fintype.card ι = nfac P ∧ (∀ i, NumberField.IsTotallyReal (K i)) ∧ (∀ i, NumberField.IsTotallyComplex (L i)) ∧ (∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i)) ∧ ∑ i, Fintype.card (InfinitePlace (K i)) = n * Fintype.card (InfinitePlace E) ∧ Nonempty ({c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} ≃ ∀ i, {q : (K i)ˣ ⧸ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) // ∃ t : (K i)ˣ, q = QuotientGroup.mk t ∧ ∀ u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) t u ∈ GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i))}) :=
  param_pfL skewEx_pf (struct_pf factorField_pf) quadField_pf
    (locDict_pf clsNorm_pf clsOnto_pf clsEq_pf baseFrame_pf (inertBase_pf tensorCompl_pf) (splitSq_pf tensorCompl_pf)
      tensorCompl_pf) clsNorm_pf clsOnto_pf clsEq_pf locGood_pf

end CompanionTheory.Rg.BcB.G3
