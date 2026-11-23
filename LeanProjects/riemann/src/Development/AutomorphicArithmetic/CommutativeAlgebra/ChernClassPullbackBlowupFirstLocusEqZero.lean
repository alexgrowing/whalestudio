import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section
namespace UpperTheory.Rel1

private abbrev Ac (N : ℕ) : Act := (BC N).sub ((Q1 N).comap (βC N))

private theorem isUnit_cyclotomicPeriod_deRham {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) :
    IsUnit ((show Um N A × Um 2 A from p.pt.1).2.1 1) := by
  have h := p.pt.2
  change IsUnit ((Um.join (show Um N A × Um 2 A from p.pt.1)).1 (Fin.last N)) at h
  simpa [Um.join] using h

private def tU {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) : Aˣ := (isUnit_cyclotomicPeriod_deRham p).unit

private def vert {E : Spc} {N : ℕ} {T : Scheme.{0}} (x : Sx (Sp E (Ac N)) 0 T) : Ob (Ac N) Γ(T, ⊤) :=
  (show ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 0 from x.2).obj 0

private def ww (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 0 T) : (Γ(T, ⊤))ˣ := tU (vert x)

private theorem triv1 (E : Spc) (N : ℕ) {T' T : Scheme.{0}} (g : T' ⟶ T) (x : Sx (Sp E (Ac N)) 0 T) :
    ww E N T' (x.res g) = Units.map g.appTop.hom.toMonoidHom (ww E N T x) := by
  ext
  rfl

private theorem triv2 (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 1 T) :
    lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x * ww E N T (x.face 0) = ww E N T (x.face 1) := by
  let c : ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 1 := x.2
  let f := c.map' 0 1
  have hl : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x = (show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 := by
    have e : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x =
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
          (show (Γ(T, ⊤))ˣ from (chiB N).app Γ(T, ⊤) f.1)) := rfl
    rw [e]
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
    rfl
  rw [hl]
  change _ * tU (c.obj 1) = tU (c.obj 0)
  ext
  have e := congrArg (fun p => (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from p.1).2.1 1) f.2
  change ((show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 : Γ(T, ⊤)) * (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 1).pt.1).2.1 1 =
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 0).pt.1).2.1 1
  refine Eq.trans ?_ e.symm
  rfl

end UpperTheory.Rel1
end

theorem UpperTheory.chernClass_pullback_blowupFirstLocus_eq_zero :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q1 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) = 0 := by
  intro q _ N E hE
  have hX : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hY : Inv q (Sp E (UpperTheory.Rel1.Ac N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX]
  exact UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ (UpperTheory.Rel1.ww E N) hY ⟨fun g x => UpperTheory.Rel1.triv1 E N g x, UpperTheory.Rel1.triv2 E N⟩
