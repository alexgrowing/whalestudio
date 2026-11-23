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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EqvTwistBlowupRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.BlowEqvInter

private theorem pb_sub (E : Spc) {a : Act} (Q R S : Pred a) (h1 : Q.Le R) (h2 : Q.Le S)
    (h : ∀ A x, R.P A x → S.P A x → Q.P A x) :
    IsPullback (Sp.map E (inclLe h1)) (Sp.map E (inclLe h2)) (Sp.map E (incl R)) (Sp.map E (incl S)) := by
  refine stackProduct_isPullback_of_actionPullback E (inclLe h1) (inclLe h2) (incl R) (incl S) ?_ ?_ ?_ ?_
  · intro A z
    rfl
  · intro A z
    rfl
  · intro A x y hxy
    have hy : S.P A x.1 := by
      have : (x.1 : a.D.obj A) = y.1 := hxy
      rw [this]
      exact y.2
    refine ⟨⟨x.1, h A x.1 x.2 hy⟩, ⟨rfl, ?_⟩, ?_⟩
    · exact Subtype.ext hxy
    · rintro z ⟨hz1, -⟩
      subst hz1
      rfl
  · intro A g k hgk
    refine ⟨g, ⟨rfl, hgk⟩, ?_⟩
    rintro z ⟨hz1, -⟩
    exact hz1

private theorem comm_sub (E : Spc) {a b : Act} (φ : Act.Hom a b) (Q R : Pred b) (h : Q.Le R)
    (h' : (Q.comap φ).Le (R.comap φ)) :
    Sp.map E (φ.sub Q) ≫ Sp.map E (inclLe h) = Sp.map E (inclLe h') ≫ Sp.map E (φ.sub R) := by
  rfl

end UpperTheory.BlowEqvInter

open UpperTheory.BlowEqvInter in
theorem UpperTheory.pullback_cube_faces_equiv_tate_twist :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (i : ℤ) (h₁ h₂), Inv q E →
        Eqv _ (pullback.map (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N))))
          (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) (Sp.map E ((βC N).sub (Q1 N))) (Sp.map E ((βC N).sub (Q2 N)))
          (Sp.map E (βC N)) h₁ h₂) (tw q i) := by
  intro q _ N E i h₁ h₂ hE
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hP := pb_sub E ((Q1 N).inf (Q2 N)) (Q1 N) (Q2 N) (fun A x hx => hx.1) (fun A x hx => hx.2)
    (fun A x ha hb => ⟨ha, hb⟩)
  have hP' := pb_sub E (((Q1 N).inf (Q2 N)).comap (βC N)) ((Q1 N).comap (βC N)) ((Q2 N).comap (βC N))
    (fun A x hx => hx.1) (fun A x hx => hx.2) (fun A x ha hb => ⟨ha, hb⟩)
  have hb := eqv_twist_blowupRestriction q N E ((Q1 N).inf (Q2 N)) i (fun A x hx => hx.2) hE
  have e : hP'.isoPullback.hom ≫ pullback.map _ _ _ _ _ _ _ h₁ h₂ =
      Sp.map E ((βC N).sub ((Q1 N).inf (Q2 N))) ≫ hP.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_fst]
      exact (comm_sub E (βC N) _ _ _ _).symm
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
        IsPullback.isoPullback_hom_snd]
      exact (comm_sub E (βC N) _ _ _ _).symm
  refine (hcomp _ _ _ hP'.isoPullback.hom _).2.1 (hiso _ _ hP'.isoPullback.hom inferInstance) ?_
  rw [e]
  exact (hcomp _ _ _ _ _).1 hb (hiso _ _ _ inferInstance)
