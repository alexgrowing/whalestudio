import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTangentOfIsLieImage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.Mum.Two.HomConst

theorem map_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (ψ : G ⟶ G) :
    ((Over.pullback (thick R I e)).map ψ).left ≫ (fstG I e G).left = (fstG I e G).left ≫ ψ.left := by
  simp [fstG, pullback.lift_fst]

end GlobalTheory.Mum.Two.PullLin

open GlobalTheory.Mum.Two.PullLin GlobalTheory.Mum.Two.HomConst in

theorem GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (ψ : G ⟶ G) (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (b : D'.toPre.P.A ⟶ D.toPre.P.A), IsMonHom ψ → bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.left → hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = b.left → IsPullUnif (RingHom.id R) hD bc U U' → Over₀ U'.toUnifPre U.toUnifPre ψ b ∧ OnTorus U'.toUnifPre U.toUnifPre ψ hD.xe.symm := by
  intro R _ _ _ hB D A G _ _ hG U D' A' U' hD ψ bc b hψ hbc hb hP
  obtain ⟨hR, -⟩ := hB
  obtain ⟨wL, -, he, -, hlev⟩ := hP.lg

  have lev : ∀ e, ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h = ((Over.pullback (thick R (maximalIdeal R) e)).map ψ).left ∧
      (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        h ≫ (U.gt e).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt e).pG) x k ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            h ≫ D.toPre.Oφ ((U.gt e).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt e).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) h _
            Oinvε _ hψ ((U.gt e).t (hD.xe x)))) := by
    intro e
    obtain ⟨h, h1, h2, h3, -⟩ := hlev e
    have : Mono (fstG (maximalIdeal R) e G).left :=
      inferInstanceAs (Mono (pullback.fst G.hom (thick R (maximalIdeal R) e)))
    refine ⟨h, (cancel_mono (fstG (maximalIdeal R) e G).left).1 ?_, h2, h3⟩
    rw [h1, hbc, map_fstG]
  refine ⟨fun e => ?_, ?_⟩
  · obtain ⟨h, rfl, h2, -⟩ := lev e
    have : Mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) := inferInstance
    refine Over.OverMorphism.ext ((cancel_mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))).1 ?_)
    rw [hb] at h2
    clear lev hlev hP wL he
    simp only [Over.comp_left, Category.assoc]
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · show (U'.gt e).q.left ≫ pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ b.left = _
      congr 1
      exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨-, -, -, hC⟩ := id hR
    obtain ⟨h₀, hT⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R (maximalIdeal R) hR D' D A' A G G U'.toUnifPre
      U.toUnifPre ψ hψ
    have key : (h₀ : D.toPre.X → D'.toPre.X) = hD.xe.symm := by
      haveI := hC
      obtain ⟨t, ht, hi⟩ := hT 0
      refine acts_unique (U'.gt 0) (U.gt 0) (acts_of_torusHomOf _ _ _ ht hi) ?_
      obtain ⟨h, rfl, -, h3⟩ := lev 0
      clear lev hlev hP wL he hT ht hi
      intro Z r z J₁ J₂ hJ₁ hJ₂ c χ
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [AddEquiv.symm_apply_apply]
      obtain ⟨hψk, M⟩ := h3 x
      have P := (maps_iff hD.w _ _ Oinvε _ _ _ _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψk ·) (fun _ => rfl)).1 M
      have e := P Z r z
        (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
          pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
        (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => hJ₂ _) (fun k => hJ₁ _)
      have h1 := GlobalTheory.ArcLieCompare.prod_Oφ_zero (D := D'.toPre) (U'.gt 0).pG r
        (r ≫ (fstG (maximalIdeal R) 0 G).left ≫ G.hom) (c.trans (by simp only [Category.assoc])) x
        (fun f => gw hD.w f z (J₂ (f ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) (J₁ f))
      rw [h1, _root_.one_mul] at e
      rw [val_of _ _ z J₂
          (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
          (fun k => by simp only [Category.assoc, hψk k]),
        val_of _ r z J₁ (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => rfl)]
      exact e
    rw [key] at hT
    exact hT
