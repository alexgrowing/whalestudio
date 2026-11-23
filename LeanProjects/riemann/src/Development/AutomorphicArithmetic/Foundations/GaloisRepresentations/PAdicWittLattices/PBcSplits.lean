import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem bc_isPullback {B B' Z Y : Scheme.{0}} (g : B ⟶ B') (p : Z ⟶ B') (s : Y ⟶ Z) :
    IsPullback (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) := by
  refine IsPullback.of_bot ?_ (bcMap_fst g s rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (s ≫ p) g

theorem UpperTheory.Gal.G3.pBcSplits :
    SplitsBasic → BcSplits := by
  intro hb B B' Z Y W g p q r s hs c hc J _ σ hσ _ _
  subst hs
  subst hc
  have sq := bc_isPullback g p s
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›,
    MorphismProperty.of_isPullback (P := @Etale) sq ‹_›, fun h => ?_⟩
  obtain ⟨h0, -⟩ := id h
  have hcomp : ∀ j, bcMap g (σ j) (hσ j) ≫ bcMap g s rfl = bcMap g c rfl := by
    intro j
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst g s rfl, ← Category.assoc, bcMap_fst g (σ j) (hσ j), Category.assoc, h0 j,
        bcMap_fst g c rfl]
    · rw [Category.assoc, bcMap_snd g s rfl, bcMap_snd g (σ j) (hσ j), bcMap_snd g c rfl]
  have e1 : bcMap g c rfl ≫ pullback.fst p g = pullback.fst (c ≫ p) g ≫ c := bcMap_fst g c rfl
  have e2 : (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) = fun j => pullback.fst (c ≫ p) g ≫ σ j :=
    funext fun j => bcMap_fst g (σ j) (hσ j)
  have h2 : Splits s (bcMap g c rfl ≫ pullback.fst p g)
      (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) := by
    rw [e1, e2]
    exact hb.1 s c J σ (pullback.fst (c ≫ p) g) h
  exact (hb.2 (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) sq (bcMap g c rfl) J
    (fun j => bcMap g (σ j) (hσ j)) hcomp).2 h2
