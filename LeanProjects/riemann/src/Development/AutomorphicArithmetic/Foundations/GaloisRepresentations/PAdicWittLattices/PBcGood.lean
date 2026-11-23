import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pBcGood :
    BcSplits → BcGal → BcGood.{u} := by
  intro hS hG B B' R _ T g hT
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have ha : ∀ x, a x ≫ r = r := fun x => by
      rw [← hc, ← Category.assoc, hgal.2.2.2.2.2.1 x]
    exact hT.inj (pullback.snd p g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) G
      (fun x => bcMap g (a x) (ha x)) (hG g p r c hc G a ha hgal)
  · intro Z Y p q s _ _ hs
    obtain ⟨hfin, het, -⟩ := hS g p q q s hs s hs Empty Empty.elim (fun j => j.elim)
    obtain ⟨tr, htr⟩ := hT.tr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) (bcMap_snd g s hs)
    refine ⟨tr, ?_⟩
    intro W r c hc J _ σ hσ hspl x
    exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
      (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j))
      ((hS g p q r s hs c hc J σ hσ).2.2 hspl) x
