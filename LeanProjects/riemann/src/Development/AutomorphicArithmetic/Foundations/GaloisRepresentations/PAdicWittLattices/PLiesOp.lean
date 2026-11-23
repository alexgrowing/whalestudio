import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pLiesOp :
    LiesGen → LiesAbs.{u} → LiesOp.{u} := by
  intro hGen hAbs k L O _ _ _ _ H θ C g D s t hst m d hL hd R _ T hT tr trg htr htrg x
  obtain ⟨κ, h, hκt, hfet⟩ := hGen C g s t hst m hL
  exact hAbs T hT _ _ _ _ (piK C) (piK_snd C) (H.s g) (H.t g) (H.comm g) _ _
    (bcMap_snd _ _ _) κ h d m rfl (bcMap_snd _ _ _) hκt hd hfet tr trg htr htrg x
