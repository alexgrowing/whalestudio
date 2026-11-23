import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.embAll_of :
    UpperTheory.Gal.W2.EmbAll := by
  intro p _ G τ
  rcases HTGroupOver.liesOver_or_conj p G τ with h | h
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ h
    refine ⟨i, σ, Or.inl fun x => ?_⟩
    rw [hσ]
    rfl
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ h
    refine ⟨i, σ, Or.inr fun x => ?_⟩
    have hx := congrArg (fun f : G.F →+* PadicAlgCl p => f (IsCMField.complexConj G.F x)) hσ
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      conjQ_apply] at hx
    have hc : (conjQ G.F).toRingHom ((IsCMField.complexConj G.F) x) = x := by
      simp [conjQ_apply]
    rw [hc] at hx
    exact hx
