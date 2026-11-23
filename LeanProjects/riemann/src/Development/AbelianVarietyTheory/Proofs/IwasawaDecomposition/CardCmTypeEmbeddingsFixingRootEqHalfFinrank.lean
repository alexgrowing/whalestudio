import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.CMTypeCard

theorem card_psi_eq_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H
  let e : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ GlobalTheory.AllWt.Psi H :=
    { toFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have h1 : Fintype.card (E →+* ℂ) =
      Fintype.card (GlobalTheory.AllWt.Psi H) + Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).symm
  have h2 : Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} = Fintype.card (GlobalTheory.AllWt.Psi H) :=
    Fintype.card_congr e
  rw [← NumberField.Embeddings.card E ℂ, h1, h2]
  omega

end GlobalTheory.CMTypeCard
