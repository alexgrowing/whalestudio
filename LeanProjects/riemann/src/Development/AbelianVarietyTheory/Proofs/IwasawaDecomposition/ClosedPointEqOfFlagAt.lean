import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfFlagAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal

namespace GlobalTheory.LocM.FJ

theorem flagAt_bcField {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} (Z : Mdl Y i₀) {k k' : Type} [Field k] [Field k'] (s : k →+* k') {x : Sp k ⟶ Z.X}
    {v : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x v) : Z.FlagAt (spMap s ≫ x) (v.bc s) := by
  obtain ⟨a, φ, e, hfr, hfl⟩ := h
  refine ⟨a, s.comp φ, ?_, ?_, ?_⟩
  · rw [← e, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
  · have := GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ s _ _ hfr
    rw [Category.assoc]
    exact this
  · have := GlobalTheory.DRFlag.Spez.sameFlag_bc s hfl
    rw [Vecs.bc_bc] at this
    rwa [Category.assoc]

end GlobalTheory.LocM.FJ
