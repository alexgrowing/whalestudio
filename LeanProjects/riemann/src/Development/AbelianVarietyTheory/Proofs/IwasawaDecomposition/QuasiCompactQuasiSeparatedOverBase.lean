import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GModMap

theorem quasiCompact_quasiSeparated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), π ≫ X.s = Z.s →
    QuasiCompact π ∧ QuasiSeparated π := by
  intro E _ _ _ H D l Xo c X Z π hπ
  have hX : IsProper X.s := GlobalTheory.SchemeWords.isProper_of_isProjOver X.proj
  have hZ : IsProper Z.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Z.proj
  have hc : IsProper (π ≫ X.s) := hπ ▸ hZ
  exact ⟨QuasiCompact.of_comp π X.s, QuasiSeparated.of_comp π X.s⟩

end GlobalTheory.GModMap
