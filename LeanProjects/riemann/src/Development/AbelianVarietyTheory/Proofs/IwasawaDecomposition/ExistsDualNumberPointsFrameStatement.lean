import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDualNumberPointsFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_number_points_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), SABMap Y'.t Y.t v → ∀ (M : MChart Y) (U' : Y'.X.Opens) (hU' : IsAffineOpen U'), U' ≤ v ⁻¹ᵁ M.U → ∃ (k : ℕ) (v₀ : Fin k → (Sp (DualNumber Γ(Y'.X, U')) ⟶ Y'.t.G.left)) (ρ : 𝓞 E → Matrix (Fin k) (Fin k) Γ(Y'.X, U')), ∀ (R' : Type) [CommRing R'] (f : Γ(Y'.X, U') →+* R') (t' : SAB H (Sp R')) (m : SABMap t' Y'.t (spMap f ≫ hU'.fromSpec)), ∃ v' : Fin k → (epsR R' ⟶ t'.G), (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧ ∀ a j, IsLieComb (fun i => f (ρ a i j)) v' (v' j ≫ t'.act.act a) := by
  first | exact @GlobalTheory.MChartDown.lieDown | exact GlobalTheory.MChartDown.lieDown | (intros; apply GlobalTheory.MChartDown.lieDown <;> assumption)
