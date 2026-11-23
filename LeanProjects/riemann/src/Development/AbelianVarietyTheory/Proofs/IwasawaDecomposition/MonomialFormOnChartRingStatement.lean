import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_form_on_chart_ring : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (_ : SABMap tC Y.t (ξ ≫ genι Y)) (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X), IsMonomial PC.D.toPre (bdParam k m e) γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (ϖ : W), Irreducible ϖ → ∀ (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∀ (be : LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ϖ' : V), Irreducible ϖ' → ∀ (f : W →+* V) (ψ : ChartRing k m e →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y → ∀ (r : ℕ) (u : Vˣ), f ϖ = u * ϖ' ^ r → ∀ (n : Fin m → ℕ) (v : Fin m → Vˣ), (∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) → ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) := by
  first | exact @GlobalTheory.TraitChartForm.main | exact GlobalTheory.TraitChartForm.main | (intros; apply GlobalTheory.TraitChartForm.main <;> assumption)
