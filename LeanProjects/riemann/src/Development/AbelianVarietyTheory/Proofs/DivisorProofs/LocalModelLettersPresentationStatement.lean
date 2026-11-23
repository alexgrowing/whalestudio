import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelLettersPresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_letters_presentation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
  (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (oo : EPres B (𝓞 E)) (π : Γ(B.X, ⊤)) (u : oo.E ⟶ oo.E'),
  u ≫ oo.ψ = smulA _ π → IsEqLatPres Z h (fun k => x k.rev) true oo →
    ∃ (lw : EPres B (𝓞 E)) (wl : lw.E ⟶ lw.E'), lw.ψ ≫ wl = smulA _ π ∧ IsEqLatPres Z h x false lw := by
  first | exact @GlobalTheory.ChainPts.DualPres.exists_dual_pres | exact GlobalTheory.ChainPts.DualPres.exists_dual_pres | (intros; apply GlobalTheory.ChainPts.DualPres.exists_dual_pres <;> assumption)
