import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelChainCharPDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_chain_char_p_dual : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [CharP (ResidueField O) p] {B : GlobalTheory.Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (oo : EPres B (𝓞 E)) (Q : B.X.Modules) (ρ : oo.E.V ⟶ Q) (hρ : oo.ψ.hom ≫ ρ = 0) (s : ∀ a : Fin Z.m, Fin r → Γ(oo.E.V, h ⁻¹ᵁ (Z.U a).1)) (hs : IsEqLat Z h x true oo.E s), oo.r = r → Epi ρ → (ShortComplex.mk oo.ψ.hom ρ hρ).Exact → PtR Z h x hs.2.2.1.frame ρ → IsEqLatPres Z h x true oo := by
  first | exact @GlobalTheory.ChainPts.KerOm.isEqLatPres_of_ptR | exact GlobalTheory.ChainPts.KerOm.isEqLatPres_of_ptR | (intros; apply GlobalTheory.ChainPts.KerOm.isEqLatPres_of_ptR <;> assumption)
