import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelChainCharP
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
theorem _root_.GlobalTheory.T.local_model_chain_char_p : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [CharP (ResidueField O) p] {B : GlobalTheory.Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (lw : EPres B (𝓞 E)) (wl : lw.E ⟶ lw.E') (π : Γ(B.X, ⊤)) (P₁ P₃ : Pres B) (j : lw.E'.V ⟶ P₁.mod) (hj : wl.hom ≫ j = 0) (s : ∀ a : Fin Z.m, Fin r → Γ(lw.E'.V, h ⁻¹ᵁ (Z.U a).1)) (hs : IsEqLat Z h x false lw.E' s), lw.r = r → IsRootOfP p π (p - 1) → lw.ψ ≫ wl = smulA _ π → Mono wl.hom → (ShortComplex.mk wl.hom j hj).Exact → Nonempty (cokernel j ≅ P₃.mod) → PtJ Z h x hs.2.2.1.frame π j → IsEqLatPres Z h x false lw := by
  first | exact @GlobalTheory.ChainPts.LatLie.isEqLatPres_of_ptJ | exact GlobalTheory.ChainPts.LatLie.isEqLatPres_of_ptJ | (intros; apply GlobalTheory.ChainPts.LatLie.isEqLatPres_of_ptJ <;> assumption)
