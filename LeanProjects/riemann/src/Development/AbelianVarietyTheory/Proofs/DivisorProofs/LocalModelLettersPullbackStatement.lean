import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelLettersPullback
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
theorem _root_.GlobalTheory.T.local_model_letters_pullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : GlobalTheory.Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ} (x x' : Fin r → Letter Dw) (Lie Om : AM B (𝓞 E)) (sL : ∀ a : Fin Z.m, Fin r → Γ(Lie.V, h ⁻¹ᵁ (Z.U a).1)) (hL : ∀ a, GlobalTheory.VB.IsFrame (sL a)) (sO : ∀ a : Fin Z.m, Fin r → Γ(Om.V, h ⁻¹ᵁ (Z.U a).1)) (hO : ∀ a, GlobalTheory.VB.IsFrame (sO a)) (n o : ℕ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (C : ChainsBp p n o Lie Om π γ) (X' : Scheme.{0}) (f : X' ⟶ B.X) (Q₁ Q₂ : X'.Modules) (j' : (Scheme.Modules.pullback f).obj Lie.V ⟶ Q₁) (ρ' : (Scheme.Modules.pullback f).obj Om.V ⟶ Q₂) (hL' : ∀ a, GlobalTheory.VB.IsFrame (pullS f sL a)) (hO' : ∀ a, GlobalTheory.VB.IsFrame (pullS f sO a)), GlobalTheory.VB.IsVB Lie.V r → GlobalTheory.VB.IsVB Om.V r → SysPt Z h x x' hL hO C → KerMatch C f j' ρ' → PtJ Z (f ≫ h) x hL' (f.appTop π) j' ∧ PtR Z (f ≫ h) x' hO' ρ' := by
  first | exact @GlobalTheory.ChainPts.PtDesc.ptJ_ptR_of_kerMatch | exact GlobalTheory.ChainPts.PtDesc.ptJ_ptR_of_kerMatch | (intros; apply GlobalTheory.ChainPts.PtDesc.ptJ_ptR_of_kerMatch <;> assumption)
