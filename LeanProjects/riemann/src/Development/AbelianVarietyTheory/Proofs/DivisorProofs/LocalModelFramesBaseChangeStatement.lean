import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelFramesBaseChange
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
theorem _root_.GlobalTheory.T.local_model_frames_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {X X' : Scheme.{0}} (g : X' ⟶ X) (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (F Q : X.Modules) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) (hs' : ∀ a, GlobalTheory.VB.IsFrame (pullS g s a)) (u : F ⟶ Q) (Q' : X'.Modules) (u' : (Scheme.Modules.pullback g).obj F ⟶ Q') (e : Q' ≅ (Scheme.Modules.pullback g).obj Q), GlobalTheory.VB.IsVB F r → u' ≫ e.hom = (Scheme.Modules.pullback g).map u → (∀ π : Γ(X, ⊤), PtJ Z h x hs π u → PtJ Z (g ≫ h) x hs' (g.appTop π) u') ∧ (PtR Z h x hs u → PtR Z (g ≫ h) x hs' u') := by
  first | exact @GlobalTheory.ChainPts.PtPull.pt_pull | exact GlobalTheory.ChainPts.PtPull.pt_pull | (intros; apply GlobalTheory.ChainPts.PtPull.pt_pull <;> assumption)
