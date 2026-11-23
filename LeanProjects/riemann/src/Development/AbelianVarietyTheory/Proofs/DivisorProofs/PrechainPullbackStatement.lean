import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechainPullback
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
theorem _root_.GlobalTheory.T.prechain_pullback : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B' : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B' B) (Λ : Type) [CommRing Λ] (o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (P : PreChain p o Lie Om π), ∃ (P' : PreChain p o ((pullA g.f).obj Lie) ((pullA g.f).obj Om) (g.f.appTop π)) (e : (P'.q 0).mod.V ≅ (Scheme.Modules.pullback g.f).obj (P.q 0).mod.V) (e' : (cokernel P'.j).V ≅ (Scheme.Modules.pullback g.f).obj (cokernel P.j).V), P'.j.hom ≫ e.hom = (Scheme.Modules.pullback g.f).map P.j.hom ∧ P'.ρ.hom ≫ e'.hom = (Scheme.Modules.pullback g.f).map P.ρ.hom := by
  first | exact @GlobalTheory.ChainPts.PrePull.preChain_pull | exact GlobalTheory.ChainPts.PrePull.preChain_pull | (intros; apply GlobalTheory.ChainPts.PrePull.preChain_pull <;> assumption)
