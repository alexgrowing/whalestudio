import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainFrameHasDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_domain_frame_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀), HasDR Z → ∀ z : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(Z.X, U)) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), z ∈ U ∧ IsIntegrallyClosed Γ(Z.X, U) ∧ Function.Injective β ∧ IntFrame Z hU w ∧ GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e ∧ spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  first | exact @GlobalTheory.HTLine.exists_small_chart | exact GlobalTheory.HTLine.exists_small_chart | (intros; apply GlobalTheory.HTLine.exists_small_chart <;> assumption)
