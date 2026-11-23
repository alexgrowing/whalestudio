import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrDegenerationUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_degeneration_uniformization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Y.X), 1 ≤ D.p + D.q → x ∉ abLocus Y.t.G → ∃ (T : Formalism.L2.Pj.CDVR) (σ : T.V →+* ℂ) (y : Sp T.V ⟶ Y.X) (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t) (ρ : ℂ), Function.Injective σ ∧ y (closedPoint T.V : Sp T.V) = x ∧ Nontrivial P.D.toPre.X ∧ ρ ^ 2 = -(H.d : ℂ) ∧ ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult t.act (spMap σ) τ D.p) ∧ (τ H.rt ≠ ρ → LieMult t.act (spMap σ) τ D.q) := by
  first | exact @GlobalTheory.SmallTrait.exists_unif_trait_complex | exact GlobalTheory.SmallTrait.exists_unif_trait_complex | (intros; apply GlobalTheory.SmallTrait.exists_unif_trait_complex <;> assumption)
