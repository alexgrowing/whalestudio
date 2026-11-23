import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrArcOutsideAbelianLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_arc_outside_abelian_locus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Z.X), x ∉ abLocus Z.t.G → ∃ (T : CDVR) (b : 𝓞 c.F →+* T.V) (io : c.F →+* T.Fr) (y : Sp T.V ⟶ Z.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp (algebraMap (𝓞 c.F) c.F) ∧ y ≫ Z.s = spMap b ∧ z ≫ pullback.snd _ _ = spMap io ∧ z ≫ Z.j = spMap (algebraMap T.V T.Fr) ≫ y ∧ y (closedPoint T.V) = x := by
  first | exact @GlobalTheory.HorizTrait.exists_trait_of_not_mem_abLocus | exact GlobalTheory.HorizTrait.exists_trait_of_not_mem_abLocus | (intros; apply GlobalTheory.HorizTrait.exists_trait_of_not_mem_abLocus <;> assumption)
