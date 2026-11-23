import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcDataClosedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_data_closed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)), Z.N4 → ∀ (T : CDVR) (b : 𝓞 c.F →+* T.V) (ϖ : T.V) (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) T.V b) (y : Sp T.V ⟶ Z.X), Irreducible ϖ → y ≫ Z.s = spMap b → Set.range (jK T.V ≫ y) ⊆ Set.range Z.j → Z.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y → y (closedPoint T.V) ∈ closure (genι Z '' (genBd Z : Set (gen Z))) := by
  first | exact @GlobalTheory.TorRef.closedPoint_mem_closure_genBd_of_arcData | exact GlobalTheory.TorRef.closedPoint_mem_closure_genBd_of_arcData | (intros; apply GlobalTheory.TorRef.closedPoint_mem_closure_genBd_of_arcData <;> assumption)
