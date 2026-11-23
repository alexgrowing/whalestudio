import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

theorem exists_torsionTower : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (p : ℕ) [Fact p.Prime], IsProper t.G.hom → ∃ GG : PDivGroup p k, Nonempty (GG.TorsionTower t.G) := by
  intro E _ _ _ H k _ _ _ t p hp hP
  have hA : IsAbelianScheme t.G :=
    { comm := t.comm, smooth := t.semi.smooth, proper := hP, geomConnected := t.semi.geomConnected }
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k t.G hA
  obtain ⟨G, -, h⟩ := GlobalTheory.AbelianPDiv.exists_pDivGroup p k (Nat.cast_ne_zero.2 hp.out.ne_zero) t.G hA g hg
  exact ⟨G, h⟩

end GlobalTheory.GroupBplus.Closed
