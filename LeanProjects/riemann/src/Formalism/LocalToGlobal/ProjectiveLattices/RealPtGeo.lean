import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.ExtPtUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem intFr_of_model (hIF : IntFramesSt Xo c) (T : CDVR) (io : c.F →+* T.Fr) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (hPI : PushInvertible Y.t.G Y.t.PP.L) (b : O →+* T.V)
    (hb : (algebraMap T.V T.Fr).comp b = io.comp β) (y₀ : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), (letI := io.toAlgebra; FrBor t y₀ y.1) := by
  letI := io.toAlgebra
  have e1 : y₀.x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y₀.x_over]
    exact spMap_comp _ _
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Sp T.Fr ⟶ pullback Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom),
      z ≫ pullback.fst _ _ = y₀.x ∧ z ≫ pullback.snd _ _ = spMap io :=
    ⟨pullback.lift y₀.x (spMap io) e1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have e3 : Out.jK T.V = spMap (algebraMap T.V T.Fr) := rfl
  have e4 : Y.j = Y.jQ ≫ pullback.fst _ _ := rfl
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    rw [e4, e3, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hz2,
      ← spMap_comp, ← spMap_comp, hb]
  obtain ⟨yt, hyt1, -⟩ := extPt Y T b z hx
  exact hIF T io O β Y hPI yt z (by rw [← hyt1, e3]) hz2 y₀ hz1.symm

def ModelAtSt (Xo : Moduli Dw l) (c : Coeff l) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (Y : Model Xo c β), Y.N3 ∧ PushInvertible Y.t.G Y.t.PP.L ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β

end Formalism.L2.Pj
