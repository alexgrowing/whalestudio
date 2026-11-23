import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow

namespace GlobalTheory.TowVal

theorem bddAll_one_iff_valSet_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (f : Rul Xo c), GlobalTheory.GoodPts.BddAll Xo c la 1 f ↔ ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c la f
  constructor
  · rintro h _ ⟨⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩, rfl⟩
    have h1 := h T io e ho y hy
    rw [map_one, one_mul] at h1
    exact (GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1 _).1 h1
  · intro h T io e ho y hy
    rw [map_one, one_mul, GlobalTheory.GoodPtsModel.inV_iff_nval T ho.1]
    exact h _ ⟨PtV.mk la ho y hy () trivial, rfl⟩

end GlobalTheory.TowVal
