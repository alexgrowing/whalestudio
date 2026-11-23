import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHCut

noncomputable section

open MeasureTheory Formalism.MainNotions.S

namespace Formalism.L2.SG.PoincareInHH.Cut

theorem isFundamentalDomain_of_isFundDom (I : AutInst) (μ : Measure I.GA) [μ.IsMulLeftInvariant]
    (fund : Set I.GA) (h : I.IsFundDom μ fund) :
    IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund μ := by
  obtain ⟨hmeas, hcov, hdisj⟩ := h
  refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    obtain ⟨γ, hγ, hy⟩ := hcov y
    exact ⟨⟨γ, hγ⟩, hy⟩
  · intro g hg
    have hg' : (g : I.GA) ≠ 1 := fun h1 => hg (Subtype.ext h1)
    exact hdisj (g : I.GA) g.2 hg'
  · intro g
    exact (measurePreserving_mul_left μ (g : I.GA)).quasiMeasurePreserving

end Formalism.L2.SG.PoincareInHH.Cut
