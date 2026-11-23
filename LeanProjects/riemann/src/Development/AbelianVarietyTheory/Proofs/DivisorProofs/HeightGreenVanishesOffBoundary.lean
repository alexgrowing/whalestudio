import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeightParts

theorem zero_psi_of_not_mem_offBd : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N)
    (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∉ offBd O.Φ c σ → GlobalTheory.HeightParts.psi O x c σ τ i y = 0 := by
  intro D O x c σ τ i y hy
  simp only [offBd, Set.mem_setOf_eq, not_not] at hy
  have hL : LiesIn ((O.Φ.C c).down y) (Toroidal.genBd O.s.T.Z) := hy
  have hh : ∀ (n : Pad.Letter O.S.Dw → ℤ) (a : (O.Φ.C c).Y.Fnˣ),
      (metsOf x O.Φ c none σ n).h a y = (refMet x O.Φ c σ n).h a y := fun n a =>
    FlagCpt.met_congr _ n (fun g τ' => x.hodge_gram_of_liesIn hL g τ') a
  have hr : ∀ (n : Pad.Letter O.S.Dw → ℤ),
      lnRatio (metsOf x O.Φ c none σ n) (refMet x O.Φ c σ n) y = 0 := fun n => by
    simp only [lnRatio, lnN]
    show Real.log (ProjVar.Var.pn _ σ _ _ _ y) / 2 - Real.log (ProjVar.Var.pn _ σ _ _ _ y) / 2 = 0
    simp only [ProjVar.Var.pn, hh]
    ring
  simp only [psi, phW, hr, mul_zero, Finset.sum_const_zero]

end GlobalTheory.HeightParts

end
