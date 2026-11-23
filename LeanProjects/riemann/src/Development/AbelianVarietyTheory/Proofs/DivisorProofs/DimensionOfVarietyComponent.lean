import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimEqDimGrAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbBBijective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagEigDim

theorem rkB_eq_mult {D : D7} (O : Setup D) (a : D.what₂.Tau × Bool) :
    rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a) := by
  have hp := O.S.p_eq
  have hq := O.S.rank_eq
  obtain ⟨t, _ | _⟩ := a
  · change O.N - O.j = O.S.Dw.mult (conjEmb (DV.tauEmb D t))
    rw [Datum.mult, if_neg (GlobalTheory.Proof.LetterConjugation.conj_ne (Amb.cm _ t))]
    omega
  · change O.j = O.S.Dw.mult (DV.tauEmb D t)
    rw [Datum.mult, if_pos (Amb.cm _ t), hp]

theorem dim_eq_dimGr_add_sum : ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp,
    dimGr D.what₂.Tau O.N O.j + ∑ σ : D.host.E →+* ℂ, O.S.Dw.mult σ * (O.S.Dw.mult σ - 1) / 2 = (O.var c).dim := by
  intro D O _ c
  rw [← GlobalTheory.FlagBlockDim.dim_eq_dimGr_add O c]
  congr 1
  refine (Fintype.sum_bijective (embB D) (GlobalTheory.FlagCls.embB_bijective D) _ _ fun a => ?_).symm
  rw [rkB_eq_mult O a]

end GlobalTheory.FlagEigDim

end
