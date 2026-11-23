import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.N.K.Topo

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem topoHyps
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (u : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) :
    letI := fracTopology (D.nd.O i); letI := rTopology (D.nd.O i) Dd.R';
    Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) ∧ PadicCoeff (D.nd.l i) (D.nd.O i) ∧
      FracTop (D.nd.O i) ∧ IsFGTop (D.nd.O i) Dd.R' ∧ IsCycG (D.nd.l i) (epsU D.nd i) ∧
      (Continuous fun g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) => uElt Dd.r Dd.χ g) ∧
      (∀ v, IsPlaceOver (Formalism.MainNotions.N.K.Av (D := D) v) v) ∧
      (D.nd.l i ≠ 2 ∨ InfinitePlace.nrRealPlaces D.host.E = 0) ∧
      1 ≤ D.nd.s0 i ∧ (D.nd.l i = 2 → 2 ≤ D.nd.s0 i) ∧
      ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) - 1 =
        ((D.nd.l i : ℕ) : D.nd.O i) ^ D.nd.s0 i * ((yU i u : (D.nd.O i)ˣ) : D.nd.O i) ∧
      (∀ w ∈ Formalism.MainNotions.N.K.rowsN i dc, (Formalism.MainNotions.N.K.Aw i dc w).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 ∧
        IsPlaceOver (Formalism.MainNotions.N.K.Aw i dc w) (Formalism.MainNotions.N.K.plOf i dc w)) := by
  refine ⟨?_, padicCoeff_O i, fracTop_O i, fgTop_RD i r π g0 eB e₁ s Dd hD, ?_, uElt_cont i r π g0 eB e₁ s Dd hD hc,
    av_over, ?_, one_le_localLevel i, restNLevelExponent_of_two i, ?_, rows_over i dc⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 : algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((PadicInt.unitCoeff h0 : ℤ_[D.nd.l i]) * (D.nd.l i : ℤ_[D.nd.l i]) ^ x.valuation) = 0 := by
      rw [← PadicInt.unitCoeff_spec h0]
      exact hx
    rw [map_mul, map_pow, map_natCast] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))).ne_zero h
    · exact (padicCoeff_O i).p_ne (pow_eq_zero_iff'.mp h).1
  · apply isCyc_eps <;> assumption
  · apply l_or_noReal <;> assumption
  · have h2 : ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) := rfl
    rw [h2, hcyc]
    simp [yU]

end Formalism.MainNotions.N.K.Topo

end
