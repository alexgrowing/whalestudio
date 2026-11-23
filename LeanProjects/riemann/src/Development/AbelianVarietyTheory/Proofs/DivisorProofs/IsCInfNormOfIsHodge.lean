import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDualRiemann
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRiemannDataPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCInfOfIsDualRiemann
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.PPAS

theorem isCInfNorm_of_isHodge {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (P : PPAS X)
    {h : VMetric p (LieVB.omega P.A) P.g} (H : P.IsHodge h) : h.IsCInfNorm := by
  intro Y π hs
  obtain ⟨P', φ, hg, hpull⟩ := GlobalTheory.PPAS.exists_pull X Y P π
  obtain ⟨hφ, -⟩ := id hpull
  obtain ⟨h', H'⟩ := GlobalTheory.PPAS.exists_isDualRiemann k Y (π ≫ p) P' Real.pi Real.pi_pos
  have hc := GlobalTheory.HodgeSmooth.isCInf_of_isDualRiemann k Y (π ≫ p) 1 hs P' Real.pi Real.pi_pos h' H'
  have hf := GlobalTheory.HodgePull.form_omegaBase k X p Y (π ≫ p) π rfl P P' φ hφ hg hpull Real.pi h h' H H'
  clear H'
  revert h' hc hf
  generalize P'.g = r at *
  subst hg
  intro h' hc hf
  have e : h'.IsIsometry (h.pull π rfl) (asIso (LieVB.omegaBase hφ)).symm := by
    intro σ V s t y hy
    have := hf σ V ((inv (LieVB.omegaBase hφ)).app V s) ((inv (LieVB.omegaBase hφ)).app V t) y hy
    simp only [Iso.symm_hom, asIso_inv]
    rw [← this]
    congr 1
    · exact (congr(($(IsIso.inv_hom_id (LieVB.omegaBase hφ))).app V s) :)
    · exact (congr(($(IsIso.inv_hom_id (LieVB.omegaBase hφ))).app V t) :)
  rw [(VMetric.isIsometry_iff _).1 e]
  exact hc.map _

end GlobalTheory.PPAS
