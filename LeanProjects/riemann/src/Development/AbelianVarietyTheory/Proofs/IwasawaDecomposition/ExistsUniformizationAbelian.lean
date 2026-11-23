import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem exists_pelUnif_torsionIso_subsingleton_of_abLocus {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (hR : IsCN R) (hpol : PolAt t (jK R))
    (hth : ThetaNZ t.G t.PP.L) (hab : ∀ x, x ∈ abLocus t.G) :
    ∃ P : PELUnif (maximalIdeal R) t, P.TorsionIso ∧ Subsingleton P.D.toPre.X := by
  obtain ⟨hn, hi, hc, hz⟩ := hR
  obtain ⟨l1, l2, l3, l4, l5, -⟩ := GlobalTheory.allSixLaws
  have hadm := GlobalTheory.isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hn hi hc
  have hpir : IsPrincipalIdealRing (R ⧸ maximalIdeal R) := by
    letI := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨P, hP⟩ := LN.UnifPrime.exists_pelUnif l1 l2 l3 l4 l5 LN.ega_holds uniformisation_dvr_unconditional
    LN.pelSt_holds E H R _ hadm hpir t hpol (GoodTrait.splitOver_of_abLocus t.G t.semi hab) hth
  refine ⟨P, hP, ?_⟩
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (R ⧸ maximalIdeal R ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (CartesianMonoidalCategory.toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick R (maximalIdeal R) 0) p (hab _)
    P.D.toPre.X g.i g.i_hom

end GlobalTheory.GenFan
