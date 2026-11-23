import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuppFLocal
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.HeckeLevelFree

theorem ne_under_of_offS {D : D7} {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hQ : OffS D SF Q) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ SF) :
    v ≠ HeightOneSpectrum.under (𝓞 D.host.F) Q := by
  intro hvq
  obtain ⟨x, hx, hy⟩ := hQ v hv
  have hx' : x ∈ (HeightOneSpectrum.under (𝓞 D.host.F) Q).asIdeal := hvq ▸ hx
  have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Q.asIdeal := hx'
  refine hy (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ?_ hmem
  rfl

theorem rTup_eq_one {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hS : finE V g ∈ St β) : rTup β L (finE V g) = 1 := by
  have hproj : ∀ v ∈ SF, GlobalTheory.FinZeta.projV V v g = 1 := fun v hv =>
    (GlobalTheory.SuppLocal.suppF_local D V Q e f g hef hg).2 v (ne_under_of_offS hQ hv)
  funext PP
  obtain ⟨v, hv, hPv⟩ := hPg PP.1 PP.2
  have hu : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 ∈ SF := by
    have : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 = v := HeightOneSpectrum.ext hPv
    rw [this]; exact hv
  have hr := GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β SF hS hproj hu
  show upperLeftBlock L.hr (redFn β PP.1 (finE V g)) = 1
  rw [hr]; exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_and_chi {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) :
    g ∈ levS V β (withP L P') ∧ levChi V β (withP L P) g = levChi V β (withP L P') g := by
  obtain ⟨hG, hl⟩ := hJ
  have hpar : finE V g ∈ parLev D.sp.cm V.gram β (withP L P) := (mem_lev.1 hl).1
  have hS : finE V g ∈ St β := parLev_St hpar
  have h1 : rTup β L (finE V g) = 1 := rTup_eq_one β L hPg hQ hef hg hS
  refine ⟨⟨hG, mem_lev.2 ⟨hpar, ?_⟩⟩, ?_⟩
  · show rTup β L (finE V g) ∈ P'.H
    rw [h1]; exact Subgroup.one_mem _
  · unfold levChi
    rw [levFn_withP, levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]

theorem isHeckeOpFull_imp {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)) :
    Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp →
      Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  rintro ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, hK, hχ, h4, h5, h6, hR⟩
  have key := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) => mem_and_chi β L P P' hPg hQ hef hg hJ
  have key' := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P')) => mem_and_chi β L P' P hPg hQ hef hg hJ
  have hset : {k | k ∈ levS V β (withP L P) ∧ SuppF V f k} = {k | k ∈ levS V β (withP L P') ∧ SuppF V f k} := by
    ext k
    exact ⟨fun ⟨a, b⟩ => ⟨(key k b a).1, b⟩, fun ⟨a, b⟩ => ⟨(key' k b a).1, b⟩⟩
  refine ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, fun g hg => ?_, fun g hJ hg => ?_, h4, h5, h6, hset ▸ hR⟩
  · exact ⟨fun h => (hK g hg).1 ((key' g hg h).1), fun h => (key g hg ((hK g hg).2 h)).1⟩
  · have hJ0 := (key' g hg hJ).1
    rw [← (key g hg hJ0).2]
    exact hχ g hJ0 hg

theorem isHeckeOpFull_withP_iff : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))), (∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) → ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp ↔ Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  intro D V β L P P' SF hPg Q d Rp
  exact ⟨isHeckeOpFull_imp β L P P' SF hPg Q d Rp, isHeckeOpFull_imp β L P' P SF hPg Q d Rp⟩

end GlobalTheory.HeckeLevelFree
