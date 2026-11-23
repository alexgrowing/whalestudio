import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecDivNonzeroLocusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDetLieEigenpartsToroidalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
namespace GlobalTheory.LogCanon

theorem exOf_kapBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) :
    (fun ix : Ix Dw => Option.elim ix 0 fun x =>
      (fun τ : E →+* ℂ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) x.1) =
      AllWt.exOf Dw (kapBase Dw) 0 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · by_cases h' : τ (H.rt : E) = H.rt0
    · have hi : (i : ℕ) < Dw.p := by
        have := i.2; simp only [Datum.mult, if_pos h'] at this; exact this
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_pos h', dif_pos h', dif_pos hi, kapBase, sub_zero,
        if_pos hi]
    · have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg h'] at this; exact this
      have hc : conjEmb τ (H.rt : E) = H.rt0 := by
        have := (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H τ).resolve_left h'
        unfold InPsi at this
        rw [ComplexEmbedding.conjugate_coe_eq] at this
        exact this
      have hn : ¬ (Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p) := by omega
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_neg h', dif_neg h', dif_pos hc, dif_pos hi, kapBase,
        if_neg hn, neg_neg, sub_zero]

theorem exists_kap_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hF _ K
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  obtain ⟨φ₀, f₀, hgen, hdiv⟩ := GlobalTheory.T.exists_cartierDivisor_det_lieEigenparts_toroidal E H Dw l Xo c TF Z
  obtain ⟨D, hpull, hD⟩ := hdiv fun τ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [exOf_kapBase Dw] at hpull
    exact hpull
  · obtain ⟨i₀, hi₀⟩ : ∃ i, genericPoint (X₀ TF.Y Z) ∈ K.bundle.U i :=
      Opens.mem_iSup.1 (K.isLB.cover.ge (Set.mem_univ _))
    have hP := presents_ofLB K.isLB i₀ hi₀
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent E H Dw l Xo c TF Z hpq hF K _ _ hP φ₀ f₀ hgen D hD
    exact GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq D _ K.bundle _ hP _ h hh
end GlobalTheory.LogCanon
