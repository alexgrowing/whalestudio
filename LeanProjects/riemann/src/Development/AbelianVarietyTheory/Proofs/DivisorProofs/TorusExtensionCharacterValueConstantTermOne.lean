import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GermDerivationUniformisedAbelianVarietyUniqueVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
noncomputable section
namespace GlobalTheory.MBLow.Cl

theorem fst_vE_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  intro R _ _ D _ N ν gm ⟨o, hz, hp⟩ χ
  have hJ : Good D.P.L (IsLocalRing.closedPoint ℂ) ν.J := fun ψ => ν.good ψ trivial
  have hm : redE ℂ (IsLocalRing.closedPoint ℂ) ∈ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    simpa only [Category.id_comp] using hJ.mem (DegPre.gtφT D (TE R ℂ) gm.b χ) (redE ℂ)
  have h : ⊤ ≤ (𝟙 (Sp (DualNumber ℂ))) ⁻¹ᵁ LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) := by
    refine (GlobalTheory.KS.TangentAt.top_le_iff_dual _ _).2 ((GlobalTheory.ZH.CrdCalc.top_le_iff _ _).2 ?_)
    rw [Category.comp_id]
    exact hm
  have e1 : valR (redE ℂ ≫ 𝟙 (Sp (DualNumber ℂ))) (LB.wchart D.P.L (DegPre.gtφT D (TE R ℂ) gm.b χ)
      (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)))
      ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val = (vE (gm.s χ) (𝟙 _) ν.J).fst :=
    (GlobalTheory.ZH.CrdCalc.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (𝟙 _) _ h).2 _
  rw [Category.comp_id] at e1
  have e2 := GlobalTheory.ZH.ThetaData.valR_eq_gs (redE ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)).val
  have e3 := gs_unit (redE ℂ) (IsLocalRing.closedPoint ℂ) _ hm
    ((gm.s χ).s fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k))
  have e4 := val_of (gm.s χ) (redE ℂ) (IsLocalRing.closedPoint ℂ) ν.J
    (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ DegPre.gtφT D (TE R ℂ) gm.b χ k)) (fun k => by rw [Category.id_comp])
  have v1 := val_pull hJ (gm.s χ) (redE ℂ) (𝟙 _)
  rw [Category.id_comp] at v1
  have v2 := (val_corr hJ (hp.2 χ) (𝟙 _)).symm.trans ((val_corr hJ (hz.2 χ) (𝟙 _)).trans (val_one _))
  rw [v1] at v2
  refine e1.symm.trans (e2.trans ?_)
  rw [e3, ← e4, v2, Units.val_one, map_one]

end GlobalTheory.MBLow.Cl
