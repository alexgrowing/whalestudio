import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometryStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.LowDat.exists_lower : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
  GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R, 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La)
    (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    GlobalTheory.LowDat.IsLower Dw D' Z f ∧ D'.p = Dw.p - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    D'.q = Dw.q - Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : GlobalTheory.LowDat.LowTate C D' o' F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I ∧
          GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C hr
  obtain ⟨Z, hZ, hrk, tK, m1, m2, hI⟩ := GlobalTheory.T.exists_isotropic_saturated_weight_filtration Xo c R hR C hr
  obtain ⟨D', f, hf, hp, hq⟩ := GlobalTheory.T.exists_lower_datum_of_isotropic_saturated Dw Z hZ
  obtain ⟨o', φB, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry Xo c R hR C Z D' f hZ hf hrk hp hq tK m1 m2 hI
  refine ⟨Z, D', f, o', φB, hZ, hrk, hf, hrk ▸ hp, hrk ▸ hq, h1, h2, h3, tK, m1, m2, ?_⟩
  intro F _ _ _
  obtain ⟨I, hI1, hI2⟩ := hI F
  obtain ⟨I', hI'⟩ := h4 F I hI1 hI2
  exact ⟨I, I', hI1, hI2, hI'⟩
