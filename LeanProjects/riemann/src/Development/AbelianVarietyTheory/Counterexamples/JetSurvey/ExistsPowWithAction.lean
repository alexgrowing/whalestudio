import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxRosati
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesDvrAdmissibleXIdeal

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowActProbe

theorem exists_pow (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (n : ℕ) :
    ∃ D' : DegData R I, Nonempty (IsPowDeg D'.toPre D.toPre n) :=
  GlobalTheory.PowDegData.main GlobalTheory.globalFns_holds R I D n

section Unique

variable {R : Type} [CommRing R] [IsDomain R] {D' D : DegPre R} {n : ℕ}

theorem isMonHom_of_coord (pD : IsPowDeg D' D n) (f : D.P.A ⟶ D.P.A) [IsMonHom f] (f' : D'.P.A ⟶ D'.P.A)
    (h : ∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) : IsMonHom f' := by
  have : f' = powMap pD.pw f := pow_ext pD.pw fun i => (h i).trans (powMap_pr _ _ i).symm
  rw [this]; exact powMap_isMonHom _ _

end Unique

theorem powOActSt_iff : PowOActSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
      [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
      (n : ℕ) (D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre P.D.toPre n),
      ∃ (M : Module (𝓞 E) D'.toPre.X) (oD' : @DegPre.OAct V _ _ (𝓞 E) _ H.starRing D'.toPre M),
        (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n),
          pD.xe (M.toDistribMulAction.toMulAction.toSMul.smul a x) i =
            P.mod.toDistribMulAction.toMulAction.toSMul.smul a (pD.xe x i)) ∧
        ∀ (a : 𝓞 E) (i : Fin n), (letI := H.starRing; oD'.onB.act a) ≫ pD.pw.pr i =
          pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a) := Iff.rfl

theorem premises_met (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Δ : Datum H)
    (h : 1 ≤ Δ.p + Δ.q) (n : ℕ) :
    ∃ (t : SAB H (Sp (PowerSeries ℂ))) (P : PELUnif (maximalIdeal (PowerSeries ℂ)) t), 0 < P.A.g ∧
      ∃ D' : DegData (PowerSeries ℂ) (maximalIdeal _), Nonempty (IsPowDeg D'.toPre P.D.toPre n) := by
  obtain ⟨t, P, -, -, hg, -⟩ := GlobalTheory.ConstantFamily.exists_pelUnif_powerSeries E H Δ h
  exact ⟨t, P, hg, exists_pow _ _ P.D n⟩

end GlobalTheory.PowActProbe
