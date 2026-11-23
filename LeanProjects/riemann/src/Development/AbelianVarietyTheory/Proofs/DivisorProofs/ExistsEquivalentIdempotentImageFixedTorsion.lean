import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndUOfOLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EFix

theorem exists_equiv_act_of_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  intro R _ _ _ hR n hn _ Q D' F A' G' _ _ U' oA oG hS hl a _ hae p hp
  have hAdm : AdmBase R (maximalIdeal R) := ⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩
  haveI : CharZero R := hR.2.2.2
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨q, hqy, hqg⟩ := exists_gtPtAct (F := AlgebraicClosure (FractionRing R)) hL.1.globalFns F.o F.e p
  obtain ⟨E, eG, eA, -, -, eact⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl F.e
  obtain ⟨E', eG', -, -, eh', -⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl (star F.e)
  have hcube := GlobalTheory.Mum.EFixCube.cube_adj_of_oLinear R hAdm D' A' G' U'.toUnifPre hS F.O F.o oA oG hl F.e
  have hfun := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D' A' G' hS U'
  have h2 := (hfun.2 E E' (by rw [eG, eG']; exact hcube)).2 (AlgebraicClosure (FractionRing R))
  have hq := h2.2.2 n hn p q a (by rw [eh', star_star]; exact hqy)
    ((eact (AlgebraicClosure (FractionRing R)) _ _).2 hqg) hp
  rw [eA, hae] at hq
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D' A' G' hS U'
    (AlgebraicClosure (FractionRing R)) n hn
  exact ⟨q, hqy, hqg, (hf.2.2.1 q p).1 (((hf.1 q a).1 hq).symm.trans ((hf.1 p a).1 hp))⟩

end GlobalTheory.Mum.EFix
