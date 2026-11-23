import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratorsIffOfChartIndep
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc

theorem qk_lattice_oAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt P.D.toPre K m) (x x' : TFK (R := V) K ⟶ P.A.A), 1 ≤ m → QkToAkU P.U.toUnifPre K m pk x → QkToAkU P.U.toUnifPre K m pk' x' → x' = x ≫ P.oA.act a → CongMod m pk'.y (a • pk.y) := by
  intro E _ _ _ H V _ _ _ hV t P K _ _ _ m a pk pk' x x' hm hx hx' hxx'
  obtain ⟨h1, h2, h3⟩ := hV
  have hT : P.TorsionIso := GlobalTheory.GeneratorsCompare.torsionIso P
  obtain ⟨f, hf, -, heq, -, hact, -⟩ := hT K m hm
  letI := H.starRing
  obtain ⟨p'', hp''⟩ := qkAct_exists GlobalTheory.lawsAndExpansions.1.1.globalFns P.D.tau_bimult P.oD a pk
  have e1 : f p'' = x' := by
    rw [hact a pk p'' hp'', ← (hf pk x).1 hx, hxx']
  have e2 : f p'' = f pk' := by rw [e1, ← (hf pk' x').1 hx']
  obtain ⟨z₂, hz₂, -⟩ := (heq p'' pk').1 e2
  obtain ⟨q, hq, -, z₁, hz₁, -⟩ := hp''
  exact ⟨z₁ + z₂, by rw [hz₂, hz₁, hq, smul_add, add_assoc]⟩

end GlobalTheory.UPoinc
