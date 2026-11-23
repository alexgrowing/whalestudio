import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

theorem GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain : ∀ {D : D7} {V : HSp D} (m : MeasureTheory.Measure (GA D V)) (fd : Set (GA D V)) (g : GA D V), m.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GQ V) fd m → (m.map (fun x => x * g⁻¹)).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ V) ((fun x => x * g) ⁻¹' fd) (m.map (fun x => x * g⁻¹)) := by
  intro D V m fd g hm hfd
  have hmeas : Measurable (fun x : GA D V => x * g⁻¹) := measurable_mul_const g⁻¹
  refine ⟨?_, ?_⟩
  · have h := Measure.isHaarMeasure_map_mul_right m g⁻¹
    exact h
  · refine hfd.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · refine ⟨measurable_mul_const g, ?_⟩
      rw [Measure.map_map (measurable_mul_const g) hmeas]
      have : ((fun x : GA D V => x * g) ∘ fun x => x * g⁻¹) = id := by
        funext x; simp
      rw [this, Measure.map_id]
    · intro h x
      show (h • x) * g = h • (x * g)
      simp [Submonoid.smul_def, Subgroup.smul_def, mul_assoc]
