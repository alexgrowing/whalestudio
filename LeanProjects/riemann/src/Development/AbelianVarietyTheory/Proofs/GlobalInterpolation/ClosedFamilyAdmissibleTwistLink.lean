import Mathlib
import Formalism.LocalToGlobal.GroupLattices.ServiceOfTiedSelection
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.GlobalSchurBounds.PlugDgt
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Top.closed_family_admissible_twist_link : ∀ (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (aPt0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u)
    (aPtTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw)
    (aPer0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i))
    (aPerTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw)
    (aP10 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u)
    (aAtG : Closed (D3 3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1)
    (hServ : Formalism.L2.G.ServT.ServT (D3 3 𝒜) fun Fm hc => sel Fm (d3_a hc)), Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i) := by
  intro 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hDG : Closed (D3 3 𝒜) fun Fm _ => DGamSize Fm := Closed.of_class fun _ _ hc => hc.2.2.2
  have hA2 : Formalism.L2.G.Adm2InU.Adm2InU (D3 3 𝒜) :=
    { pt0 := aPt0, ptTw := aPtTw, per0 := aPer0, perTw := aPerTw,
      serv := Formalism.L2.G.ServT.servF_of_servT (fun Fm hc => sel Fm (d3_a hc)) hDG hServ,
      p10 := aP10, dgt := Formalism.MainNotions.closed_eventually_levelPrimeCoprimeStabiliser (WithChN 𝒜) 3, atG := aAtG }
  exact (Formalism.L2.G.Adm2InU.admissible_family_of_inclusion hA2).imp fun _ _ _ a => a.1

end
