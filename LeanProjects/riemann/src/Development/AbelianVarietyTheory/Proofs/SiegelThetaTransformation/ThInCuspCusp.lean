import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExpansionOfRowHighest
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadingEqThP
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleMemSec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem thInCusp_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ThInCusp Xo c nab (Formalism.L2.PjFree.cusp Xo c U) := by
  intro hC E _ _ _ H Dw l Xo c r U hr hU _ nab hnab
  unfold Formalism.L2.Pj.ThInCusp
  intro a n hDom hLast f hf
  have hsec : f ∈ Formalism.L2.Pj.sec Xo c a n :=
    GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hnab a n f hf
  obtain ⟨xs, P, hP, hfP⟩ := hf
  rw [Formalism.L2.PjFree.mem_cusp]
  refine ⟨hsec, fun σ hσ => ?_⟩
  have hUσ := hU σ hσ
  obtain ⟨W⟩ := GlobalTheory.Dict.nonempty_uw hUσ
  have hU' := hUσ
  unfold Formalism.L2.PjFree.IsUnf at hU'
  obtain ⟨hrpq, hcomp, -, -, hsecU, -⟩ := hU'
  apply Formalism.L2.PjFree.holCusp_mem_holSub
  intro k
  obtain ⟨hp0, hΨ⟩ := hcomp k
  have hself := (GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r (U σ) hσ hUσ hr W k).2.1
  obtain ⟨Dc, hDce, hrow⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hrpq hp0 hΨ hself hDom
  obtain ⟨-, φ, hφ, hread⟩ := GlobalTheory.Dict.ThRead.reading_eq_thP hC E H Dw l Xo c σ r (U σ) hσ hUσ hr nab hnab n W k a hDom Dc hDce xs P hP f hfP
  have hHH : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (Formalism.L2.Pj.InPsi H) (fun τ i => a (τ, i)) := by
    unfold Formalism.L2.Pj.harmA HaO at hP
    exact hP.1
  have hev : Even n := by
    unfold Dom at hDom
    exact hDom.2
  have hsecQ := hsecU a n hDom f hsec k
  have hw : wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n = Formalism.L2.PjFree.laU (U σ) a n k := by
    rw [Dc.wt_eq]
    rfl
  rw [← hw]
  refine GlobalTheory.Dict.CuspAny.mem_SS_of_eq_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev Dc.k Dc.k' ?_ φ hφ _ (Dc.mem P hHH) _ hread ?_
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | hpos
    · exact Or.inr h0
    · exact Or.inl (hrow hLast hpos)
  · intro ga hga x hx
    rw [hw]
    exact hsecQ.2.2 ga hga x hx

end GlobalTheory.Dict
