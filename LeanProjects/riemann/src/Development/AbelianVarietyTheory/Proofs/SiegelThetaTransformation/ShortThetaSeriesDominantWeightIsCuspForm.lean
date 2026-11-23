import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NotIsIsoOfDefinite
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HalfIntegralGeneratorAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem shortInCusp_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ShortInCusp Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) a n d := by
  intro hci E _ _ _ H Dw l Xo c n d r U hr1 hU hlev hnab hunit hpin nab bad nV a hD hL f hf
  obtain ⟨hsec, Λ, N, x0, P, hun, -, htr, hN, hx0, hP, hrule⟩ := hf
  refine (mem_cusp Xo c U a n f).2 ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  have hsd := (GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k).2.1
  obtain ⟨Dc, hDe, hk⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  obtain ⟨φ, hφ, hrd⟩ := GlobalTheory.Dict.ShortRead.rdU_eq_thP hci E H Dw l Xo c n d σ r (U σ) hσ hu hr1 hlev hnab hunit hpin W k a hD
    Dc hDe Λ N _ x0 P hun htr hN hx0 hP.1 f hsec hrule
  have hrn : r ≤ n := hu.1 ▸ (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).1 _ x0 hx0
  have hw : laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  rw [hw] at hs ⊢
  refine CuspClass.mem_SS_of_eq_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hD.2 Dc.k Dc.k'
    ?_ hrn φ hφ _ (Dc.mem P hP.1) _ hrd ?_
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · exact hs.2.2

end GlobalTheory.Dict
