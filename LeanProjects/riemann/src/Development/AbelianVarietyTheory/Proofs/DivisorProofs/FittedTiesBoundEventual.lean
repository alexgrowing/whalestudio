import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigTop.Fun

theorem gBig_atTied : ∀ Q : GlobalTheory.SqTop.GP, SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.SqTop.GBig @Q → Lf (@Fitted @Comparison₂) fun p _ d C _ => Q d.G p.P.A3.A.μ0 C p.Z.x p.Z.b := by
  intro Q hS hD hG
  obtain ⟨CF0, hG⟩ := hG
  refine ⟨CF0, fun CF hCF => (hS.and hD).imp fun {eps} Fm CH he h => ?_⟩
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩ := h
  intro _
  obtain ⟨C0, x₀, hC⟩ := hG eps CF hCF
  refine ⟨C0, fun C hC0 => ⟨max x₀ (max x1 x2), fun x hx hle i p hp d hd => ?_⟩⟩
  obtain ⟨_, a, ht⟩ := hd
  have hset := h1 x hx (le_of_max_le_left (le_of_max_le_right hle)) i p hp ht.ok.eser
  have hdl := h2 x hx (le_of_max_le_right (le_of_max_le_right hle)) i p hp
  have hx0 : x₀ ≤ (Fm.L x i).sc.x := (le_of_max_le_left hle).trans (Fm.L_x x i hx).ge
  exact hC C hC0 _ (Fm.L x i) (Fm.L_eps x i) hx0 ⟨hset.size, hset.host, hset.hF, hdl⟩ _ p.R.toLevCh p.P.A3.A.μ0
    hset.core.lev d.G

end GlobalTheory.BigTop.Fun

end
