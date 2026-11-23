import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithfulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegersStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalSubgroupNotMovesUniformBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitOfCoprimeOrderStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootFixedSubfieldOfAlmostEtaleStatement
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  intro L _ v p hp hp0 hp1 G _ _ _ _ hinv ζ hζ hζfix hroot σ hσ
  obtain ⟨N, hNn, hNmem, i, hi, hNi⟩ := GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound L v G hinv
  by_contra hmov
  have hσN : σ ∈ N := (hNmem σ).2 hmov
  have hfixN : ∀ τ ∈ N, ∀ x ∈ Fix L N, τ • x = x := fun τ hτ x hx => hx ⟨τ, hτ⟩
  have hdesc : ∀ τ : G, τ ∉ N → Moves v (Fix L N) τ := fun τ hτ =>
    GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield L v G hinv N i hi hNi τ (by_contra fun h => hτ ((hNmem τ).2 h))
  have hsep : AlmostSep v N := GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hinv N hNn inferInstance hdesc
  have hF : ApproxRoot p v (Fix L N) := GlobalTheory.T.approxPthRoot_fixedSubfield_of_almostEtale L v p hp hp0 hp1 G hinv N inferInstance hsep hroot
  have hpg : IsPGroup p N := by
    intro τ
    set n := orderOf (τ : G) with hn
    have hn0 : n ≠ 0 := (orderOf_pos (τ : G)).ne'
    set k := n.factorization p
    refine ⟨k, ?_⟩
    have hcop : Nat.Coprime (n / p ^ k) p := (Nat.coprime_ordCompl hp hn0).symm
    have hτ' : ((τ : G) ^ (p ^ k)) ∈ N := N.pow_mem τ.2 _
    by_contra hne
    have hne' : (τ : G) ^ (p ^ k) ≠ 1 := by
      intro h; apply hne; ext; simpa using h
    have hl : ((τ : G) ^ (p ^ k)) ^ (n / p ^ k) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd n p), hn, pow_orderOf_eq_one]
    obtain ⟨y, hy⟩ : ∃ y : L, ((τ : G) ^ (p ^ k)) • y ≠ y := by
      by_contra h
      push_neg at h
      exact hne' (eq_of_smul_eq_smul (α := L) (fun y => by rw [h y, one_smul]))
    exact (hNmem _).1 hτ' (GlobalTheory.T.movesIntegersAlmostUnit_of_coprime_order L v p hp (Fix L N) hF hp0 hp1 G hinv _ (hfixN _ hτ') _ hcop hl ⟨y, hy⟩)
  haveI : Nontrivial N := ⟨⟨⟨σ, hσN⟩, 1, fun h => hσ (congrArg Subtype.val h)⟩⟩
  haveI : FaithfulSMul N L := ⟨fun {a b} h => Subtype.ext (eq_of_smul_eq_smul (α := L) h)⟩
  obtain ⟨σ₀, α, hα0, hσα, hαp⟩ := GlobalTheory.T.exists_lagrange_resolvent_of_pGroup_faithful L p hp N hpg ζ hζ (fun g => hζfix g)
  have hαF : α ^ p ∈ Fix L N := fun g => hαp g
  exact (hNmem _).1 σ₀.2 (GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit L v p hp (Fix L N) hF hp0 hp1 G (σ₀ : G) (hfixN _ σ₀.2) ζ α hζ hα0 hαF hσα)

end GlobalTheory.AlmostEt
