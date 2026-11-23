import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedgeStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierProjectionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTopStatement

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_eq_extD_imp_eq_zero :
    ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ)
      (γ : abelian₂ K →+* abelian₂ K), IsCoord x → IsCartierMap p x γ → ∀ ζ ξ : abelian₂ K, γ ζ = extD K ξ → ζ = 0 := by
  intro K _ p _ _ n x γ hx hγ ζ ξ hζ
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hx
  have hmem : ζ ∈ Submodule.span K (Set.range (logWedge x)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  obtain ⟨-, Q, π, -, hQ, -, hπ, hQd, -⟩ := GlobalTheory.T.cartier_projection_properties K p n x hx
  have hγs : γ (∑ I, c I • logWedge x I) = ∑ I, (c I ^ p) • logWedge x I := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ (c I) I
  have hfix : Q (γ (∑ I, c I • logWedge x I)) = γ (∑ I, c I • logWedge x I) := by
    rw [hγs, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQ, hπ]
  have h0 : ∑ I, (c I ^ p) • logWedge x I = 0 := by
    rw [← hγs, ← hfix, hζ, hQd]
  have hc : ∀ I, c I ^ p = 0 := fun I =>
    (Fintype.linearIndependent_iff.1 hli) (fun I => c I ^ p) h0 I
  have hc' : ∀ I, c I = 0 := fun I =>
    (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 (hc I)
  simp [hc']

end GlobalTheory
