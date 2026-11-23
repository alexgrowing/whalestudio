import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapEqZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapMemSkewTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapSurjectiveSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSkewTraceEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGoodAtUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGoodFormAtPrimeStatement

noncomputable section

open Matrix

namespace GlobalTheory.SUCong

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem relIndex_congSU (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q k : ℕ)
    (hR : GoodRing S σ ϖ q) (hF : GoodForm S σ H) (hk : 1 ≤ k) :
    (congSU S σ H ϖ (k + 1)).relIndex (congSU S σ H ϖ k) = q ^ (Fintype.card n ^ 2 - 1) := by
  let f : congSU S σ H ϖ k →* Multiplicative (Matrix n n (Res S ϖ)) :=
    { toFun := fun g => Multiplicative.ofAdd (levMap S ϖ k ((g : GL n A) : Matrix n n A))
      map_one' := by
        have := (GlobalTheory.T.level_map_eq_zero_iff S σ H ϖ q k hR 1 (one_mem _)).2 (one_mem _)
        simpa using this
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul]
        rw [GlobalTheory.T.level_map_additive S σ H ϖ q k hR hk g h g.2 h.2]
        rfl }
  have hker : f.ker = (congSU S σ H ϖ (k + 1)).subgroupOf (congSU S σ H ϖ k) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact GlobalTheory.T.level_map_eq_zero_iff S σ H ϖ q k hR g g.2
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [← GlobalTheory.T.card_skew_trace_eq S σ H ϖ q hR hF]
  refine Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, ?_⟩
      invFun := fun Y => ⟨Multiplicative.ofAdd Y.1, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun Y => rfl }
  · obtain ⟨g, hg⟩ := x.2
    rw [← hg]
    exact GlobalTheory.T.level_map_mem_skew_trace S σ H ϖ q k hR hF hk g g.2
  · obtain ⟨g, hg, hgY⟩ := GlobalTheory.T.level_map_surjective_skew S σ H ϖ q k hR hF hk Y.1 Y.2
    exact ⟨⟨g, hg⟩, by simp [f, hgY]⟩

end GlobalTheory.SUCong

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamCnt

theorem relIndex_locCong : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (k : ℕ), 1 ≤ k → (GlobalTheory.TamCnt.locCong (IsCMField.complexConj E).toAlgHom Gᵀ Λ v (k + 1)).relIndex (GlobalTheory.TamCnt.locCong (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k) = Ideal.absNorm v.asIdeal ^ (r ^ 2 - 1) := by
  intro E _ _ _ r G Λ hr hU hSD v k hk
  have hlt : v.asIdeal ^ 2 < v.asIdeal := by
    simpa using Ideal.pow_right_strictAnti v.asIdeal v.ne_bot v.isPrime.ne_top (show 1 < 2 by norm_num)
  obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt hlt
  obtain ⟨P, hF, hEq⟩ := GlobalTheory.T.exists_local_good_form_at_prime E r G Λ hr hU hSD v π hπ hπ2
  have hR := GlobalTheory.T.local_ring_good_at_uniformizer E hU v π hπ hπ2
  rw [hEq (k + 1), hEq k, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj P).injective]
  have := GlobalTheory.SUCong.relIndex_congSU _ _ _ _ _ k hR hF hk
  simpa using this

end GlobalTheory.TamCnt
